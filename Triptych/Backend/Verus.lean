/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Triptych.Architecture.Classify
import Triptych.Architecture.Unambiguity
import Triptych.Backend.Verus.Translation
import Triptych.Backend.Verus.Lowering
import Triptych.Backend.Verus.Preservation
import Triptych.Backend.Verus.PrettyPrint
import Triptych.Architecture.ParsePlan
import Triptych.Architecture.SearchMachine
import Triptych.Backend.Verus.RuntimeModel
import Triptych.Backend.Verus.SemanticPlan

/-!
# Verus backend

The Verus generation pipeline has four stages:

1. the Triptych elaborator supplies the already-parsed grammar, value expression, phased
   constraints, and conversion names in `Verus.FormatInput`;
2. this module validates that input and translates the readable specification to `Verus.IR`;
3. `Triptych.Backend.Verus.Lowering` lowers the IR to `Verus.Ast`;
4. `Triptych.Backend.Verus.PrettyPrint` emits Verus source from that AST.

`Verus.FormatInput` is only a convenience record at the elaborator/backend boundary. It is not
another intermediate language: its grammar, value, and constraint fields are the same Triptych
values used by Lean generation.

Value and constraint translation is checked against the Triptych denotation in
`Triptych.Backend.Verus.Translation`. Concrete value and arithmetic-constraint expressions are
checked after lowering in `Triptych.Backend.Verus.Preservation`, while generated helper bodies are
checked in `Triptych.Backend.Verus.AstSemantics`. The target pretty-printer remains a separate
trusted boundary.

Executable emission is fail-closed. The public backend entry point returns `spec.rs` and a
proof-carrying `parser.rs` as one `CertifiedRustOutput`; it never exposes an uncertified parser
fallback. Eligible deterministic grammars compile through the shared `ScanPlan`, whose verified
lowering produces `CursorProgram`, and then to direct single-cursor code with compositional
grammar-witness proofs. Acyclic branching grammars lower through `SearchPlan`, `SearchProgram`,
and `SearchMachine` to direct proof-carrying state functions. Finite separated repetitions are
unrolled while preserving source-order stopping and repetition-count captures. Direct search-state
capture frames reserve two disjoint stable output slots, so capture closure and rollback use verified
in-place updates without mid-vector insertion, removal, whole-state branch allocation, or a
clone-based fallback. Emission is fail-closed: if specialized lowering or rendering cannot cover
a grammar shape, generation reports that shape instead of substituting a generic runtime parser.
A generated `contract.rs` states the obligations implemented by an optional optimized external
parser.
-/

namespace Triptych.Backend.Verus

open IR

/-- The already-elaborated Triptych data required to generate one Verus specification. -/
structure FormatInput where
  name : String
  grammar : Grammar
  valueExpr : ValExpr
  wfConstraints : List Constraint := []
  valueConstraints : List Constraint := []
  ofSpec : String := "id"
  toSpec : String := "id"
  hasPrinter : Bool := false
  deriving Repr, Inhabited, DecidableEq

private structure FieldSpec where
  capture : String
  ident : String
  deriving Repr, Inhabited, DecidableEq

private def isIdentChar (character : Char) : Bool :=
  character.isAlpha || character.isDigit || character == '_'

private def sanitizeIdent (source : String) : String :=
  let cleaned := String.ofList (source.toList.map fun character =>
    if isIdentChar character then character else '_')
  let cleaned := if cleaned.isEmpty then "field" else cleaned
  match cleaned.toList.head? with
  | some character => if character.isDigit then "field_" ++ cleaned else cleaned
  | none => "field"

private partial def snakeChars (previousWasWordEnd : Bool) : List Char → List Char
  | [] => []
  | character :: rest =>
      let uppercase := character.isUpper
      let separator := if uppercase && previousWasWordEnd then ['_'] else []
      let rendered := if isIdentChar character then character.toLower else '_'
      let wordEnd := character.isLower || character.isDigit
      separator ++ [rendered] ++ snakeChars wordEnd rest

private def snakeCase (source : String) : String :=
  sanitizeIdent (String.ofList (snakeChars false source.toList))

private def typeName (source : String) : String :=
  sanitizeIdent source

private def fieldIdent (fields : List FieldSpec) (capture : String) : String :=
  match fields.find? (·.capture == capture) with
  | some field => field.ident
  | none => snakeCase (Triptych.surfaceBinder capture)

private def functionName (formatName suffix : String) : String :=
  snakeCase formatName ++ "_" ++ suffix

private def productionName (formatName production : String) : String :=
  functionName formatName "is_wf" ++ "_" ++ sanitizeIdent production

private def productionViewName (formatName production : String) : String :=
  functionName formatName "matches" ++ "_" ++ sanitizeIdent production

private def directRefs (sequence : Triptych.Seq) : List String :=
  sequence.filterMap fun item =>
    match item.sym with
    | .ref name => some name
    | _ => none

private def requiredDirectRefs (sequence : Triptych.Seq) : List String :=
  sequence.filterMap fun item =>
    match item.sym with
    | .ref name => if item.optional then none else some name
    | _ => none

private def rootCaptures (grammar : Grammar) : List String :=
  match grammar.startProd? with
  | none => []
  | some production => (production.alts.flatMap directRefs).eraseDups

private def requiredInEveryRootAlternative (grammar : Grammar) (capture : String) : Bool :=
  match grammar.startProd? with
  | none => false
  | some production =>
      production.alts.all fun alternative =>
        (requiredDirectRefs alternative).contains capture

private partial def stringEqualityCaptures : Constraint → List String
  | .strEq capture _ => [capture]
  | .and left right => (stringEqualityCaptures left ++ stringEqualityCaptures right).eraseDups
  | _ => []

private def constraintStringEqualityCaptures : List Constraint → List String
  | [] => []
  | constraint :: rest =>
      stringEqualityCaptures constraint ++ constraintStringEqualityCaptures rest

private def productionQualifier (grammar : Grammar) (production : Production) : String :=
  if production.name == grammar.start then "" else production.name

private def captureKeys (qual name : String) : List String :=
  if qual.isEmpty then [name] else [name, qual ++ "." ++ name]

private def referencesInSymbolAux (grammar : Grammar) : Nat → String → Sym → List String
  | 0, _, _ => []
  | fuel + 1, qual, .ref name =>
      let descendants := match grammar.prod? name with
        | some production =>
            (production.alts.map fun alternative =>
              (alternative.map fun item =>
                referencesInSymbolAux grammar fuel name item.sym).flatten).flatten
        | none => []
      captureKeys qual name ++ descendants
  | fuel + 1, qual, .rep _ item _ _ => referencesInSymbolAux grammar fuel qual item
  | _ + 1, _, _ => []

private def referencesInSymbol (grammar : Grammar) (qual : String) (symbol : Sym) : List String :=
  referencesInSymbolAux grammar (grammar.prods.length + 1) qual symbol

private def semanticCaptures (format : FormatInput) : List String :=
  (format.valueExpr.captures ++
    (format.wfConstraints ++ format.valueConstraints).flatMap Constraint.captures).eraseDups

private def fieldsFor (format : FormatInput) : List FieldSpec :=
  (rootCaptures format.grammar ++ semanticCaptures format).eraseDups.map fun capture =>
    { capture, ident := snakeCase (Triptych.surfaceBinder capture) }

mutual

  private partial def captureKeysInSymbol (grammar : Grammar) (qual : String) (fuel : Nat) :
      Sym → List String
    | .ref name =>
        let own := if qual.isEmpty then [name] else [name, qual ++ "." ++ name]
        if fuel == 0 then
          own
        else
          match grammar.prod? name with
          | none => own
          | some production =>
              (own ++ production.alts.flatMap
                (captureKeysInSequence grammar name (fuel - 1))).eraseDups
    | .rep _ item _ _ =>
        let base := item.refName?.getD qual
        ((base ++ "#count") :: captureKeysInSymbol grammar qual fuel item).eraseDups
    | _ => []

  private partial def captureKeysInSequence (grammar : Grammar) (qual : String) (fuel : Nat)
      (sequence : Triptych.Seq) : List String :=
    (sequence.flatMap fun item => captureKeysInSymbol grammar qual fuel item.sym).eraseDups

end

private def grammarCaptureKeys (grammar : Grammar) : List String :=
  match grammar.startProd? with
  | none => []
  | some production =>
      (production.alts.flatMap
        (captureKeysInSequence grammar "" grammar.prods.length)).eraseDups

private def allSymbols (grammar : Grammar) : List Sym :=
  grammar.prods.flatMap fun production =>
    production.alts.flatMap fun sequence => sequence.map (·.sym)

private partial def repetitionsIn : Sym → List Sym
  | repetition@(.rep _ item _ _) => repetitionsIn item ++ [repetition]
  | _ => []

private partial def containsStringSymbol : Sym → Bool
  | .str => true
  | .rep _ item _ _ => containsStringSymbol item
  | _ => false

private def repetitionsFor (grammar : Grammar) : List Sym :=
  ((allSymbols grammar).flatMap repetitionsIn).eraseDups

private def duplicate? [BEq α] (values : List α) : Bool :=
  values.eraseDups.length != values.length

private def validateCaptureShape (grammar : Grammar) : Except String Unit := do
  let start ← match grammar.startProd? with
    | some production => pure production
    | none => throw s!"Verus backend: start production `{grammar.start}` is missing"
  for alternative in start.alts do
    let captures := directRefs alternative
    if duplicate? captures then
      throw "Verus backend: each root alternative may capture a production at most once"

def validateReadableSpecInput (format : FormatInput) : Except String Unit := do
  let names := format.grammar.prods.map (·.name)
  if duplicate? names then
    throw "Verus backend: production names must be unique"
  if !format.grammar.refsResolve then
    throw "Verus backend: every nonterminal reference must resolve"
  if let some cycle := format.grammar.cycle? then
    throw s!"Verus backend: recursive grammars are unsupported: \
      {String.intercalate " -> " cycle}"
  if !format.grammar.repOk then
    throw "Verus backend: separated repetition requires a nonempty separator and lower bound 1"
  validateCaptureShape format.grammar
  let available := grammarCaptureKeys format.grammar
  let required := semanticCaptures format
  for capture in required do
    if !available.contains capture then
      throw s!"Verus backend: capture `{capture}` is not produced by the grammar"
  let equalityCaptures :=
    constraintStringEqualityCaptures (format.wfConstraints ++ format.valueConstraints)
  for capture in equalityCaptures.eraseDups do
    if !requiredInEveryRootAlternative format.grammar capture then
      throw s!"Verus backend: string equality on `{capture}` requires that capture to be a \
        non-optional direct reference in every root alternative"

/-! ## Generic proof-carrying Rust parser -/

/-- Canonical direct scanner. Verus proves its source-grammar semantics once; generated format
    modules only serialize their grammar tables and call its checked entry point. -/
-- Keep generated runtime scanners sourced from the shared proof-carrying template.
-- Keep runtime representation changes synchronized with the generated parser source.
private def runtimeParserTemplate : String :=
  include_str "Verus/RuntimeParser.rs.in"

-- Shared copyable checked values and verified source-span readers for semantic stages.
-- Recompile this module after changing any embedded runtime template.
private def runtimeSemanticTemplate : String :=
  include_str "Verus/RuntimeSemantic.rs.in"

private def runtimeSemanticUnsignedTemplate : String :=
  let signedMarker :=
    "/// Exact signed arithmetic with an optional executable `i128` representation."
  let commonMarker :=
    "/// Runtime predicates shared by signed and unsigned semantic plans."
  let commonPrefix := (runtimeSemanticTemplate.splitOn signedMarker).headD ""
  let suffix := ((runtimeSemanticTemplate.splitOn commonMarker).drop 1).headD ""
  commonPrefix ++ commonMarker ++ suffix

-- Includes exact, fixed-bound, and primitive fast paths for decimal source-span decoding.
private def runtimeSemanticNatTemplate : String :=
  include_str "Verus/RuntimeSemanticNat.rs.in"

-- Semantic readers retain character-level contracts while specializing ASCII execution paths.
private def runtimeSemanticSignTemplate : String :=
  include_str "Verus/RuntimeSemanticSign.rs.in"

private def runtimeSemanticHexSequenceTemplate : String :=
  -- Includes the single-pass hex scanner and its certified separated-group accumulator lemmas.
  include_str "Verus/RuntimeSemanticHexSequence.rs.in"

private def runtimeSemanticSegmentsTemplate : String :=
  include_str "Verus/RuntimeSemanticSegments.rs.in"

-- Runtime arithmetic retains exact ghost values through proof-linked iterative machine operations.
private def runtimeSemanticPowTemplate : String :=
  include_str "Verus/RuntimeSemanticPow.rs.in"

private def runtimeSemanticNaturalCacheTemplate : String :=
  include_str "Verus/RuntimeSemanticNaturalCache.rs.in"

private def runtimeSemanticHexSequenceCacheTemplate : String :=
  include_str "Verus/RuntimeSemanticHexSequenceCache.rs.in"

private def renderTokenClass : TokClass → String
  | .digit => "TokenClass::Digit"
  | .hexDigit => "TokenClass::HexDigit"
  | .bit => "TokenClass::Bit"
  | .asciiRange lower upper =>
      "TokenClass::AsciiRange { lower: " ++ toString lower ++
        ", upper: " ++ toString upper ++ " }"

private def renderLengthSpec : LenSpec → String
  | .exactly width => s!"LengthSpec::Exactly({width})"
  | .between lower upper =>
      "LengthSpec::Between { lower: " ++ toString lower ++
        ", upper: " ++ toString upper ++ " }"
  | .atLeastOne => "LengthSpec::AtLeastOne"

private def renderNatOption : Option Nat → String
  | .none => "None"
  | .some n => s!"Some({n})"

private def renderGrammarSymbol : RuntimeSymbol → String
  | .literal text => s!"GrammarSymbol::Literal({String.quote text})"
  | .stringLiteral => "GrammarSymbol::StringLiteral"
  | .reference production => s!"GrammarSymbol::Reference({production})"
  | .terminal token length =>
      s!"GrammarSymbol::Terminal({renderTokenClass token}, {renderLengthSpec length})"
  | .repetition separator item lower upper =>
      "GrammarSymbol::Repetition { separator: NonEmptySeparator::new(" ++
        String.quote separator ++ ")" ++
        ", item: " ++ toString item ++
        ", lower: " ++ toString lower ++
        ", upper: " ++ renderNatOption upper ++ " }"

private def renderSeparatorProofs (grammar : FlatGrammar) : String :=
  let separators :=
    grammar.symbols.filterMap (fun
      | .repetition separator _ _ _ => some separator
      | _ => none) |>.eraseDups
  match separators with
  | [] => ""
  | _ =>
      "    proof {\n" ++
        String.intercalate "" (separators.map fun separator =>
          let quoted := String.quote separator
          s!"        reveal_strlit({quoted});\n" ++
            s!"        assert({quoted}@.len() > 0);\n") ++
        "    }\n"

private def renderGrammarItem (item : RuntimeItem) : String :=
  "GrammarItem { symbol: " ++ toString item.symbol ++
    ", optional: " ++ toString item.optional ++ " }"

private def renderGrammarAlternative (alternative : FlatAlternative) : String :=
  "GrammarAlternative { first_item: " ++ toString alternative.firstItem ++
    ", item_count: " ++ toString alternative.itemCount ++ " }"

private def renderGrammarProduction (production : FlatProduction) : String :=
  "GrammarProduction { first_alternative: " ++ toString production.firstAlternative ++
    ", alternative_count: " ++ toString production.alternativeCount ++ " }"

private def renderArray (indent : String) (items : List String) : String :=
  match items with
  | [] => "[]"
  | _ =>
      "[\n" ++ String.intercalate ",\n" (items.map fun item => indent ++ item) ++ "\n    ]"

private def productionTableComment (grammar : FlatGrammar) : String :=
  "// Production table: " ++
    String.intercalate ", " (grammar.productions.zipIdx.map fun (production, index) =>
      s!"{index} = {production.name}")

private def indentText (depth : Nat) (source : String) : String :=
  let indent := String.ofList (List.replicate (depth * 4) ' ')
  String.intercalate "\n" ((source.splitOn "\n").map fun line =>
    if line.isEmpty then line else indent ++ line)

private def renderFiniteIndexCases (collection : String) (items : List String) : String :=
  match items.zipIdx with
  | [] => "assert(false);"
  | (firstItem, firstIndex) :: rest =>
      let branches :=
        (s!"if index == {firstIndex} " ++ "{\n" ++
          s!"    assert(index == {firstIndex});\n" ++
          s!"    assert({collection}@[index] == {firstItem});\n" ++
          "}") ::
        rest.map fun (item, indexValue) =>
          s!"else if index == {indexValue} " ++ "{\n" ++
            s!"    assert(index == {indexValue});\n" ++
            s!"    assert({collection}@[index] == {item});\n" ++
            "}"
      String.intercalate " " branches ++ " else {\n    assert(false);\n}"

private def semanticCharacterLiteral (character : Char) : String :=
  "'\\u{" ++ String.ofList (Nat.toDigits 16 character.toNat) ++ "}'"

private def renderSemanticTextLiteral (text : String) : String :=
  "seq![" ++ String.intercalate ", " (text.toList.map semanticCharacterLiteral) ++ "]"

private def renderSymbolProof : RuntimeSymbol → String
  | .literal _ =>
      "match source_grammar.symbols@[index] {\n" ++
        "    GrammarSymbol::Literal(_) => {},\n" ++
        "    _ => { assert(false); },\n" ++
        "}"
  | .stringLiteral =>
      "match source_grammar.symbols@[index] {\n" ++
        "    GrammarSymbol::StringLiteral => {},\n" ++
        "    _ => { assert(false); },\n" ++
        "}"
  | .reference production =>
      "match source_grammar.symbols@[index] {\n" ++
        "    GrammarSymbol::Reference(found_production) => {\n" ++
        s!"        assert(found_production == {production});\n" ++
        "    },\n" ++
        "    _ => { assert(false); },\n" ++
        "}"
  | .terminal _ _ =>
      "match source_grammar.symbols@[index] {\n" ++
        "    GrammarSymbol::Terminal(_, _) => {},\n" ++
        "    _ => { assert(false); },\n" ++
        "}"
  | .repetition _ item lower _ =>
      "match source_grammar.symbols@[index] {\n" ++
        "    GrammarSymbol::Repetition {\n" ++
        "        item: found_item, lower: found_lower, ..\n" ++
        "    } => {\n" ++
        s!"        assert(found_item == {item});\n" ++
        s!"        assert(found_lower == {lower});\n" ++
        "    },\n" ++
        "    _ => { assert(false); },\n" ++
        "}"

private def renderSymbolIndexCases (symbols : List RuntimeSymbol) : String :=
  match symbols.zipIdx with
  | [] => "assert(false);"
  | (firstSymbol, firstIndex) :: rest =>
      let branch (branchPrefix : String) (symbol : RuntimeSymbol) (indexValue : Nat) :=
        s!"{branchPrefix} index == {indexValue} " ++ "{\n" ++
          s!"    assert(index == {indexValue});\n" ++
          indentText 1 (renderSymbolProof symbol) ++ "\n" ++
          "}"
      let branches :=
        branch "if" firstSymbol firstIndex ::
          rest.map fun (symbol, indexValue) =>
            branch "else if" symbol indexValue
      String.intercalate " " branches ++ " else {\n    assert(false);\n}"

private def renderStaticGrammarProof (grammar : FlatGrammar) : String :=
  let symbolCases := indentText 2 (renderSymbolIndexCases grammar.symbols)
  let itemCases := indentText 2
    (renderFiniteIndexCases "source_grammar.items"
      (grammar.items.map renderGrammarItem))
  let alternativeCases := indentText 2
    (renderFiniteIndexCases "source_grammar.alternatives"
      (grammar.alternatives.map renderGrammarAlternative))
  let productionCases := indentText 2
    (renderFiniteIndexCases "source_grammar.productions"
      (grammar.productions.map renderGrammarProduction))
  "proof {\n" ++
    "    reveal(grammar_well_formed);\n" ++
    "    reveal(grammar_symbol_well_formed);\n" ++
    "    reveal(grammar_alternative_well_formed);\n" ++
    "    reveal(grammar_production_well_formed);\n" ++
    "    assert forall|index: int| 0 <= index < source_grammar.symbols@.len() implies\n" ++
    "        grammar_symbol_well_formed(\n" ++
    "            source_grammar.symbols@[index],\n" ++
    "            index,\n" ++
    "            source_grammar.symbols@.len() as int,\n" ++
    "            source_grammar.productions@.len() as int,\n" ++
    "        ) by {\n" ++
    symbolCases ++ "\n" ++
    "    }\n" ++
    "    assert forall|index: int| 0 <= index < source_grammar.items@.len() implies\n" ++
    "        source_grammar.items@[index].symbol < source_grammar.symbols@.len() by {\n" ++
    itemCases ++ "\n" ++
    "    }\n" ++
    "    assert forall|index: int| 0 <= index < source_grammar.alternatives@.len() implies\n" ++
    "        grammar_alternative_well_formed(\n" ++
    "            source_grammar.alternatives@[index],\n" ++
    "            source_grammar.items@.len() as int,\n" ++
    "        ) by {\n" ++
    alternativeCases ++ "\n" ++
    "    }\n" ++
    "    assert forall|index: int| 0 <= index < source_grammar.productions@.len() implies\n" ++
    "        grammar_production_well_formed(\n" ++
    "            source_grammar.productions@[index],\n" ++
    "            source_grammar.alternatives@.len() as int,\n" ++
    "        ) by {\n" ++
    productionCases ++ "\n" ++
    "    }\n" ++
    "    assert(grammar_well_formed(&source_grammar));\n" ++
  "}"

private def renderCaptureSelector : CaptureSelector → String
  | .production production => s!"CaptureKey::Production({production})"
  | .qualified parent production =>
      "CaptureKey::Qualified { parent: " ++ toString parent ++
        ", production: " ++ toString production ++ " }"
  | .repetition symbol => s!"CaptureKey::Repetition({symbol})"

private def semanticCaptureTextFunction (format : FormatInput) : String :=
  functionName format.name "capture_text"

private def semanticCaptureCountFunction (format : FormatInput) : String :=
  functionName format.name "capture_count"

private def renderSemanticCaptureText (format : FormatInput) (selector : CaptureSelector) : String :=
  semanticCaptureTextFunction format ++
    s!"(input, candidate, {renderCaptureSelector selector})"

private def renderSemanticCaptureCount (format : FormatInput) (selector : CaptureSelector) : String :=
  semanticCaptureCountFunction format ++
    s!"(candidate, {renderCaptureSelector selector})"

private partial def ExecutableExpr.readers : ExecutableExpr → List CaptureReader
  | .literal _ => []
  | .capture _ _ reader _ => [reader]
  | .add left right | .sub left right | .mul left right | .tdiv left right
  | .mod left right | .pow left right =>
      (left.readers ++ right.readers).eraseDups
  | .neg expression => expression.readers
  | .iteEq left right thenBranch elseBranch
  | .iteLt left right thenBranch elseBranch
  | .iteLe left right thenBranch elseBranch =>
      (left.readers ++ right.readers ++ thenBranch.readers ++ elseBranch.readers).eraseDups
  | .iteEmpty _ thenBranch elseBranch =>
      (thenBranch.readers ++ elseBranch.readers).eraseDups

private partial def ExecutableExpr.captureReaders :
    ExecutableExpr → List (CaptureSelector × CaptureReader)
  | .literal _ => []
  | .capture _ selector reader _ => [(selector, reader)]
  | .add left right | .sub left right | .mul left right | .tdiv left right
  | .mod left right | .pow left right =>
      (left.captureReaders ++ right.captureReaders).eraseDups
  | .neg expression => expression.captureReaders
  | .iteEq left right thenBranch elseBranch
  | .iteLt left right thenBranch elseBranch
  | .iteLe left right thenBranch elseBranch =>
      (left.captureReaders ++ right.captureReaders ++ thenBranch.captureReaders ++
        elseBranch.captureReaders).eraseDups
  | .iteEmpty _ thenBranch elseBranch =>
      (thenBranch.captureReaders ++ elseBranch.captureReaders).eraseDups

private partial def ExecutableExpr.captureSelectors : ExecutableExpr → List CaptureSelector
  | .literal _ => []
  | .capture _ selector _ _ => [selector]
  | .add left right | .sub left right | .mul left right | .tdiv left right
  | .mod left right | .pow left right =>
      (left.captureSelectors ++ right.captureSelectors).eraseDups
  | .neg expression => expression.captureSelectors
  | .iteEq left right thenBranch elseBranch
  | .iteLt left right thenBranch elseBranch
  | .iteLe left right thenBranch elseBranch =>
      (left.captureSelectors ++ right.captureSelectors ++ thenBranch.captureSelectors ++
        elseBranch.captureSelectors).eraseDups
  | .iteEmpty selector thenBranch elseBranch =>
      (selector :: thenBranch.captureSelectors ++ elseBranch.captureSelectors).eraseDups

private partial def ExecutableExpr.primitiveCaptureExpressions :
    ExecutableExpr → List ExecutableExpr
  | expression@(.capture ..) => [expression]
  | .literal _ => []
  | .add left right | .sub left right | .mul left right | .tdiv left right
  | .mod left right | .pow left right =>
      left.primitiveCaptureExpressions ++ right.primitiveCaptureExpressions
  | .neg expression => expression.primitiveCaptureExpressions
  | .iteEq left right thenBranch elseBranch
  | .iteLt left right thenBranch elseBranch
  | .iteLe left right thenBranch elseBranch =>
      left.primitiveCaptureExpressions ++ right.primitiveCaptureExpressions ++
        thenBranch.primitiveCaptureExpressions ++ elseBranch.primitiveCaptureExpressions
  | .iteEmpty _ thenBranch elseBranch =>
      thenBranch.primitiveCaptureExpressions ++ elseBranch.primitiveCaptureExpressions

private partial def ExecutableExpr.usesPow : ExecutableExpr → Bool
  | .pow _ _ => true
  | .literal _ | .capture .. => false
  | .add left right | .sub left right | .mul left right | .tdiv left right
  | .mod left right =>
      left.usesPow || right.usesPow
  | .neg expression => expression.usesPow
  | .iteEq left right thenBranch elseBranch
  | .iteLt left right thenBranch elseBranch
  | .iteLe left right thenBranch elseBranch =>
      left.usesPow || right.usesPow || thenBranch.usesPow || elseBranch.usesPow
  | .iteEmpty _ thenBranch elseBranch => thenBranch.usesPow || elseBranch.usesPow

private partial def ExecutableConstraint.readers : ExecutableConstraint → List CaptureReader
  | .noLeadingZero _ | .stringEq .. | .card .. => []
  | .le left right | .lt left right | .eq left right =>
      (left.readers ++ right.readers).eraseDups
  | .and left right => (left.readers ++ right.readers).eraseDups

private partial def ExecutableConstraint.captureReaders :
    ExecutableConstraint → List (CaptureSelector × CaptureReader)
  | .noLeadingZero _ | .stringEq .. | .card .. => []
  | .le left right | .lt left right | .eq left right =>
      (left.captureReaders ++ right.captureReaders).eraseDups
  | .and left right => (left.captureReaders ++ right.captureReaders).eraseDups

private partial def ExecutableConstraint.captureSelectors :
    ExecutableConstraint → List CaptureSelector
  | .noLeadingZero selector | .stringEq selector _ => [selector]
  | .card _ _ selectors => selectors.eraseDups
  | .le left right | .lt left right | .eq left right =>
      (left.captureSelectors ++ right.captureSelectors).eraseDups
  | .and left right => (left.captureSelectors ++ right.captureSelectors).eraseDups

private partial def ExecutableConstraint.primitiveCaptureExpressions :
    ExecutableConstraint → List ExecutableExpr
  | .noLeadingZero _ | .stringEq .. | .card .. => []
  | .le left right | .lt left right | .eq left right =>
      left.primitiveCaptureExpressions ++ right.primitiveCaptureExpressions
  | .and left right =>
      left.primitiveCaptureExpressions ++ right.primitiveCaptureExpressions

private partial def ExecutableConstraint.usesPow : ExecutableConstraint → Bool
  | .noLeadingZero _ | .stringEq .. | .card .. => false
  | .le left right | .lt left right | .eq left right => left.usesPow || right.usesPow
  | .and left right => left.usesPow || right.usesPow

private def ExecutableSemanticPlan.readers : ExecutableSemanticPlan → List CaptureReader
  | .int64 expression wfConstraints valueConstraints =>
      (expression.readers ++
        (wfConstraints ++ valueConstraints).flatMap ExecutableConstraint.readers).eraseDups
  | .ip _ _ _ addressExpr prefixExpr wfConstraints valueConstraints =>
      (addressExpr.readers ++ prefixExpr.readers ++
        (wfConstraints ++ valueConstraints).flatMap ExecutableConstraint.readers).eraseDups

private def ExecutableSemanticPlan.captureReaders :
    ExecutableSemanticPlan → List (CaptureSelector × CaptureReader)
  | .int64 expression wfConstraints valueConstraints =>
      (expression.captureReaders ++
        (wfConstraints ++ valueConstraints).flatMap ExecutableConstraint.captureReaders).eraseDups
  | .ip _ _ _ addressExpr prefixExpr wfConstraints valueConstraints =>
      (addressExpr.captureReaders ++ prefixExpr.captureReaders ++
        (wfConstraints ++ valueConstraints).flatMap
          ExecutableConstraint.captureReaders).eraseDups

private def ExecutableSemanticPlan.captureSelectors :
    ExecutableSemanticPlan → List CaptureSelector
  | .int64 expression wfConstraints valueConstraints =>
      (expression.captureSelectors ++
        (wfConstraints ++ valueConstraints).flatMap
          ExecutableConstraint.captureSelectors).eraseDups
  | .ip _ _ _ addressExpr prefixExpr wfConstraints valueConstraints =>
      (addressExpr.captureSelectors ++ prefixExpr.captureSelectors ++
        (wfConstraints ++ valueConstraints).flatMap
          ExecutableConstraint.captureSelectors).eraseDups

private def repeatedExpressions [DecidableEq α] (expressions : List α) : List α :=
  expressions.eraseDups.filter fun expression =>
    1 < expressions.count expression

private def ExecutableSemanticPlan.repeatedPrimitiveCaptureExpressions :
    ExecutableSemanticPlan → List ExecutableExpr
  | .int64 expression wfConstraints valueConstraints =>
      repeatedExpressions
        (expression.primitiveCaptureExpressions ++
          (wfConstraints ++ valueConstraints).flatMap
            ExecutableConstraint.primitiveCaptureExpressions)
  | .ip _ _ _ addressExpr prefixExpr wfConstraints valueConstraints =>
      repeatedExpressions
        (addressExpr.primitiveCaptureExpressions ++ prefixExpr.primitiveCaptureExpressions ++
          (wfConstraints ++ valueConstraints).flatMap
            ExecutableConstraint.primitiveCaptureExpressions)

private def ExecutableSemanticPlan.fusedHexSequenceSelectors
    (plan : ExecutableSemanticPlan) : List CaptureSelector :=
  let uses := plan.captureReaders
  (uses.map Prod.fst).eraseDups.filter fun selector =>
    uses.contains (selector, .hexadecimalSequence)

private inductive SemanticCacheKind where
  | natural
  | hexSequence
  deriving Repr, Inhabited, DecidableEq, BEq

private structure SemanticCacheEntry where
  selector : CaptureSelector
  kind : SemanticCacheKind
  index : Nat
  deriving Repr, Inhabited, DecidableEq, BEq

private def ExecutableSemanticPlan.semanticCacheEntries
    (plan : ExecutableSemanticPlan) : List SemanticCacheEntry :=
  plan.fusedHexSequenceSelectors.zipIdx.map fun (selector, index) =>
    { selector, kind := .hexSequence, index }

private def ExecutableSemanticPlan.usesPow : ExecutableSemanticPlan → Bool
  | .int64 expression wfConstraints valueConstraints =>
      expression.usesPow || (wfConstraints ++ valueConstraints).any ExecutableConstraint.usesPow
  | .ip _ _ _ addressExpr prefixExpr wfConstraints valueConstraints =>
      addressExpr.usesPow || prefixExpr.usesPow ||
        (wfConstraints ++ valueConstraints).any ExecutableConstraint.usesPow

private def ExecutableSemanticPlan.runtimeSemanticBase : ExecutableSemanticPlan → String
  | .int64 .. => runtimeSemanticTemplate
  | .ip .. => runtimeSemanticUnsignedTemplate

/-- Evaluate a closed semantic expression while the parser is generated.

    This is deliberately narrower than `ExecutableExpr.eval`: captures and source-dependent
    branches remain runtime work, while arithmetic made entirely from literals is folded once. -/
private partial def ExecutableExpr.closedValue? : ExecutableExpr → Option Int
  | .literal integer => some integer
  | .capture .. | .iteEmpty .. | .tdiv .. | .mod .. => none
  | .add left right => return (← left.closedValue?) + (← right.closedValue?)
  | .sub left right => return (← left.closedValue?) - (← right.closedValue?)
  | .mul left right => return (← left.closedValue?) * (← right.closedValue?)
  | .pow base exponent => do
      let baseValue ← base.closedValue?
      let exponentValue ← exponent.closedValue?
      guard (0 ≤ exponentValue)
      pure (baseValue ^ exponentValue.toNat)
  | .neg expression => return -(← expression.closedValue?)
  | .iteEq left right thenBranch elseBranch => do
      if (← left.closedValue?) == (← right.closedValue?) then
        thenBranch.closedValue?
      else
        elseBranch.closedValue?
  | .iteLt left right thenBranch elseBranch => do
      if (← left.closedValue?) < (← right.closedValue?) then
        thenBranch.closedValue?
      else
        elseBranch.closedValue?
  | .iteLe left right thenBranch elseBranch => do
      if (← left.closedValue?) ≤ (← right.closedValue?) then
        thenBranch.closedValue?
      else
        elseBranch.closedValue?

private def u128Maximum : Int :=
  340282366920938463463374607431768211455

private def ValueRange.fitsU128 (range : ValueRange) : Bool :=
  0 ≤ range.lower && range.upper ≤ u128Maximum

/-- The fragment lowered to direct `u128` arithmetic. Multiplication remains linear in one
    runtime operand, which keeps both generated verification conditions and emitted code small. -/
private partial def ExecutableExpr.primitiveNatEligible : ExecutableExpr → Bool
  | expression@(.literal _) =>
      expression.range?.any ValueRange.fitsU128
  | expression@(.capture _ _ reader _) =>
      expression.range?.any ValueRange.fitsU128 &&
        (reader == .natural || reader == .length || reader == .count ||
          reader == .hexadecimalSequence || reader == .segments)
  | expression@(.add left right) | expression@(.sub left right) =>
      expression.range?.any ValueRange.fitsU128 &&
        left.primitiveNatEligible && right.primitiveNatEligible
  | expression@(.mul left right) =>
      expression.range?.any ValueRange.fitsU128 &&
        left.primitiveNatEligible && right.primitiveNatEligible &&
        (left.closedValue?.isSome || right.closedValue?.isSome)
  | expression@(.pow _ _) =>
      expression.range?.any ValueRange.fitsU128 && expression.closedValue?.isSome
  | expression@(.iteEq left right thenBranch elseBranch)
  | expression@(.iteLt left right thenBranch elseBranch)
  | expression@(.iteLe left right thenBranch elseBranch) =>
      expression.range?.any ValueRange.fitsU128 &&
        left.primitiveNatEligible && right.primitiveNatEligible &&
        thenBranch.primitiveNatEligible && elseBranch.primitiveNatEligible
  | expression@(.iteEmpty _ thenBranch elseBranch) =>
      expression.range?.any ValueRange.fitsU128 &&
        thenBranch.primitiveNatEligible && elseBranch.primitiveNatEligible
  | .tdiv .. | .mod .. | .neg .. => false

private partial def ExecutableConstraint.primitiveNatEligible :
    ExecutableConstraint → Bool
  | .noLeadingZero _ | .stringEq .. | .card .. => true
  | .le left right | .lt left right | .eq left right =>
      left.primitiveNatEligible && right.primitiveNatEligible
  | .and left right => left.primitiveNatEligible && right.primitiveNatEligible

private def renderRuntimeSemanticSupport (plan : ExecutableSemanticPlan) : String :=
  let readers := plan.readers
  String.intercalate "\n\n" <|
    [if readers.any fun reader =>
        reader == .natural || reader == .integer then runtimeSemanticNatTemplate else "",
     if readers.any fun reader =>
        reader == .sign || reader == .prefixSign then runtimeSemanticSignTemplate else "",
     if readers.contains .hexadecimalSequence then runtimeSemanticHexSequenceTemplate else "",
     if readers.contains .segments then runtimeSemanticSegmentsTemplate else "",
     if plan.usesPow then runtimeSemanticPowTemplate else ""].filter (· != "")

private def rustLeftBrace : String := "{"
private def rustRightBrace : String := "}"

private def semanticCacheType (format : FormatInput) : String :=
  typeName format.name ++ "SemanticCache"

private def semanticCacheField (entry : SemanticCacheEntry) : String :=
  s!"cache_{entry.index}"

private def semanticCacheSetter (entry : SemanticCacheEntry) : String :=
  s!"set_cache_{entry.index}"

private def semanticCacheValueType : SemanticCacheKind → String
  | .natural => "CachedSemanticNatural"
  | .hexSequence => "CachedSemanticHexSequence"

private def renderSemanticCacheSupport (entries : List SemanticCacheEntry) : String :=
  String.intercalate "\n\n" <|
    [if entries.any (·.kind == .natural) then runtimeSemanticNaturalCacheTemplate else "",
     if entries.any (·.kind == .hexSequence) then
       runtimeSemanticHexSequenceCacheTemplate
     else ""].filter (· != "")

private def renderSemanticCache (format : FormatInput)
    (entries : List SemanticCacheEntry) : String :=
  let cacheType := semanticCacheType format
  let fields := entries.map fun entry =>
    s!"    {semanticCacheField entry}: Option<{semanticCacheValueType entry.kind}>,"
  let matchClauses := entries.map fun entry =>
    s!"match self.{semanticCacheField entry} {rustLeftBrace}
            Some(value) => value.source_matches(input),
            None => true,
        {rustRightBrace}"
  let initializers := entries.map fun entry =>
    s!"            {semanticCacheField entry}: None,"
  let setters := entries.map fun entry =>
    let field := semanticCacheField entry
    let setter := semanticCacheSetter entry
    let valueType := semanticCacheValueType entry.kind
    s!"    #[inline(always)]
    fn {setter}(
        &mut self,
        input: Ghost<Seq<char>>,
        value: {valueType},
    )
        requires
            old(self).matches_input(input@),
            value.source_matches(input@),
        ensures
            final(self).matches_input(input@),
            final(self).{field}.is_some(),
    {rustLeftBrace}
        self.{field} = Some(value);
    {rustRightBrace}"
  let matchesBody :=
    match matchClauses with
    | [] => "true"
    | clauses => String.intercalate "\n            && " (clauses.map fun part => s!"({part})")
  s!"#[derive(Copy, Clone)]
pub struct {cacheType} {rustLeftBrace}
{String.intercalate "\n" fields}
{rustRightBrace}

impl {cacheType} {rustLeftBrace}
    pub closed spec fn matches_input(&self, input: Seq<char>) -> bool {rustLeftBrace}
        {matchesBody}
    {rustRightBrace}

    #[inline(always)]
    fn new(input: Ghost<Seq<char>>) -> (result: Self)
        ensures
            result.matches_input(input@),
    {rustLeftBrace}
        Self {rustLeftBrace}
{String.intercalate "\n" initializers}
        {rustRightBrace}
    {rustRightBrace}

{String.intercalate "\n\n" setters}
{rustRightBrace}"

private def semanticCacheEntryForKey (grammar : FlatGrammar)
    (entries : List SemanticCacheEntry) (key : String) : Option SemanticCacheEntry := do
  let selector ← captureSelector? grammar key
  entries.find? (·.selector == selector)

private def renderSemanticCacheWrites (grammar : FlatGrammar)
    (entries : List SemanticCacheEntry) (keys : List String)
    (start end_ : String) : Except String String := do
  let writes ← keys.filterMapM fun key => do
    let some entry := semanticCacheEntryForKey grammar entries key | pure none
    if entry.kind == .hexSequence then
      -- Colon-separated hexadecimal values are accumulated by the direct repetition scanner.
      -- Reconstructing them here would reread the capture after recognition.
      pure none
    else
      let some selector := captureSelector? grammar key
        | throw s!"Verus backend: semantic cache cannot resolve capture key `{key}`"
      let renderedKey := renderCaptureSelector selector
      let setter := semanticCacheSetter entry
      let constructor := match entry.kind with
        | .natural => "CachedSemanticNatural"
        | .hexSequence => "CachedSemanticHexSequence"
      pure <| some s!"        let cached_capture_{entry.index} = RuntimeCapture {rustLeftBrace}
            key: {renderedKey},
            start: {start},
            end: {end_},
            count: 0,
            is_count: false,
        {rustRightBrace};
        let cached_value_{entry.index} = {constructor}::new(
            input,
            input_ascii,
            cached_capture_{entry.index},
        );
        state.semantic_cache.{setter}(Ghost(input@), cached_value_{entry.index});"
  pure (String.intercalate "\n" writes)

private partial def renderExecutableExprSpec (format : FormatInput)
    (expression : ExecutableExpr) : String :=
  match expression.closedValue? with
  | some integer => s!"({integer}int)"
  | none =>
      match expression with
      | .literal integer => s!"({integer}int)"
      | .capture _ selector reader _ =>
          let text := renderSemanticCaptureText format selector
          match reader with
          | .natural => s!"triptych_nat_of({text})"
          | .integer => s!"triptych_int_of({text})"
          | .length => s!"({text}.len() as int)"
          | .count => renderSemanticCaptureCount format selector
          | .hexadecimal => s!"triptych_hex_of({text})"
          | .hexadecimalSequence => s!"triptych_hex_seq_of({text})"
          | .segments => s!"triptych_segments_of({text})"
          | .sign | .prefixSign => s!"triptych_sign_of({text})"
      | .add left right =>
          s!"({renderExecutableExprSpec format left} + {renderExecutableExprSpec format right})"
      | .sub left right =>
          s!"({renderExecutableExprSpec format left} - {renderExecutableExprSpec format right})"
      | .mul left right =>
          s!"({renderExecutableExprSpec format left} * {renderExecutableExprSpec format right})"
      | .tdiv left right =>
          s!"rust_div({renderExecutableExprSpec format left}, \
            {renderExecutableExprSpec format right})"
      | .mod left right =>
          s!"rust_rem({renderExecutableExprSpec format left}, \
            {renderExecutableExprSpec format right})"
      | .pow base exponent =>
          s!"triptych_int_pow({renderExecutableExprSpec format base}, \
            {renderExecutableExprSpec format exponent})"
      | .neg inner => s!"(-{renderExecutableExprSpec format inner})"
      | .iteEq left right thenBranch elseBranch =>
          "if " ++ renderExecutableExprSpec format left ++ " == " ++
            renderExecutableExprSpec format right ++ " {\n" ++
            indentText 1 (renderExecutableExprSpec format thenBranch) ++
            "\n} else {\n" ++
            indentText 1 (renderExecutableExprSpec format elseBranch) ++ "\n}"
      | .iteLt left right thenBranch elseBranch =>
          "if " ++ renderExecutableExprSpec format left ++ " < " ++
            renderExecutableExprSpec format right ++ " {\n" ++
            indentText 1 (renderExecutableExprSpec format thenBranch) ++
            "\n} else {\n" ++
            indentText 1 (renderExecutableExprSpec format elseBranch) ++ "\n}"
      | .iteLe left right thenBranch elseBranch =>
          "if " ++ renderExecutableExprSpec format left ++ " <= " ++
            renderExecutableExprSpec format right ++ " {\n" ++
            indentText 1 (renderExecutableExprSpec format thenBranch) ++
            "\n} else {\n" ++
            indentText 1 (renderExecutableExprSpec format elseBranch) ++ "\n}"
      | .iteEmpty selector thenBranch elseBranch =>
          "if " ++ renderSemanticCaptureText format selector ++ " == seq![] {\n" ++
            indentText 1 (renderExecutableExprSpec format thenBranch) ++
            "\n} else {\n" ++
            indentText 1 (renderExecutableExprSpec format elseBranch) ++ "\n}"

private def renderSafetyConjunction (parts : List String) : String :=
  match parts.eraseDups with
  | [] => "true"
  | parts => String.intercalate "\n        && " (parts.map fun part => s!"({part})")

private def renderSemanticCaptureSafety (selector : CaptureSelector) : String :=
  let key := renderCaptureSelector selector
  s!"match first_runtime_capture(candidate.captures, {key}) {rustLeftBrace}
            Some(capture) =>
                capture.start <= capture.end && capture.end <= input.len(),
            None => true,
        {rustRightBrace}"

private def renderIntRuntimeBound (expression : String) : String :=
  s!"(-170141183460469231731687303715884105728int) <= {expression}
            && {expression} <= (170141183460469231731687303715884105727int)"

private def renderNatRuntimeBound (expression : String) : String :=
  s!"(0int) <= {expression}
            && {expression} <= (340282366920938463463374607431768211455int)"

private partial def renderExecutableExprRuntimeSafe (format : FormatInput) (useNat : Bool) :
    ExecutableExpr → String
  | expression@(.literal _) =>
      let rendered := renderExecutableExprSpec format expression
      if useNat then renderNatRuntimeBound rendered else renderIntRuntimeBound rendered
  | expression@(.capture _ selector _ range) =>
      let rendered := renderExecutableExprSpec format expression
      renderSafetyConjunction
        [renderSemanticCaptureSafety selector,
         match range with
         | some range =>
             s!"({range.lower}int) <= {rendered}
            && {rendered} <= ({range.upper}int)"
         | none => "true",
         if useNat then renderNatRuntimeBound rendered else renderIntRuntimeBound rendered]
  | expression@(.add left right)
  | expression@(.sub left right)
  | expression@(.mul left right)
  | expression@(.pow left right) =>
      let rendered := renderExecutableExprSpec format expression
      renderSafetyConjunction
        [renderExecutableExprRuntimeSafe format useNat left,
         renderExecutableExprRuntimeSafe format useNat right,
         if useNat then renderNatRuntimeBound rendered else renderIntRuntimeBound rendered]
  | expression@(.tdiv left right)
  | expression@(.mod left right) =>
      let rightValue := renderExecutableExprSpec format right
      let rendered := renderExecutableExprSpec format expression
      renderSafetyConjunction
        [renderExecutableExprRuntimeSafe format useNat left,
         renderExecutableExprRuntimeSafe format useNat right,
         s!"(0int) < {rightValue}",
         if useNat then renderNatRuntimeBound rendered else renderIntRuntimeBound rendered]
  | expression@(.neg inner) =>
      let rendered := renderExecutableExprSpec format expression
      renderSafetyConjunction
        [renderExecutableExprRuntimeSafe format useNat inner,
         if useNat then renderNatRuntimeBound rendered else renderIntRuntimeBound rendered]
  | expression@(.iteEq left right thenBranch elseBranch)
  | expression@(.iteLt left right thenBranch elseBranch)
  | expression@(.iteLe left right thenBranch elseBranch) =>
      let rendered := renderExecutableExprSpec format expression
      renderSafetyConjunction
        [renderExecutableExprRuntimeSafe format useNat left,
         renderExecutableExprRuntimeSafe format useNat right,
         renderExecutableExprRuntimeSafe format useNat thenBranch,
         renderExecutableExprRuntimeSafe format useNat elseBranch,
         if useNat then renderNatRuntimeBound rendered else renderIntRuntimeBound rendered]
  | expression@(.iteEmpty selector thenBranch elseBranch) =>
      let rendered := renderExecutableExprSpec format expression
      renderSafetyConjunction
        [renderSemanticCaptureSafety selector,
         renderExecutableExprRuntimeSafe format useNat thenBranch,
         renderExecutableExprRuntimeSafe format useNat elseBranch,
         if useNat then renderNatRuntimeBound rendered else renderIntRuntimeBound rendered]

private partial def renderExecutableConstraintRuntimeSafe (format : FormatInput) (useNat : Bool) :
    ExecutableConstraint → String
  | .noLeadingZero selector | .stringEq selector _ =>
      renderSemanticCaptureSafety selector
  | .card _ _ selectors =>
      renderSafetyConjunction (selectors.map renderSemanticCaptureSafety)
  | .le left right | .lt left right | .eq left right =>
      renderSafetyConjunction
        [renderExecutableExprRuntimeSafe format useNat left,
         renderExecutableExprRuntimeSafe format useNat right]
  | .and left right =>
      renderSafetyConjunction
        [renderExecutableConstraintRuntimeSafe format useNat left,
         renderExecutableConstraintRuntimeSafe format useNat right]

private def renderExecutableConstraintsRuntimeSafe (format : FormatInput) (useNat : Bool)
    (constraints : List ExecutableConstraint) : String :=
  renderSafetyConjunction
    (constraints.map (renderExecutableConstraintRuntimeSafe format useNat))

private def renderCardComparison (operation : CardOp) (minimum : Nat) (present : String) :
    String :=
  match operation with
  | .atLeast => s!"({minimum}int) <= {present}"
  | .atMost => s!"{present} <= ({minimum}int)"
  | .exactlyK => s!"{present} == ({minimum}int)"

private partial def renderExecutableConstraintSpec (format : FormatInput) :
    ExecutableConstraint → String
  | .noLeadingZero selector =>
      let text := renderSemanticCaptureText format selector
      let zero := semanticCharacterLiteral '0'
      s!"{text}.len() == 0 || {text}[0] != {zero} || {text} == seq![{zero}]"
  | .stringEq selector literal =>
      let text := renderSemanticCaptureText format selector
      s!"{text}.len() == 0 || {text} == {renderSemanticTextLiteral literal}"
  | .card operation minimum selectors =>
      let present :=
        match selectors with
        | [] => "(0int)"
        | _ =>
            String.intercalate " + " <| selectors.map fun selector =>
              "(if " ++ renderSemanticCaptureText format selector ++
                ".len() == 0 { (0int) } else { (1int) })"
      renderCardComparison operation minimum present
  | .le left right =>
      s!"{renderExecutableExprSpec format left} <= {renderExecutableExprSpec format right}"
  | .lt left right =>
      s!"{renderExecutableExprSpec format left} < {renderExecutableExprSpec format right}"
  | .eq left right =>
      s!"{renderExecutableExprSpec format left} == {renderExecutableExprSpec format right}"
  | .and left right =>
      s!"({renderExecutableConstraintSpec format left}) && \
        ({renderExecutableConstraintSpec format right})"

private def renderExecutableConstraintsSpec (format : FormatInput)
    (constraints : List ExecutableConstraint) : String :=
  match constraints with
  | [] => "true"
  | _ =>
      String.intercalate "\n        && " <|
        constraints.map fun constraint =>
          s!"({renderExecutableConstraintSpec format constraint})"

private def renderRuntimeSemanticSpec (format : FormatInput)
    (plan : ExecutableSemanticPlan) : String :=
  let formatPrefix := snakeCase format.name
  let valueName := formatPrefix ++ "_candidate_value"
  let wfName := formatPrefix ++ "_candidate_wf_constraints"
  let constraintsName := formatPrefix ++ "_candidate_constraints"
  let validName := formatPrefix ++ "_candidate_is_valid"
  let safeName := formatPrefix ++ "_candidate_runtime_safe"
  let leftBrace := "{"
  let rightBrace := "}"
  let common :=
    s!"pub open spec fn {semanticCaptureTextFunction format}(
    input: Seq<char>,
    candidate: CandidateSpec,
    key: CaptureKey,
) -> Seq<char> {leftBrace}
    match first_runtime_capture(candidate.captures, key) {leftBrace}
        Some(capture) =>
            input.subrange(capture.start as int, capture.end as int),
        None => seq![],
    {rightBrace}
{rightBrace}

pub open spec fn {semanticCaptureCountFunction format}(
    candidate: CandidateSpec,
    key: CaptureKey,
) -> int {leftBrace}
    match first_runtime_capture(candidate.captures, key) {leftBrace}
        Some(capture) => capture.count as int,
        None => 0,
    {rightBrace}
{rightBrace}
"
  match plan with
  | .int64 expression wfConstraints valueConstraints =>
      let renderedValue := renderExecutableExprSpec format expression
      let runtimeSafe :=
        renderSafetyConjunction
          [renderExecutableExprRuntimeSafe format false expression,
           renderExecutableConstraintsRuntimeSafe format false
             (wfConstraints ++ valueConstraints),
           s!"(-9223372036854775808int) <= {renderedValue}
                && {renderedValue} <= (9223372036854775807int)"]
      common ++ s!"
pub open spec fn {valueName}(input: Seq<char>, candidate: CandidateSpec) -> int {leftBrace}
{indentText 1 renderedValue}
{rightBrace}

pub open spec fn {wfName}(input: Seq<char>, candidate: CandidateSpec) -> bool {leftBrace}
{indentText 1 (renderExecutableConstraintsSpec format wfConstraints)}
{rightBrace}

pub open spec fn {constraintsName}(input: Seq<char>, candidate: CandidateSpec) -> bool {leftBrace}
{indentText 1 (renderExecutableConstraintsSpec format valueConstraints)}
{rightBrace}

pub open spec fn {validName}(input: Seq<char>, candidate: CandidateSpec) -> bool {leftBrace}
    {wfName}(input, candidate)
        && {constraintsName}(input, candidate)
{rightBrace}

pub open spec fn {safeName}(input: Seq<char>, candidate: CandidateSpec) -> bool {leftBrace}
{indentText 1 runtimeSafe}
{rightBrace}
"
  | .ip family addressBits radix addressExpr prefixExpr wfConstraints valueConstraints =>
      let addressBound :=
        if addressBits == 128 then
          "340282366920938463463374607431768211456int"
        else
          s!"{(2 : Nat) ^ addressBits}int"
      let runtimeSafe :=
        renderSafetyConjunction
          [renderExecutableExprRuntimeSafe format true addressExpr,
           renderExecutableExprRuntimeSafe format true prefixExpr,
           renderExecutableConstraintsRuntimeSafe format true
             (wfConstraints ++ valueConstraints)]
      common ++ s!"
pub open spec fn {formatPrefix}_candidate_address(
    input: Seq<char>,
    candidate: CandidateSpec,
) -> int {leftBrace}
{indentText 1 (renderExecutableExprSpec format addressExpr)}
{rightBrace}

pub open spec fn {formatPrefix}_candidate_prefix(
    input: Seq<char>,
    candidate: CandidateSpec,
) -> int {leftBrace}
{indentText 1 (renderExecutableExprSpec format prefixExpr)}
{rightBrace}

pub open spec fn {valueName}(input: Seq<char>, candidate: CandidateSpec) -> int {leftBrace}
    {formatPrefix}_candidate_address(input, candidate) * ({radix}int)
        + {formatPrefix}_candidate_prefix(input, candidate)
{rightBrace}

pub open spec fn {wfName}(input: Seq<char>, candidate: CandidateSpec) -> bool {leftBrace}
{indentText 1 (renderExecutableConstraintsSpec format wfConstraints)}
{rightBrace}

pub open spec fn {constraintsName}(input: Seq<char>, candidate: CandidateSpec) -> bool {leftBrace}
{indentText 1 (renderExecutableConstraintsSpec format valueConstraints)}
{rightBrace}

pub open spec fn {validName}(input: Seq<char>, candidate: CandidateSpec) -> bool {leftBrace}
    {wfName}(input, candidate)
        && {constraintsName}(input, candidate)
        && 0 <= {formatPrefix}_candidate_address(input, candidate)
        && {formatPrefix}_candidate_address(input, candidate)
            < {addressBound}
        && 0 <= {formatPrefix}_candidate_prefix(input, candidate)
        && {formatPrefix}_candidate_prefix(input, candidate) < {radix}
{rightBrace}

pub open spec fn {safeName}(input: Seq<char>, candidate: CandidateSpec) -> bool {leftBrace}
{indentText 1 runtimeSafe}
{rightBrace}

pub open spec fn {formatPrefix}_candidate_family() -> int {leftBrace}
    {family}
{rightBrace}
"

private structure SemanticRenderState where
  next : Nat := 0
  lines : List String := []
  spans : List (CaptureSelector × String) := []
  hexSequenceSummaries : List (CaptureSelector × String) := []
  semanticCacheEntries : List SemanticCacheEntry := []
  fusedHexSequenceSelectors : List CaptureSelector := []
  intExpressions : List (ExecutableExpr × String) := []
  natExpressions : List (ExecutableExpr × String) := []
  primitiveNatExpressions : List (ExecutableExpr × String) := []
  searchState : Bool := false

private abbrev SemanticRenderM := StateT SemanticRenderState (Except String)

private def emitSemanticLine (line : String) : SemanticRenderM Unit :=
  modify fun state => { state with lines := state.lines ++ [line] }

private def freshSemanticName (stem : String) : SemanticRenderM String := do
  let state ← get
  set { state with next := state.next + 1 }
  pure s!"{stem}_{state.next}"

private def semanticCacheEntryFor (selector : CaptureSelector)
    (kind : SemanticCacheKind) : SemanticRenderM (Option SemanticCacheEntry) := do
  let state ← get
  if state.searchState then
    pure <| state.semanticCacheEntries.find? fun entry =>
      entry.selector == selector && entry.kind == kind
  else
    pure none

private def semanticCaptureIndexType (format : FormatInput) : String :=
  typeName format.name ++ "SemanticCaptureIndex"

private def semanticCaptureIndexFunction (format : FormatInput) : String :=
  functionName format.name "index_semantic_captures"

private def semanticCaptureIndexField (index : Nat) : String :=
  s!"capture_{index}"

private def semanticSpanFor (format : FormatInput) (selector : CaptureSelector) :
    SemanticRenderM String := do
  let state ← get
  match state.spans.find? (·.1 == selector) with
  | some (_, name) => pure name
  | none =>
      let name ← freshSemanticName "span"
      let key := renderCaptureSelector selector
      if state.searchState then
        let field := semanticCaptureIndexField state.spans.length
        emitSemanticLine s!"let {name} = match semantic_indexed_capture_span(
    capture_index.{field},
    input,
    input_length,
) {rustLeftBrace}
    Some(span) => span,
    None => return None,
{rustRightBrace};"
        emitSemanticLine s!"proof {rustLeftBrace}
    reveal({semanticCaptureTextFunction format});
    reveal({semanticCaptureCountFunction format});
    reveal(semantic_candidate_capture_text);
    reveal(semantic_candidate_capture_count);
    reveal(semantic_optional_capture_text);
    reveal(semantic_optional_capture_count);
    assert(capture_index.{field}
        == first_runtime_capture(candidate_view.captures, {key}));
    assert(semantic_span_text(input@, {name})
        == {semanticCaptureTextFunction format}(
            input@,
            candidate_view,
            {key},
        ));
    assert({name}.count as int
        == {semanticCaptureCountFunction format}(candidate_view, {key}));
{rustRightBrace}"
      else
        emitSemanticLine s!"let {name} = match semantic_capture_span(
    &candidate,
    {key},
    input,
    input_length,
) {rustLeftBrace}
    Some(span) => span,
    None => return None,
{rustRightBrace};"
        emitSemanticLine s!"proof {rustLeftBrace}
    reveal({semanticCaptureTextFunction format});
    assert(semantic_span_text(input@, {name})
        == {semanticCaptureTextFunction format}(
            input@,
            candidate_view,
            {key},
        ));
{rustRightBrace}"
      modify fun state => { state with spans := state.spans ++ [(selector, name)] }
      pure name

private def semanticNaturalFor (format : FormatInput)
    (selector : CaptureSelector) : SemanticRenderM String := do
  let span ← semanticSpanFor format selector
  let name ← freshSemanticName "nat_value"
  match ← semanticCacheEntryFor selector .natural with
  | some entry =>
      emitSemanticLine s!"let {name} = match candidate.semantic_cache.{semanticCacheField entry} {rustLeftBrace}
    Some(cached) if {span}.present
        && cached.capture.start == {span}.start
        && cached.capture.end == {span}.end => {rustLeftBrace}
        proof {rustLeftBrace}
            use_type_invariant(&cached);
            assert(candidate.semantic_cache.matches_input(input@));
            assert(cached.source_matches(input@));
            reveal(semantic_span_text);
        {rustRightBrace}
        cached.value
    {rustRightBrace},
    _ => semantic_nat_of_span_fast(input, input_ascii, {span}),
{rustRightBrace};"
  | none =>
      emitSemanticLine
        s!"let {name} = semantic_nat_of_span_fast(input, input_ascii, {span});"
  pure name

private def semanticHexSequenceSummaryFor (format : FormatInput)
    (selector : CaptureSelector) : SemanticRenderM String := do
  let state ← get
  match state.hexSequenceSummaries.find? (·.1 == selector) with
  | some (_, name) => pure name
  | none =>
      let span ← semanticSpanFor format selector
      let name ← freshSemanticName "hex_sequence"
      match ← semanticCacheEntryFor selector .hexSequence with
      | some entry =>
          emitSemanticLine s!"let {name} = match candidate.semantic_cache.{semanticCacheField entry} {rustLeftBrace}
    Some(cached) if {span}.present
        && cached.start == {span}.start
        && cached.end == {span}.end => {rustLeftBrace}
        proof {rustLeftBrace}
            use_type_invariant(&cached);
            assert(candidate.semantic_cache.matches_input(input@));
            assert(cached.source_matches(input@));
            reveal(semantic_span_text);
        {rustRightBrace}
        cached.semantic_summary()
    {rustRightBrace},
    _ => semantic_hex_sequence_summary_of_span_fast(
        input,
        input_ascii,
        {span},
    ),
{rustRightBrace};"
      | none =>
          emitSemanticLine s!"let {name} = semantic_hex_sequence_summary_of_span_fast(
    input,
    input_ascii,
    {span},
);"
      modify fun state =>
        { state with
          hexSequenceSummaries := state.hexSequenceSummaries ++ [(selector, name)] }
      pure name

private def intLiteral? (integer : Int) : Option String :=
  if integer == (-170141183460469231731687303715884105728 : Int) then
    some "i128::MIN"
  else if (-170141183460469231731687303715884105728 : Int) ≤ integer &&
      integer ≤ (170141183460469231731687303715884105727 : Int) then
    some s!"{integer}i128"
  else
    none

private def natLiteral? (integer : Int) : Option String :=
  if 0 ≤ integer && integer ≤ (340282366920938463463374607431768211455 : Int) then
    some s!"{integer}u128"
  else
    none

private def semanticMatchBool (name call : String) : String :=
  s!"let {name} = match {call} {rustLeftBrace}
    Some(value) => value,
    None => return None,
{rustRightBrace};"

private def semanticRuntimeSafeCall (format : FormatInput) : String :=
  s!"{snakeCase format.name}_candidate_runtime_safe(input@, candidate_view)"

private def semanticRuntimeSafetyProof (format : FormatInput) (conclusion : String) : String :=
  s!"proof {rustLeftBrace}
    assert({semanticRuntimeSafeCall format} ==> {conclusion});
{rustRightBrace}"

private partial def renderSemanticIntExpr (format : FormatInput) (expression : ExecutableExpr) :
    SemanticRenderM String := do
  let state ← get
  match state.intExpressions.find? (·.1 == expression) with
  | some (_, name) => pure name
  | none =>
      let name ← freshSemanticName "int_value"
      match expression with
      | .literal integer =>
          let literal ← match intLiteral? integer with
            | some literal => pure literal
            | none => throw s!"Verus backend: signed semantic literal `{integer}` exceeds i128"
          emitSemanticLine s!"let {name} = SemanticInt::new({literal});"
      | .capture _ selector reader _ =>
          let span ← semanticSpanFor format selector
          let fuseHexSequence := (← get).fusedHexSequenceSelectors.contains selector
          match reader with
          | .natural =>
              let natural ← semanticNaturalFor format selector
              emitSemanticLine s!"let {name} = SemanticInt::from_nat(&{natural});"
          | .sign | .prefixSign =>
              emitSemanticLine
                s!"let {name} = semantic_sign_of_span(input, input_ascii, {span});"
          | .count =>
              emitSemanticLine s!"let {name}_nat = semantic_span_count({span});"
              emitSemanticLine s!"let {name} = SemanticInt::from_nat(&{name}_nat);"
          | .length =>
              emitSemanticLine s!"let {name}_nat = SemanticNat::new(
    ({span}.end - {span}.start) as u128,
);"
              emitSemanticLine s!"let {name} = SemanticInt::from_nat(&{name}_nat);"
          | .hexadecimalSequence =>
              if fuseHexSequence then
                let summary ← semanticHexSequenceSummaryFor format selector
                emitSemanticLine s!"let {name}_nat = {summary}.value;"
              else
                emitSemanticLine
                  s!"let {name}_nat = semantic_hex_sequence_of_span(
    input,
    input_ascii,
    {span},
);"
              emitSemanticLine s!"let {name} = SemanticInt::from_nat(&{name}_nat);"
          | .segments =>
              if fuseHexSequence then
                let summary ← semanticHexSequenceSummaryFor format selector
                emitSemanticLine s!"let {name}_nat = {summary}.segments;"
              else
                emitSemanticLine
                  s!"let {name}_nat = semantic_segments_of_span(input, input_ascii, {span});"
              emitSemanticLine s!"let {name} = SemanticInt::from_nat(&{name}_nat);"
          | .integer | .hexadecimal =>
              throw s!"Verus backend: executable reader `{repr reader}` is not implemented"
      | .add left right | .sub left right | .mul left right
      | .tdiv left right | .mod left right =>
          let leftName ← renderSemanticIntExpr format left
          let rightName ← renderSemanticIntExpr format right
          let method := match expression with
            | .add .. => "add"
            | .sub .. => "sub"
            | .mul .. => "mul"
            | .tdiv .. => "tdiv"
            | .mod .. => "modulo"
            | _ => unreachable!
          emitSemanticLine s!"let {name} = {leftName}.{method}(&{rightName});"
      | .neg inner =>
          let innerName ← renderSemanticIntExpr format inner
          emitSemanticLine s!"let {name} = {innerName}.neg();"
      | .iteEq left right thenBranch elseBranch
      | .iteLt left right thenBranch elseBranch
      | .iteLe left right thenBranch elseBranch =>
          let leftName ← renderSemanticIntExpr format left
          let rightName ← renderSemanticIntExpr format right
          let thenName ← renderSemanticIntExpr format thenBranch
          let elseName ← renderSemanticIntExpr format elseBranch
          let condition ← freshSemanticName "condition"
          let method := match expression with
            | .iteEq .. => "eq"
            | .iteLt .. => "lt"
            | .iteLe .. => "le"
            | _ => unreachable!
          emitSemanticLine (semanticRuntimeSafetyProof format
            s!"{leftName}.available() && {rightName}.available()")
          emitSemanticLine (semanticMatchBool condition
            s!"{leftName}.{method}(&{rightName})")
          emitSemanticLine s!"let {name} = if {condition} {rustLeftBrace}
    {thenName}
{rustRightBrace} else {rustLeftBrace}
    {elseName}
{rustRightBrace};"
      | .iteEmpty selector thenBranch elseBranch =>
          let span ← semanticSpanFor format selector
          let base ← get
          let (thenName, thenState) ←
            (renderSemanticIntExpr format thenBranch).run { base with lines := [] }
          let (elseName, elseState) ←
            (renderSemanticIntExpr format elseBranch).run
              { base with next := thenState.next, lines := [] }
          set { base with next := elseState.next }
          let thenLines := String.intercalate "\n" thenState.lines
          let elseLines := String.intercalate "\n" elseState.lines
          emitSemanticLine s!"let {name} =
    if semantic_span_is_empty(input, {span}) {rustLeftBrace}
{indentText 2 thenLines}
        {thenName}
    {rustRightBrace} else {rustLeftBrace}
{indentText 2 elseLines}
        {elseName}
    {rustRightBrace};"
      | .pow .. =>
          throw "Verus backend: signed semantic exponentiation is not implemented"
      emitSemanticLine (semanticRuntimeSafetyProof format s!"{name}.available()")
      modify fun state =>
        { state with intExpressions := state.intExpressions ++ [(expression, name)] }
      pure name

private def primitiveNatRange (expression : ExecutableExpr) :
    SemanticRenderM ValueRange :=
  match expression.range? with
  | some range =>
      if range.fitsU128 then pure range
      else throw s!"Verus backend: primitive unsigned range `{repr range}` exceeds u128"
  | none => throw "Verus backend: primitive unsigned expression has no inferred range"

private def renderExecutableExprCandidateViewSpec (format : FormatInput)
    (expression : ExecutableExpr) : String :=
  (renderExecutableExprSpec format expression)
    |>.replace
      (semanticCaptureTextFunction format ++ "(input, candidate,")
      (semanticCaptureTextFunction format ++ "(input@, candidate_view,")
    |>.replace
      (semanticCaptureCountFunction format ++ "(candidate,")
      (semanticCaptureCountFunction format ++ "(candidate_view,")

private def emitPrimitiveNatBounds (format : FormatInput) (expression : ExecutableExpr)
    (name : String) (checkInferredRange : Bool := false) : SemanticRenderM Unit := do
  let range ← primitiveNatRange expression
  let rendered := renderExecutableExprCandidateViewSpec format expression
  if checkInferredRange then
    emitSemanticLine s!"proof {rustLeftBrace}
    assert({name} as int == {rendered});
    assert({semanticRuntimeSafeCall format} ==> ({range.lower}int) <= {name} as int);
    assert({semanticRuntimeSafeCall format} ==> {name} as int <= ({range.upper}int));
{rustRightBrace}"
    if 0 < range.lower then
      emitSemanticLine s!"if {name} < {range.lower}u128 {rustLeftBrace}
    return None;
{rustRightBrace}"
    if range.upper < u128Maximum then
      emitSemanticLine s!"if {name} > {range.upper}u128 {rustLeftBrace}
    return None;
{rustRightBrace}"
  emitSemanticLine s!"proof {rustLeftBrace}
    assert({name} as int == {rendered});
    assert(({range.lower}int) <= {name} as int);
    assert({name} as int <= ({range.upper}int));
{rustRightBrace}"

private def unwrapPrimitiveNat (format : FormatInput) (expression : ExecutableExpr)
    (source name : String) : SemanticRenderM Unit := do
  emitSemanticLine s!"let {name} = match {source}.to_option() {rustLeftBrace}
    Some(value) => value,
    None => return None,
{rustRightBrace};"
  emitPrimitiveNatBounds format expression name true

/-- Lower a statically bounded nonnegative expression to direct `u128` operations. Each capture
    is checked once against its grammar-derived range; arithmetic thereafter contains no
    `SemanticNat` wrapper or candidate enumeration. -/
private partial def renderPrimitiveNatExpr (format : FormatInput)
    (expression : ExecutableExpr) : SemanticRenderM String := do
  let state ← get
  match state.primitiveNatExpressions.find? (·.1 == expression) with
  | some (_, name) => pure name
  | none =>
      unless expression.primitiveNatEligible do
        throw s!"Verus backend: expression `{repr expression}` is outside primitive u128 lowering"
      let name ← freshSemanticName "bounded_nat"
      match expression.closedValue? with
      | some integer =>
          let literal ← match natLiteral? integer with
            | some literal => pure literal
            | none =>
                throw s!"Verus backend: bounded unsigned literal `{integer}` exceeds u128"
          emitSemanticLine s!"let {name} = {literal};"
          emitPrimitiveNatBounds format expression name
      | none =>
          match expression with
          | .literal _ => unreachable!
          | .capture _ selector reader _ =>
              let span ← semanticSpanFor format selector
              match reader with
              | .natural =>
                  let natural ← semanticNaturalFor format selector
                  unwrapPrimitiveNat format expression natural name
              | .count =>
                  let natural ← freshSemanticName "bounded_count_source"
                  emitSemanticLine s!"let {natural} = semantic_span_count({span});"
                  unwrapPrimitiveNat format expression natural name
              | .length =>
                  let natural ← freshSemanticName "bounded_length_source"
                  emitSemanticLine s!"let {natural} = SemanticNat::new(
    ({span}.end - {span}.start) as u128,
);"
                  unwrapPrimitiveNat format expression natural name
              | .hexadecimalSequence =>
                  let natural ← freshSemanticName "bounded_hex_source"
                  if (← get).fusedHexSequenceSelectors.contains selector then
                    let summary ← semanticHexSequenceSummaryFor format selector
                    emitSemanticLine s!"let {natural} = {summary}.value;"
                  else
                    emitSemanticLine s!"let {natural} = semantic_hex_sequence_of_span(
    input,
    input_ascii,
    {span},
);"
                  unwrapPrimitiveNat format expression natural name
              | .segments =>
                  let natural ← freshSemanticName "bounded_segments_source"
                  if (← get).fusedHexSequenceSelectors.contains selector then
                    let summary ← semanticHexSequenceSummaryFor format selector
                    emitSemanticLine s!"let {natural} = {summary}.segments;"
                  else
                    emitSemanticLine
                      s!"let {natural} = semantic_segments_of_span(input, input_ascii, {span});"
                  unwrapPrimitiveNat format expression natural name
              | .integer | .hexadecimal | .sign | .prefixSign =>
                  throw s!"Verus backend: reader `{repr reader}` is not primitive unsigned"
          | .add left right | .sub left right | .mul left right =>
              let leftName ← renderPrimitiveNatExpr format left
              let rightName ← renderPrimitiveNatExpr format right
              let leftRange ← primitiveNatRange left
              let rightRange ← primitiveNatRange right
              let range ← primitiveNatRange expression
              let operator := match expression with
                | .add .. => "+"
                | .sub .. => "-"
                | .mul .. => "*"
                | _ => unreachable!
              emitSemanticLine s!"proof {rustLeftBrace}
    assert(({leftRange.lower}int) <= {leftName} as int);
    assert({leftName} as int <= ({leftRange.upper}int));
    assert(({rightRange.lower}int) <= {rightName} as int);
    assert({rightName} as int <= ({rightRange.upper}int));
    assert(({range.lower}int) <= {leftName} as int {operator} {rightName} as int);
    assert({leftName} as int {operator} {rightName} as int <= ({range.upper}int));
{rustRightBrace}"
              emitSemanticLine s!"let {name} = {leftName} {operator} {rightName};"
              emitPrimitiveNatBounds format expression name
          | .iteEq left right thenBranch elseBranch
          | .iteLt left right thenBranch elseBranch
          | .iteLe left right thenBranch elseBranch =>
              let leftName ← renderPrimitiveNatExpr format left
              let rightName ← renderPrimitiveNatExpr format right
              let thenName ← renderPrimitiveNatExpr format thenBranch
              let elseName ← renderPrimitiveNatExpr format elseBranch
              let operator := match expression with
                | .iteEq .. => "=="
                | .iteLt .. => "<"
                | .iteLe .. => "<="
                | _ => unreachable!
              emitSemanticLine s!"let {name} = if {leftName} {operator} {rightName} {rustLeftBrace}
    {thenName}
{rustRightBrace} else {rustLeftBrace}
    {elseName}
{rustRightBrace};"
              emitPrimitiveNatBounds format expression name
          | .iteEmpty selector thenBranch elseBranch =>
              let span ← semanticSpanFor format selector
              let thenName ← renderPrimitiveNatExpr format thenBranch
              let elseName ← renderPrimitiveNatExpr format elseBranch
              emitSemanticLine s!"let {name} =
    if semantic_span_is_empty(input, {span}) {rustLeftBrace}
        {thenName}
    {rustRightBrace} else {rustLeftBrace}
        {elseName}
    {rustRightBrace};"
              emitPrimitiveNatBounds format expression name
          | .pow .. => unreachable!
          | .tdiv .. | .mod .. | .neg .. =>
              throw "Verus backend: signed operation occurs in primitive unsigned lowering"
      modify fun state =>
        { state with
          primitiveNatExpressions := state.primitiveNatExpressions ++ [(expression, name)] }
      pure name

private partial def renderSemanticNatExpr (format : FormatInput) (expression : ExecutableExpr) :
    SemanticRenderM String := do
  let state ← get
  match state.natExpressions.find? (·.1 == expression) with
  | some (_, name) => pure name
  | none =>
      let name ← freshSemanticName "nat_value"
      match expression with
      | .literal integer =>
          let literal ← match natLiteral? integer with
            | some literal => pure literal
            | none => throw s!"Verus backend: unsigned semantic literal `{integer}` exceeds u128"
          emitSemanticLine s!"let {name} = SemanticNat::new({literal});"
      | .capture _ selector reader _ =>
          let span ← semanticSpanFor format selector
          let fuseHexSequence := (← get).fusedHexSequenceSelectors.contains selector
          match reader with
          | .natural =>
              let natural ← semanticNaturalFor format selector
              emitSemanticLine s!"let {name} = {natural};"
          | .count => emitSemanticLine s!"let {name} = semantic_span_count({span});"
          | .length =>
              emitSemanticLine s!"let {name} = SemanticNat::new(
    ({span}.end - {span}.start) as u128,
);"
          | .hexadecimalSequence =>
              if fuseHexSequence then
                let summary ← semanticHexSequenceSummaryFor format selector
                emitSemanticLine s!"let {name} = {summary}.value;"
              else
                emitSemanticLine
                  s!"let {name} = semantic_hex_sequence_of_span(input, input_ascii, {span});"
          | .segments =>
              if fuseHexSequence then
                let summary ← semanticHexSequenceSummaryFor format selector
                emitSemanticLine s!"let {name} = {summary}.segments;"
              else
                emitSemanticLine
                  s!"let {name} = semantic_segments_of_span(input, input_ascii, {span});"
          | .integer | .hexadecimal | .sign | .prefixSign =>
              throw s!"Verus backend: reader `{repr reader}` is not unsigned"
      | expression@(.mul (.literal _) (.pow (.literal _) (.literal _)))
      | expression@(.mul (.pow (.literal _) (.literal _)) (.literal _)) =>
          let integer := expression.closedValue?.getD (-1)
          let literal ← match natLiteral? integer with
            | some literal => pure literal
            | none =>
                throw s!"Verus backend: folded unsigned semantic literal `{integer}` exceeds u128"
          emitSemanticLine s!"let {name} = SemanticNat::new({literal});"
      | .mul factor (.pow (.literal 65536) exponent)
      | .mul (.pow (.literal 65536) exponent) factor =>
          -- A bounded hexadecimal-sequence radix uses one table-selected multiplication.
          let factorName ← renderSemanticNatExpr format factor
          let exponentName ← renderSemanticNatExpr format exponent
          emitSemanticLine (semanticRuntimeSafetyProof format
            s!"{exponentName}.available()")
          emitSemanticLine s!"let {name} = match semantic_nat_mul_pow_65536_fast(
    &{factorName},
    &{exponentName},
) {rustLeftBrace}
    Some(value) => value,
    None => return None,
{rustRightBrace};"
      | .mul factor (.pow base exponent) =>
          let factorName ← renderSemanticNatExpr format factor
          let baseName ← renderSemanticNatExpr format base
          let exponentName ← renderSemanticNatExpr format exponent
          emitSemanticLine (semanticRuntimeSafetyProof format
            s!"{exponentName}.available()")
          emitSemanticLine s!"let {name} = match semantic_nat_mul_pow_fast(
    &{factorName},
    &{baseName},
    &{exponentName},
) {rustLeftBrace}
    Some(value) => value,
    None => return None,
{rustRightBrace};"
      | .mul (.pow base exponent) factor =>
          let factorName ← renderSemanticNatExpr format factor
          let baseName ← renderSemanticNatExpr format base
          let exponentName ← renderSemanticNatExpr format exponent
          emitSemanticLine (semanticRuntimeSafetyProof format
            s!"{exponentName}.available()")
          emitSemanticLine s!"let {name} = match semantic_nat_mul_pow_fast(
    &{factorName},
    &{baseName},
    &{exponentName},
) {rustLeftBrace}
    Some(value) => value,
    None => return None,
{rustRightBrace};"
      | .add left right | .mul left right =>
          let leftName ← renderSemanticNatExpr format left
          let rightName ← renderSemanticNatExpr format right
          let method := if let .add .. := expression then "add" else "mul"
          emitSemanticLine s!"let {name} = {leftName}.{method}(&{rightName});"
      | .sub left right =>
          let leftName ← renderSemanticNatExpr format left
          let rightName ← renderSemanticNatExpr format right
          emitSemanticLine (semanticRuntimeSafetyProof format
            s!"{leftName}.available() && {rightName}.available() && {leftName}@ >= {rightName}@")
          emitSemanticLine s!"let {name} = match {leftName}.checked_sub(&{rightName}) {rustLeftBrace}
    Some(value) => value,
    None => return None,
{rustRightBrace};"
      | expression@(.pow (.literal _) (.literal _)) =>
          let integer := expression.closedValue?.getD (-1)
          let literal ← match natLiteral? integer with
            | some literal => pure literal
            | none =>
                throw s!"Verus backend: folded unsigned semantic literal `{integer}` exceeds u128"
          emitSemanticLine s!"let {name} = SemanticNat::new({literal});"
      | .pow base exponent =>
          let baseName ← renderSemanticNatExpr format base
          let exponentName ← renderSemanticNatExpr format exponent
          emitSemanticLine (semanticRuntimeSafetyProof format
            s!"{exponentName}.available()")
          emitSemanticLine s!"let {name} = match semantic_nat_pow(&{baseName}, &{exponentName}) {rustLeftBrace}
    Some(value) => value,
    None => return None,
{rustRightBrace};"
      | .iteEq left right thenBranch elseBranch
      | .iteLt left right thenBranch elseBranch
      | .iteLe left right thenBranch elseBranch =>
          let leftName ← renderSemanticNatExpr format left
          let rightName ← renderSemanticNatExpr format right
          let thenName ← renderSemanticNatExpr format thenBranch
          let elseName ← renderSemanticNatExpr format elseBranch
          let condition ← freshSemanticName "condition"
          let method := match expression with
            | .iteEq .. => "eq"
            | .iteLt .. => "lt"
            | .iteLe .. => "le"
            | _ => unreachable!
          emitSemanticLine (semanticRuntimeSafetyProof format
            s!"{leftName}.available() && {rightName}.available()")
          emitSemanticLine (semanticMatchBool condition
            s!"{leftName}.{method}(&{rightName})")
          emitSemanticLine s!"let {name} = if {condition} {rustLeftBrace}
    {thenName}
{rustRightBrace} else {rustLeftBrace}
    {elseName}
{rustRightBrace};"
      | .iteEmpty selector thenBranch elseBranch =>
          let span ← semanticSpanFor format selector
          let base ← get
          let (thenName, thenState) ←
            (renderSemanticNatExpr format thenBranch).run { base with lines := [] }
          let (elseName, elseState) ←
            (renderSemanticNatExpr format elseBranch).run
              { base with next := thenState.next, lines := [] }
          set { base with next := elseState.next }
          let thenLines := String.intercalate "\n" thenState.lines
          let elseLines := String.intercalate "\n" elseState.lines
          emitSemanticLine s!"let {name} =
    if semantic_span_is_empty(input, {span}) {rustLeftBrace}
{indentText 2 thenLines}
        {thenName}
    {rustRightBrace} else {rustLeftBrace}
{indentText 2 elseLines}
        {elseName}
    {rustRightBrace};"
      | .tdiv .. | .mod .. | .neg .. =>
          throw "Verus backend: signed operation occurs in an unsigned IP expression"
      emitSemanticLine (semanticRuntimeSafetyProof format s!"{name}.available()")
      modify fun state =>
        { state with natExpressions := state.natExpressions ++ [(expression, name)] }
      pure name

private partial def renderSemanticConstraint (format : FormatInput) (useNat : Bool)
    (constraint : ExecutableConstraint) : SemanticRenderM String := do
  let name ← freshSemanticName "constraint"
  match constraint with
  | .noLeadingZero selector =>
      let span ← semanticSpanFor format selector
      emitSemanticLine s!"let {name} = semantic_no_leading_zero(
    input,
    input_ascii,
    {span},
);"
  | .card operation minimum selectors =>
      let spans ← selectors.mapM (semanticSpanFor format)
      let terms := spans.map fun span =>
        s!"if semantic_span_is_present({span}) {rustLeftBrace} 1usize {rustRightBrace} \
          else {rustLeftBrace} 0usize {rustRightBrace}"
      let present := if terms.isEmpty then "0usize" else String.intercalate " + " terms
      let comparison := match operation with
        | .atLeast => s!"{minimum}usize <= ({present})"
        | .atMost => s!"({present}) <= {minimum}usize"
        | .exactlyK => s!"({present}) == {minimum}usize"
      emitSemanticLine s!"let {name} = {comparison};"
  | .le (.literal lower) right =>
      if useNat && lower ≤ 0 then
        let rightName ← renderSemanticNatExpr format right
        emitSemanticLine s!"let {name} = true;"
        emitSemanticLine s!"proof {rustLeftBrace}
    assert(0 <= {rightName}@ as int);
{rustRightBrace}"
      else
        let leftName ← if useNat then renderSemanticNatExpr format (.literal lower)
          else renderSemanticIntExpr format (.literal lower)
        let rightName ← if useNat then renderSemanticNatExpr format right
          else renderSemanticIntExpr format right
        emitSemanticLine (semanticRuntimeSafetyProof format
          s!"{leftName}.available() && {rightName}.available()")
        emitSemanticLine (semanticMatchBool name s!"{leftName}.le(&{rightName})")
  | .le left right | .lt left right | .eq left right =>
      let leftName ← if useNat then renderSemanticNatExpr format left
        else renderSemanticIntExpr format left
      let rightName ← if useNat then renderSemanticNatExpr format right
        else renderSemanticIntExpr format right
      let method := match constraint with
        | .le .. => "le"
        | .lt .. => "lt"
        | .eq .. => "eq"
        | _ => unreachable!
      emitSemanticLine (semanticRuntimeSafetyProof format
        s!"{leftName}.available() && {rightName}.available()")
      emitSemanticLine (semanticMatchBool name s!"{leftName}.{method}(&{rightName})")
  | .and left right =>
      let leftName ← renderSemanticConstraint format useNat left
      let rightName ← renderSemanticConstraint format useNat right
      emitSemanticLine s!"let {name} = {leftName} && {rightName};"
  | .stringEq .. =>
      throw "Verus backend: executable string equality constraints are not implemented"
  pure name

private partial def renderPrimitiveNatConstraint (format : FormatInput)
    (constraint : ExecutableConstraint) : SemanticRenderM String := do
  let name ← freshSemanticName "bounded_constraint"
  match constraint with
  | .noLeadingZero selector =>
      let span ← semanticSpanFor format selector
      emitSemanticLine s!"let {name} = semantic_no_leading_zero(
    input,
    input_ascii,
    {span},
);"
  | .card operation minimum selectors =>
      let spans ← selectors.mapM (semanticSpanFor format)
      let terms := spans.map fun span =>
        s!"if semantic_span_is_present({span}) {rustLeftBrace} 1usize {rustRightBrace} \
          else {rustLeftBrace} 0usize {rustRightBrace}"
      let present := if terms.isEmpty then "0usize" else String.intercalate " + " terms
      let comparison := match operation with
        | .atLeast => s!"{minimum}usize <= ({present})"
        | .atMost => s!"({present}) <= {minimum}usize"
        | .exactlyK => s!"({present}) == {minimum}usize"
      emitSemanticLine s!"let {name} = {comparison};"
  | .le (.literal lower) right =>
      if lower ≤ 0 then
        let rightName ← renderPrimitiveNatExpr format right
        emitSemanticLine s!"let {name} = true;"
        emitSemanticLine s!"proof {rustLeftBrace}
    assert(0 <= {rightName} as int);
{rustRightBrace}"
      else
        let leftName ← renderPrimitiveNatExpr format (.literal lower)
        let rightName ← renderPrimitiveNatExpr format right
        emitSemanticLine s!"let {name} = {leftName} <= {rightName};"
  | .le left right | .lt left right | .eq left right =>
      let leftName ← renderPrimitiveNatExpr format left
      let rightName ← renderPrimitiveNatExpr format right
      let operator := match constraint with
        | .le .. => "<="
        | .lt .. => "<"
        | .eq .. => "=="
        | _ => unreachable!
      emitSemanticLine s!"let {name} = {leftName} {operator} {rightName};"
  | .and left right =>
      let leftName ← renderPrimitiveNatConstraint format left
      let rightName ← renderPrimitiveNatConstraint format right
      emitSemanticLine s!"let {name} = {leftName} && {rightName};"
  | .stringEq .. =>
      throw "Verus backend: executable string equality constraints are not implemented"
  pure name

private def renderConstraintChecks (format : FormatInput) (useNat : Bool)
    (constraints : List ExecutableConstraint) : SemanticRenderM Unit := do
  for constraint in constraints do
    let name ← renderSemanticConstraint format useNat constraint
    emitSemanticLine s!"if !{name} {rustLeftBrace}
    return None;
{rustRightBrace}"

private def renderPrimitiveConstraintChecks (format : FormatInput)
    (constraints : List ExecutableConstraint) : SemanticRenderM Unit := do
  for constraint in constraints do
    let name ← renderPrimitiveNatConstraint format constraint
    emitSemanticLine s!"if !{name} {rustLeftBrace}
    return None;
{rustRightBrace}"

/-- A packed IP value `address * radix + prefix` is bounded once the generated parser has
    independently established `address < 2^bits` and `prefix < radix`. Keep the source-level
    constraint in the readable specification, but avoid reconstructing the packed integer at
    runtime when its declared interval is exactly that implied range. -/
private def redundantPackedIpConstraint (addressBits radix : Nat)
    (addressExpr prefixExpr : ExecutableExpr) : ExecutableConstraint → Bool
  | .and (.le (.literal lower) lowerExpr) (.le upperExpr upper) =>
      let packed :=
        .add (.mul addressExpr (.literal (Int.ofNat radix))) prefixExpr
      let upperBound :=
        ((2 : Int) ^ addressBits) * Int.ofNat radix - 1
      lower ≤ 0 &&
        lowerExpr == packed &&
        upperExpr == packed &&
        upper.closedValue? == some upperBound
  | _ => false

private def renderSemanticCaptureIndex (format : FormatInput)
    (spans : List (CaptureSelector × String)) (captureCapacity : Nat) : String :=
  let entries := List.zip (List.range spans.length) (spans.map Prod.fst)
  let typeName := semanticCaptureIndexType format
  let functionName := semanticCaptureIndexFunction format
  let fields := entries.map fun (index, _) =>
    s!"    {semanticCaptureIndexField index}: Option<RuntimeCapture>,"
  let ensures := entries.map fun (index, selector) =>
    "        result." ++ semanticCaptureIndexField index ++
      " == first_runtime_capture(\n" ++
      "            search_candidate_of(state.deep_view()).captures,\n" ++
      "            " ++ renderCaptureSelector selector ++
      "\n        ),"
  let locals := entries.map fun (index, _) =>
    s!"    let mut indexed_capture_{index} = None;"
  let updateBranches := entries.map fun (index, selector) =>
    "                " ++ renderCaptureSelector selector ++ " => {\n" ++
      "                    if indexed_capture_" ++ toString index ++ ".is_none() {\n" ++
      "                        indexed_capture_" ++ toString index ++
        " = Some(capture);\n" ++
      "                    }\n" ++
      "                },"
  let updates :=
    "        match slot {\n" ++
      "            Some(capture) => match capture.key {\n" ++
      String.intercalate "\n" updateBranches ++ "\n" ++
      "                _ => {},\n" ++
      "            },\n" ++
      "            None => {},\n" ++
      "        }"
  let initialProofs := entries.map fun (index, selector) =>
    "        assert(indexed_capture_" ++ toString index ++
      " == search_first_capture_before(\n" ++
      "            state.captures@,\n" ++
      "            " ++ renderCaptureSelector selector ++ ",\n" ++
      "            0,\n" ++
      "        ));"
  let steps := List.range captureCapacity |>.map fun slotIndex =>
    let nextIndex := slotIndex + 1
    let stepProofs := entries.map fun (index, selector) =>
      "            assert(indexed_capture_" ++ toString index ++
        " == search_first_capture_before(\n" ++
        "                state.captures@,\n" ++
        "                " ++ renderCaptureSelector selector ++ ",\n" ++
        "                " ++ toString nextIndex ++ ",\n" ++
        "            ));"
    "    if " ++ toString slotIndex ++ "usize < state.captures.len() {\n" ++
      "        let slot = state.captures.get(" ++ toString slotIndex ++ "usize);\n" ++
      updates ++ "\n" ++
      "        proof {\n" ++
      "            reveal_with_fuel(search_first_capture_before, 1);\n" ++
      String.intercalate "\n" stepProofs ++ "\n" ++
      "        }\n" ++
      "    }"
  let finalCases := (List.range (captureCapacity + 1)).map fun length =>
    let branch := if length == 0 then "if" else "else if"
    let assertions := entries.map fun (index, selector) =>
      "            assert(indexed_capture_" ++ toString index ++
        " == search_first_capture_before(\n" ++
        "                state.captures@,\n" ++
        "                " ++ renderCaptureSelector selector ++ ",\n" ++
        "                state.captures@.len(),\n" ++
        "            ));"
    "        " ++ branch ++ " state.captures@.len() == " ++ toString length ++ "usize {\n" ++
      String.intercalate "\n" assertions ++ "\n" ++
      "        }"
  let proofs := entries.map fun (_, selector) =>
    "        search_first_capture_before_matches(\n" ++
      "            state.captures@,\n" ++
      "            " ++ renderCaptureSelector selector ++ ",\n" ++
      "            state.captures@.len(),\n" ++
      "        );"
  let results := entries.map fun (index, _) =>
    s!"        {semanticCaptureIndexField index}: indexed_capture_{index},"
  s!"#[derive(Copy, Clone)]
struct {typeName} {rustLeftBrace}
{String.intercalate "\n" fields}
{rustRightBrace}

#[inline(always)]
#[verifier::rlimit(1000)]
fn {functionName}(
    state: &SearchState,
) -> (result: {typeName})
    requires
        state.storage_well_formed(),
    ensures
{String.intercalate "\n" ensures}
{rustLeftBrace}
{String.intercalate "\n" locals}
    proof {rustLeftBrace}
        reveal_with_fuel(search_first_capture_before, 1);
{String.intercalate "\n" initialProofs}
    {rustRightBrace}
{String.intercalate "\n" steps}
    proof {rustLeftBrace}
        assert(state.captures@.len() <= {captureCapacity}usize);
{String.intercalate " " finalCases}
        reveal(search_candidate_of);
        reveal(search_captures);
{String.intercalate "\n" proofs}
    {rustRightBrace}
    {typeName} {rustLeftBrace}
{String.intercalate "\n" results}
    {rustRightBrace}
{rustRightBrace}
"

private def renderRuntimeSemanticParser (format : FormatInput)
    (plan : ExecutableSemanticPlan) (searchState : Bool := false)
    (captureCapacity : Nat := 0) :
    Except String String := do
  let formatPrefix := snakeCase format.name
  let candidateFunction :=
    functionName format.name (if searchState then "scan_state" else "parse_candidate")
  let selectedCandidateFunction := functionName format.name "search_parse_candidate"
  let parseFunction := functionName format.name "parse"
  let evaluateFunction := functionName format.name "evaluate_candidate"
  let candidateType := if searchState then "SearchState" else "Candidate"
  let leftBrace := "{"
  let rightBrace := "}"
  let candidateView :=
    if searchState then "search_candidate_of(candidate.deep_view())"
    else "candidate.deep_view()"
  let candidateRequires :=
    if searchState then
      "    requires\n" ++
        "        input_length == input@.len(),\n" ++
        "        input_ascii == input.is_ascii(),\n" ++
        "        candidate.storage_well_formed(),\n"
        ++ "        candidate.semantic_cache.matches_input(input@),\n"
    else ""
  let evaluatorParameters :=
    if searchState then
      "    input_length: usize,\n" ++
        "    input_ascii: bool,\n"
    else ""
  let evaluatorInputSetup :=
    if searchState then ""
    else
      "    let input_ascii = input.is_ascii();\n" ++
        "    let input_length = search_input_length(input, input_ascii);\n"
  let parseInputSetup :=
    if searchState then
      "    let input_ascii = input.is_ascii();\n" ++
        "    let input_length = search_input_length(input, input_ascii);\n"
    else ""
  let candidateCall :=
    if searchState then s!"{candidateFunction}(input, input_length, input_ascii)"
    else s!"{candidateFunction}(input)"
  let evaluateCall :=
    if searchState then
      s!"{evaluateFunction}(input, input_length, input_ascii, &candidate)"
    else
      s!"{evaluateFunction}(input, &candidate)"
  let wfName := formatPrefix ++ "_candidate_wf_constraints"
  let constraintsName := formatPrefix ++ "_candidate_constraints"
  let validName := formatPrefix ++ "_candidate_is_valid"
  let valueName := formatPrefix ++ "_candidate_value"
  let safeName := formatPrefix ++ "_candidate_runtime_safe"
  let primitiveIp :=
    match plan with
    | .ip _ _ _ addressExpr prefixExpr wfConstraints valueConstraints =>
        addressExpr.primitiveNatEligible && prefixExpr.primitiveNatEligible &&
          (wfConstraints ++ valueConstraints).all ExecutableConstraint.primitiveNatEligible
    | .int64 .. => false
  let initial : SemanticRenderState :=
    { searchState
      semanticCacheEntries := plan.semanticCacheEntries
      fusedHexSequenceSelectors := plan.fusedHexSequenceSelectors }
  let action : SemanticRenderM (String × String) :=
    do
      for selector in plan.captureSelectors do
        let _ ← semanticSpanFor format selector
      for selector in plan.fusedHexSequenceSelectors do
        let _ ← semanticHexSequenceSummaryFor format selector
      match plan with
      | .int64 expression wfConstraints valueConstraints => do
        for shared in plan.repeatedPrimitiveCaptureExpressions do
          let _ ← renderSemanticIntExpr format shared
        let parsedValue ← renderSemanticIntExpr format expression
        renderConstraintChecks format false wfConstraints
        renderConstraintChecks format false valueConstraints
        pure (parsedValue, "")
      | .ip _ addressBits radix addressExpr prefixExpr wfConstraints valueConstraints => do
        let filteredValueConstraints :=
          valueConstraints.filter fun constraint =>
            !redundantPackedIpConstraint addressBits radix addressExpr prefixExpr constraint
        if primitiveIp then
          for shared in plan.repeatedPrimitiveCaptureExpressions do
            if shared.primitiveNatEligible then
              let _ ← renderPrimitiveNatExpr format shared
          let address ← renderPrimitiveNatExpr format addressExpr
          let prefixValue ← renderPrimitiveNatExpr format prefixExpr
          renderPrimitiveConstraintChecks format wfConstraints
          renderPrimitiveConstraintChecks format filteredValueConstraints
          if addressBits < 128 then
            let addressBound := (2 : Nat) ^ addressBits
            emitSemanticLine s!"if {address} >= {addressBound}u128 {rustLeftBrace}
    return None;
{rustRightBrace}"
          else if addressBits > 128 then
            throw s!"Verus backend: IP address width `{addressBits}` exceeds u128"
          pure (address, prefixValue)
        else
          for shared in plan.repeatedPrimitiveCaptureExpressions do
            let _ ← renderSemanticNatExpr format shared
          let address ← renderSemanticNatExpr format addressExpr
          let prefixValue ← renderSemanticNatExpr format prefixExpr
          renderConstraintChecks format true wfConstraints
          renderConstraintChecks format true filteredValueConstraints
          if addressBits < 128 then
            let addressBound ← renderSemanticNatExpr format
              (.pow (.literal 2) (.literal (Int.ofNat addressBits)))
            let addressOk ← freshSemanticName "address_ok"
            emitSemanticLine (semanticMatchBool addressOk s!"{address}.lt(&{addressBound})")
            emitSemanticLine
              s!"if !{addressOk} {rustLeftBrace} return None; {rustRightBrace}"
          else if addressBits > 128 then
            throw s!"Verus backend: IP address width `{addressBits}` exceeds u128"
          pure (address, prefixValue)
  let (resultNames, state) ← action.run initial
  let (firstResult, secondResult) := resultNames
  let lines := String.intercalate "\n" state.lines
  let captureIndex :=
    if searchState then renderSemanticCaptureIndex format state.spans captureCapacity else ""
  let captureIndexInit :=
    if searchState then
      s!"    let capture_index = {semanticCaptureIndexFunction format}(candidate);"
    else ""
  match plan with
  | .int64 _ _ _ =>
      pure s!"
{captureIndex}
#[inline(always)]
#[verifier::rlimit(200)]
fn {evaluateFunction}(
    input: &str,
{evaluatorParameters}\
    candidate: &{candidateType},
) -> (result: Option<i64>)
{candidateRequires}\
    ensures
        match result {leftBrace}
            Some(value) =>
                {validName}(input@, {candidateView})
                    && {valueName}(input@, {candidateView})
                        == value as int,
            None =>
                !{safeName}(input@, {candidateView})
                    || !{validName}(input@, {candidateView}),
        {rightBrace},
{leftBrace}
{evaluatorInputSetup}\
    let ghost candidate_view = {candidateView};
{captureIndexInit}
    proof {leftBrace}
        reveal({wfName});
        reveal({constraintsName});
        reveal({validName});
        reveal({safeName});
    {rightBrace}
{indentText 1 lines}
    {semanticRuntimeSafetyProof format s!"{firstResult}.available()"}
    let value = match {firstResult}.to_i64_option() {leftBrace}
        Some(value) => value,
        None => return None,
    {rightBrace};
    proof {leftBrace}
        reveal({valueName});
        assert({validName}(input@, candidate_view));
        assert({valueName}(input@, candidate_view) == value as int);
    {rightBrace}
    Some(value)
{rightBrace}

#[inline(always)]
pub fn {parseFunction}(input: &str) -> (result: Option<i64>)
    ensures
        match result {leftBrace}
            Some(value) =>
                match {selectedCandidateFunction}(input@) {leftBrace}
                    Some(candidate) =>
                        {validName}(input@, candidate)
                            && {valueName}(input@, candidate) == value as int,
                    None => false,
                {rightBrace},
            None =>
                match {selectedCandidateFunction}(input@) {leftBrace}
                    Some(candidate) =>
                        !{safeName}(input@, candidate)
                            || !{validName}(input@, candidate),
                    None => true,
                {rightBrace},
        {rightBrace},
{leftBrace}
{parseInputSetup}\
    let candidate = match {candidateCall} {leftBrace}
        Some(candidate) => candidate,
        None => return None,
    {rightBrace};
    let value = match {evaluateCall} {leftBrace}
        Some(value) => value,
        None => return None,
    {rightBrace};
    proof {leftBrace}
        assert({selectedCandidateFunction}(input@) == Some({candidateView}));
        assert({validName}(input@, {candidateView}));
        assert({valueName}(input@, {candidateView}) == value as int);
    {rightBrace}
    Some(value)
{rightBrace}
"
  | .ip family _ radix _ _ _ _ =>
      let resultType := typeName format.name ++ "ParseResult"
      let unpackResults :=
        if primitiveIp then
          s!"    let address = {firstResult};
    let prefix_u128 = {secondResult};"
        else
          s!"    let address = match {firstResult}.to_option() {leftBrace}
        Some(value) => value,
        None => return None,
    {rightBrace};
    let prefix_u128 = match {secondResult}.to_option() {leftBrace}
        Some(value) => value,
        None => return None,
    {rightBrace};"
      pure s!"
{captureIndex}
#[derive(Structural, Copy, Clone, PartialEq, Eq, Debug)]
pub struct {resultType} {leftBrace}
    pub family: u8,
    pub address: u128,
    pub prefix: u8,
{rightBrace}

#[inline(always)]
#[verifier::rlimit(100)]
fn {evaluateFunction}(
    input: &str,
{evaluatorParameters}\
    candidate: &{candidateType},
) -> (result: Option<{resultType}>)
{candidateRequires}\
    ensures
        match result {leftBrace}
            Some(value) =>
                {validName}(input@, {candidateView})
                    && {formatPrefix}_candidate_address(input@, {candidateView})
                        == value.address as int
                    && {formatPrefix}_candidate_prefix(input@, {candidateView})
                        == value.prefix as int
                    && value.family as int == {family},
            None =>
                !{safeName}(input@, {candidateView})
                    || !{validName}(input@, {candidateView}),
        {rightBrace},
{leftBrace}
{evaluatorInputSetup}\
    let ghost candidate_view = {candidateView};
{captureIndexInit}
    proof {leftBrace}
        reveal({wfName});
        reveal({constraintsName});
        reveal({validName});
        reveal({safeName});
{rightBrace}
{indentText 1 lines}
{unpackResults}
    if prefix_u128 >= {radix}u128 || prefix_u128 > u8::MAX as u128 {leftBrace}
        return None;
    {rightBrace}
    let prefix = prefix_u128 as u8;
    let value = {resultType} {leftBrace}
        family: {family}u8,
        address,
        prefix,
    {rightBrace};
    proof {leftBrace}
        reveal({formatPrefix}_candidate_address);
        reveal({formatPrefix}_candidate_prefix);
        assert({validName}(input@, candidate_view));
        assert({formatPrefix}_candidate_address(input@, candidate_view)
            == address as int);
        assert({formatPrefix}_candidate_prefix(input@, candidate_view)
            == prefix as int);
    {rightBrace}
    Some(value)
{rightBrace}

#[inline(always)]
pub fn {parseFunction}(input: &str) -> (result: Option<{resultType}>)
    ensures
        match result {leftBrace}
            Some(value) =>
                match {selectedCandidateFunction}(input@) {leftBrace}
                    Some(candidate) =>
                        {validName}(input@, candidate)
                            && {formatPrefix}_candidate_address(input@, candidate)
                                == value.address as int
                            && {formatPrefix}_candidate_prefix(input@, candidate)
                                == value.prefix as int
                            && value.family as int == {family},
                    None => false,
                {rightBrace},
            None =>
                match {selectedCandidateFunction}(input@) {leftBrace}
                    Some(candidate) =>
                        !{safeName}(input@, candidate)
                            || !{validName}(input@, candidate),
                    None => true,
                {rightBrace},
        {rightBrace},
{leftBrace}
{parseInputSetup}\
    let candidate = match {candidateCall} {leftBrace}
        Some(candidate) => candidate,
        None => return None,
    {rightBrace};
    let value = match {evaluateCall} {leftBrace}
        Some(value) => value,
        None => return None,
    {rightBrace};
    proof {leftBrace}
        assert({selectedCandidateFunction}(input@) == Some({candidateView}));
        assert({validName}(input@, {candidateView}));
        assert({formatPrefix}_candidate_address(input@, {candidateView})
            == value.address as int);
        assert({formatPrefix}_candidate_prefix(input@, {candidateView})
            == value.prefix as int);
        assert(value.family as int == {family});
    {rightBrace}
    Some(value)
{rightBrace}
"

private def instantiateRuntimeParser (format : FormatInput) (grammar : FlatGrammar)
    (semanticPlan? : Option ExecutableSemanticPlan) (prevalidated : Bool := false) :
    Except String String := do
  let function := functionName format.name "parse_candidate"
  let semanticRuntime := (semanticPlan?.map fun plan =>
    plan.runtimeSemanticBase ++ "\n\n" ++ renderRuntimeSemanticSupport plan).getD ""
  let semanticParser ← match semanticPlan? with
    | some plan => renderRuntimeSemanticParser format plan
    | none => pure ""
  let grammarSymbols := renderArray "        " (grammar.symbols.map renderGrammarSymbol)
  let grammarItems := renderArray "        " (grammar.items.map renderGrammarItem)
  let grammarAlternatives :=
    renderArray "        " (grammar.alternatives.map renderGrammarAlternative)
  let grammarProductions :=
    renderArray "        " (grammar.productions.map renderGrammarProduction)
  let leftBrace := "{"
  let rightBrace := "}"
  let parserDescription :=
    if prevalidated then
      "Proof-carrying complete search parser with a generated static grammar-table certificate."
    else
      "Proof-carrying complete search parser with runtime grammar-table validation."
  let executionDescription :=
    if prevalidated then
      "The generated proof block certifies every table index and termination invariant once. \
      Execution then runs the complete ordered grammar search, scanning each token prefix once, \
      without revalidating the table."
    else
      "The checked runtime validates every table index and termination invariant before \
      executing the complete ordered grammar search."
  pure s!"// Generated by Triptych from `triptych {format.name}`.
// {parserDescription}
// This file is regenerated; it contains no external parser or manually supplied parser proof.
{productionTableComment grammar}

{runtimeParserTemplate}
verus! {leftBrace}

{semanticRuntime}

/// Parse one complete input using the source grammar emitted from `triptych {format.name}`.
///
/// {executionDescription}
#[inline(always)]
pub fn {function}(input: &str) -> (result: Option<Candidate>)
    ensures
        match result {leftBrace}
            Some(candidate) => candidate.end == input@.len(),
            None => true,
        {rightBrace},
{leftBrace}
{renderSeparatorProofs grammar}
    let grammar_symbols: [GrammarSymbol; {grammar.symbols.length}] = {grammarSymbols};
    let grammar_items: [GrammarItem; {grammar.items.length}] = {grammarItems};
    let grammar_alternatives: [GrammarAlternative; {grammar.alternatives.length}] =
        {grammarAlternatives};
    let grammar_productions: [GrammarProduction; {grammar.productions.length}] =
        {grammarProductions};
    let source_grammar = GrammarInput {leftBrace}
        start: {grammar.start},
        symbols: &grammar_symbols,
        items: &grammar_items,
        alternatives: &grammar_alternatives,
        productions: &grammar_productions,
    {rightBrace};

{if prevalidated then renderStaticGrammarProof grammar else ""}
    {if prevalidated then "parse_grammar_candidate" else "parse_checked_grammar_candidate"}(
        &source_grammar,
        input,
    )
{rightBrace}

{semanticPlan?.map (renderRuntimeSemanticSpec format) |>.getD ""}

{semanticParser}

{rightBrace} // verus!
"

/-- Generate the parser source used inside `emitCertifiedRust`. Keeping this private prevents
    callers from treating executable Rust as a separate, potentially uncertified artifact. -/
private def emitCertifiedParserSource (format : FormatInput) (prevalidated : Bool := false) :
    Except String String := do
  let grammar ← compileFlatGrammar format.grammar
  let executablePlan? ←
    match compileSemanticPlan format.valueExpr format.wfConstraints format.valueConstraints
        format.ofSpec with
    | .ok semanticPlan =>
        match compileExecutableSemanticPlan grammar semanticPlan with
        | .ok executablePlan => pure (some executablePlan)
        | .error _ => pure none
    | .error _ => pure none
  match executablePlan? with
  | some executablePlan =>
      match instantiateRuntimeParser format grammar (some executablePlan) prevalidated with
      | .ok source => pure source
      | .error _ => instantiateRuntimeParser format grammar none prevalidated
  | none => instantiateRuntimeParser format grammar none prevalidated

/-! ## Grammar-specialized direct parser -/

/-- Verified scanning and sequence primitives shared by specialized plans. The template
    deliberately leaves its `verus!` block open so generated plan and semantic declarations are
    checked in the same module. -/
private def directParserTemplate : String :=
  include_str "Verus/DirectParser.rs.in"

private def checkedSemanticTemplate : String :=
  include_str "Verus/CheckedSemantic.rs.in"

-- Shared proof support, fixed-capacity search state, byte-fast dispatch, fused captures, and
-- scanner-carried private semantic summaries.
private def searchMachineParserTemplate : String :=
  include_str "Verus/SearchMachineParser.rs.in"

private structure VerusDirectRepeatItem where
  token : TokClass
  length : LenSpec
  keys : List String
  deriving Repr, Inhabited, DecidableEq, BEq

private inductive VerusSearchCode where
  | accept
  | fail
  | literal (text : String) (next : VerusSearchCode)
  | stringLiteral (next : VerusSearchCode)
  | tokenRun (token : TokClass) (length : LenSpec) (next : VerusSearchCode)
  | greedyTokenRun (token : TokClass) (length : LenSpec) (next : VerusSearchCode)
  | capturedTokenRun (item : VerusDirectRepeatItem) (next : VerusSearchCode)
  | save (next : VerusSearchCode)
  | capture (keys : List String) (next : VerusSearchCode)
  | countCapture (key : String) (itemCount : Nat) (next : VerusSearchCode)
  | directRepetition (separator : String) (item : VerusDirectRepeatItem)
      (lower upper : Nat) (countKey : String) (next : VerusSearchCode)
  | choice (first second : VerusSearchCode)
  | dispatch (literal : String) (present absent : VerusSearchCode)
  deriving Repr, Inhabited, DecidableEq, BEq

private def VerusSearchCode.plugAccept (code continuation : VerusSearchCode) :
    VerusSearchCode :=
  match code with
  | .accept => continuation
  | .fail => .fail
  | .literal text next => .literal text (plugAccept next continuation)
  | .stringLiteral next => .stringLiteral (plugAccept next continuation)
  | .tokenRun token length next =>
      .tokenRun token length (plugAccept next continuation)
  | .greedyTokenRun token length next =>
      .greedyTokenRun token length (plugAccept next continuation)
  | .capturedTokenRun item next =>
      .capturedTokenRun item (plugAccept next continuation)
  | .save next => .save (plugAccept next continuation)
  | .capture keys next => .capture keys (plugAccept next continuation)
  | .countCapture key itemCount next =>
      .countCapture key itemCount (plugAccept next continuation)
  | .directRepetition separator item lower upper countKey next =>
      .directRepetition separator item lower upper countKey
        (plugAccept next continuation)
  | .choice first second =>
      .choice (plugAccept first continuation) (plugAccept second continuation)
  | .dispatch needle present absent =>
      .dispatch needle
        (plugAccept present continuation)
        (plugAccept absent continuation)

/-- The first character required by every successful path through a generated Verus state. -/
private def VerusSearchCode.requiredHead? : VerusSearchCode → Option Char
  | .literal text next =>
      match text.toList with
      | character :: _ => some character
      | [] => next.requiredHead?
  | .save next
  | .capture _ next
  | .countCapture _ _ next => next.requiredHead?
  | .capturedTokenRun _ _ => none
  | .directRepetition _ _ _ _ _ _ => none
  | .choice first second =>
      match first.requiredHead?, second.requiredHead? with
      | some firstCharacter, some secondCharacter =>
          if firstCharacter == secondCharacter then some firstCharacter else none
      | _, _ => none
  | .dispatch _ present absent =>
      match present.requiredHead?, absent.requiredHead? with
      | some presentCharacter, some absentCharacter =>
          if presentCharacter == absentCharacter then some presentCharacter else none
      | _, _ => none
  | _ => none

/-- A two-character literal consumed on every successful path. The analysis is
    intentionally conservative: alternatives report a literal only when both arms report the same
    one. -/
private def VerusSearchCode.requiredLongLiteral? : VerusSearchCode → Option String
  | .accept
  | .fail => none
  | .literal text next =>
      if text.toList.length == 2 then some text else next.requiredLongLiteral?
  | .stringLiteral next
  | .tokenRun _ _ next
  | .greedyTokenRun _ _ next
  | .capturedTokenRun _ next
  | .save next
  | .capture _ next
  | .countCapture _ _ next
  | .directRepetition _ _ _ _ _ next => next.requiredLongLiteral?
  | .choice first second
  | .dispatch _ first second =>
      match first.requiredLongLiteral?, second.requiredLongLiteral? with
      | some firstLiteral, some secondLiteral =>
          if firstLiteral == secondLiteral then some firstLiteral else none
      | _, _ => none

/-- Replace a source-ordered choice by one literal-guided dispatch when the second arm must
    consume a distinctive multi-character literal. These machines come only from grammars with a
    `staticUnique` certificate, so trying the distinguished arm first cannot change a successful
    complete capture result. If the literal is absent, the distinguished arm cannot succeed and is
    skipped entirely. -/
private def VerusSearchCode.dispatchRequiredLiterals : VerusSearchCode → VerusSearchCode
  | .accept => .accept
  | .fail => .fail
  | .literal text next => .literal text next.dispatchRequiredLiterals
  | .stringLiteral next => .stringLiteral next.dispatchRequiredLiterals
  | .tokenRun token length next =>
      .tokenRun token length next.dispatchRequiredLiterals
  | .greedyTokenRun token length next =>
      .greedyTokenRun token length next.dispatchRequiredLiterals
  | .capturedTokenRun item next =>
      .capturedTokenRun item next.dispatchRequiredLiterals
  | .save next => .save next.dispatchRequiredLiterals
  | .capture keys next => .capture keys next.dispatchRequiredLiterals
  | .countCapture key itemCount next =>
      .countCapture key itemCount next.dispatchRequiredLiterals
  | .directRepetition separator item lower upper countKey next =>
      .directRepetition separator item lower upper countKey
        next.dispatchRequiredLiterals
  | .choice first second =>
      let dispatchedFirst := first.dispatchRequiredLiterals
      let dispatchedSecond := second.dispatchRequiredLiterals
      match dispatchedSecond.requiredLongLiteral? with
      | some needle =>
          if dispatchedFirst.requiredLongLiteral? == some needle then
            .choice dispatchedFirst dispatchedSecond
          else
            .dispatch needle dispatchedSecond dispatchedFirst
      | none => .choice dispatchedFirst dispatchedSecond
  | .dispatch needle present absent =>
      .dispatch needle
        present.dispatchRequiredLiterals
        absent.dispatchRequiredLiterals
termination_by code => sizeOf code

/-- Merge two compiled alternatives across operations whose result is independent of the
    continuation. Unlike source-level width search, greedy runs, fixed-width runs, direct
    repetitions, and literal dispatch have already committed to one input boundary here. -/
private def VerusSearchCode.mergeDeterministic :
    VerusSearchCode → VerusSearchCode → VerusSearchCode
  | .fail, second => second
  | first, .fail => first
  | .literal firstText firstNext, .literal secondText secondNext =>
      if firstText == secondText then
        .literal firstText (mergeDeterministic firstNext secondNext)
      else
        .choice (.literal firstText firstNext) (.literal secondText secondNext)
  | first@(.tokenRun firstToken firstLength firstNext),
      second@(.tokenRun secondToken secondLength secondNext) =>
      if firstToken == secondToken && firstLength == secondLength &&
          SearchCode.fixedWidth firstLength then
        .tokenRun firstToken firstLength (mergeDeterministic firstNext secondNext)
      else
        .choice first second
  | .greedyTokenRun firstToken firstLength firstNext,
      .greedyTokenRun secondToken secondLength secondNext =>
      if firstToken == secondToken && firstLength == secondLength then
        .greedyTokenRun firstToken firstLength
          (mergeDeterministic firstNext secondNext)
      else
        .choice
          (.greedyTokenRun firstToken firstLength firstNext)
          (.greedyTokenRun secondToken secondLength secondNext)
  | .capturedTokenRun firstItem firstNext,
      .capturedTokenRun secondItem secondNext =>
      if firstItem == secondItem then
        .capturedTokenRun firstItem (mergeDeterministic firstNext secondNext)
      else
        .choice
          (.capturedTokenRun firstItem firstNext)
          (.capturedTokenRun secondItem secondNext)
  | .save firstNext, .save secondNext =>
      .save (mergeDeterministic firstNext secondNext)
  | .capture firstKeys firstNext, .capture secondKeys secondNext =>
      if firstKeys == secondKeys then
        .capture firstKeys (mergeDeterministic firstNext secondNext)
      else
        .choice
          (.capture firstKeys firstNext)
          (.capture secondKeys secondNext)
  | .countCapture firstKey firstCount firstNext,
      .countCapture secondKey secondCount secondNext =>
      if firstKey == secondKey && firstCount == secondCount then
        .countCapture firstKey firstCount (mergeDeterministic firstNext secondNext)
      else
        .choice
          (.countCapture firstKey firstCount firstNext)
          (.countCapture secondKey secondCount secondNext)
  | .directRepetition firstSeparator firstItem firstLower firstUpper firstCountKey firstNext,
      .directRepetition secondSeparator secondItem secondLower secondUpper secondCountKey
        secondNext =>
      if firstSeparator == secondSeparator && firstItem == secondItem &&
          firstLower == secondLower && firstUpper == secondUpper &&
          firstCountKey == secondCountKey then
        .directRepetition firstSeparator firstItem firstLower firstUpper firstCountKey
          (mergeDeterministic firstNext secondNext)
      else
        .choice
          (.directRepetition firstSeparator firstItem firstLower firstUpper firstCountKey
            firstNext)
          (.directRepetition secondSeparator secondItem secondLower secondUpper secondCountKey
            secondNext)
  | .dispatch firstNeedle firstPresent firstAbsent,
      .dispatch secondNeedle secondPresent secondAbsent =>
      if firstNeedle == secondNeedle then
        .dispatch firstNeedle
          (mergeDeterministic firstPresent secondPresent)
          (mergeDeterministic firstAbsent secondAbsent)
      else
        .choice
          (.dispatch firstNeedle firstPresent firstAbsent)
          (.dispatch secondNeedle secondPresent secondAbsent)
  | first, second =>
      if first == second then first else .choice first second
termination_by first second => sizeOf first + sizeOf second

/-- Recursively left-factor already committed scanner operations. This is a generated-code
    optimization: source-ordered choices remain intact whenever a prefix can still select among
    candidate widths using its continuation. -/
private def VerusSearchCode.reduceDeterministic : VerusSearchCode → VerusSearchCode
  | .accept => .accept
  | .fail => .fail
  | .literal text next => .literal text next.reduceDeterministic
  | .stringLiteral next => .stringLiteral next.reduceDeterministic
  | .tokenRun token length next =>
      .tokenRun token length next.reduceDeterministic
  | .greedyTokenRun token length next =>
      .greedyTokenRun token length next.reduceDeterministic
  | .capturedTokenRun item next =>
      .capturedTokenRun item next.reduceDeterministic
  | .save next => .save next.reduceDeterministic
  | .capture keys next => .capture keys next.reduceDeterministic
  | .countCapture key itemCount next =>
      .countCapture key itemCount next.reduceDeterministic
  | .directRepetition separator item lower upper countKey next =>
      .directRepetition separator item lower upper countKey next.reduceDeterministic
  | .choice first second =>
      mergeDeterministic first.reduceDeterministic second.reduceDeterministic
  | .dispatch needle present absent =>
      .dispatch needle present.reduceDeterministic absent.reduceDeterministic
termination_by code => sizeOf code

/-- Whether a literal continuation can begin at the same boundary as `separator` followed by one
    token character. Returning `true` is conservative: uncertain prefixes remain on the complete
    ordered-search path. -/
private def directRepeatLiteralOverlaps (separator literal : List Char)
    (token : TokClass) : Bool :=
  match separator, literal with
  | [], character :: _ => decide (token.mem character)
  | [], [] => true
  | _ :: _, [] => true
  | separatorHead :: separatorTail, literalHead :: literalTail =>
      if separatorHead == literalHead then
        directRepeatLiteralOverlaps separatorTail literalTail token
      else
        false

/-- Certify that the continuation cannot accept at a boundary where another separated item can
    start. This is the condition that makes maximal repetition equivalent to ordered search. -/
private def VerusSearchCode.directRepeatBoundarySafe
    (separator : List Char) (token : TokClass) : VerusSearchCode → Bool
  | .accept
  | .fail => true
  | .literal text next =>
      match text.toList with
      | [] => next.directRepeatBoundarySafe separator token
      | character :: rest =>
          !directRepeatLiteralOverlaps separator (character :: rest) token
  | .save next
  | .capture _ next
  | .countCapture _ _ next =>
      next.directRepeatBoundarySafe separator token
  | .capturedTokenRun _ _ => false
  | .choice first second =>
      first.directRepeatBoundarySafe separator token &&
        second.directRepeatBoundarySafe separator token
  | .dispatch _ present absent =>
      present.directRepeatBoundarySafe separator token &&
        absent.directRepeatBoundarySafe separator token
  | _ => false

private def VerusSearchCode.directRepeatItem? :
    VerusSearchCode → Option VerusDirectRepeatItem
  | .capturedTokenRun item .accept => some item
  | .tokenRun token length .accept
  | .greedyTokenRun token length .accept =>
      some { token, length, keys := [] }
  | .save (.tokenRun token length (.capture keys .accept))
  | .save (.greedyTokenRun token length (.capture keys .accept)) =>
      if keys.length == 1 || keys.length == 2 then
        some { token, length, keys }
      else
        none
  | _ => none

/-- Apply the delimiter-certified token fusion after bounded repetitions have been expanded. This
    catches item runs whose separator is not visible in the source `SearchMachineCode`. -/
private def VerusSearchCode.fuse : VerusSearchCode → VerusSearchCode
  | .accept => .accept
  | .fail => .fail
  | .literal text next => .literal text next.fuse
  | .stringLiteral next => .stringLiteral next.fuse
  | .tokenRun token length next =>
      let fusedNext := next.fuse
      match length, fusedNext.requiredHead? with
      | .exactly _, _ => .tokenRun token length fusedNext
      | _, some character =>
          if decide (token.mem character) then
            .tokenRun token length fusedNext
          else
            .greedyTokenRun token length fusedNext
      | _, none => .tokenRun token length fusedNext
  | .greedyTokenRun token length next => .greedyTokenRun token length next.fuse
  | .capturedTokenRun item next => .capturedTokenRun item next.fuse
  | .save next =>
      let fusedNext := next.fuse
      match fusedNext with
      | .greedyTokenRun token length (.capture keys continuation) =>
          if keys.length == 1 || keys.length == 2 then
            .capturedTokenRun { token, length, keys } continuation
          else
            .save fusedNext
      | .tokenRun token (.exactly width) (.capture keys continuation) =>
          if keys.length == 1 || keys.length == 2 then
            .capturedTokenRun { token, length := .exactly width, keys } continuation
          else
            .save fusedNext
      | _ => .save fusedNext
  | .capture keys next => .capture keys next.fuse
  | .countCapture key itemCount next => .countCapture key itemCount next.fuse
  | .directRepetition separator item lower upper countKey next =>
      .directRepetition separator item lower upper countKey next.fuse
  | .choice first second => .choice first.fuse second.fuse
  | .dispatch needle present absent =>
      .dispatch needle present.fuse absent.fuse
termination_by code => sizeOf code

private def VerusSearchCode.boundedRepetition (separator countKey : String)
    (item next : VerusSearchCode) (lower upper : Nat) : VerusSearchCode :=
  let rec loop (remaining itemCount : Nat) : VerusSearchCode :=
    let stop := .countCapture (countKey ++ "#count") itemCount next
    match remaining with
    | 0 => stop
    | remaining + 1 =>
        let continuationCode :=
          .literal separator (item.plugAccept (loop remaining (itemCount + 1)))
        if lower ≤ itemCount then .choice stop continuationCode else continuationCode
  .save (item.plugAccept (loop (upper - 1) 1))

private partial def compileVerusSearchCode : SearchMachineCode → Except String VerusSearchCode
  | .accept => pure .accept
  | .fail => pure .fail
  | .literal text next => return .literal text (← compileVerusSearchCode next)
  | .stringLiteral next => return .stringLiteral (← compileVerusSearchCode next)
  | .tokenRun token length next =>
      return .tokenRun token length (← compileVerusSearchCode next)
  | .greedyTokenRun token length next =>
      return .greedyTokenRun token length (← compileVerusSearchCode next)
  | .save next => return .save (← compileVerusSearchCode next)
  | .capture keys next => return .capture keys (← compileVerusSearchCode next)
  | .choice first second =>
      return .choice (← compileVerusSearchCode first) (← compileVerusSearchCode second)
  | .repetition separator item lower upper countKey next => do
      let upper ← match upper with
        | some upper => pure upper
        | none =>
            throw "Verus backend: direct state emission requires a finite repetition upper bound"
      if upper == 0 then
        throw "Verus backend: direct state emission requires repetition upper bound at least one"
      let item ← compileVerusSearchCode item
      let next ← compileVerusSearchCode next
      let fusedItem := item.fuse
      let fusedNext := next.fuse
      match fusedItem.directRepeatItem? with
      | some directItem =>
          if lower > 0 && lower ≤ upper &&
              (lower == upper ||
                fusedNext.directRepeatBoundarySafe separator.toList directItem.token) then
            pure
              (.directRepetition separator directItem lower upper countKey fusedNext)
          else
            pure
              (VerusSearchCode.boundedRepetition
                separator countKey fusedItem fusedNext lower upper).fuse
      | _ =>
          pure
            (VerusSearchCode.boundedRepetition
              separator countKey fusedItem fusedNext lower upper).fuse

/-- Keep only source capture keys read by the executable semantic plan. Grammar control flow is
    unchanged; dead capture wrappers are erased before first-order lowering. -/
private def liveCaptureKeys (grammar : FlatGrammar) (selectors : List CaptureSelector)
    (keys : List String) : List String :=
  keys.filter fun key =>
    match captureSelector? grammar key with
    | some selector => selectors.contains selector
    | none => false

/-- Lower continuation-based search while erasing captures that cannot affect the generated
    domain value or constraints. -/
private def lowerLiveSearchCode (grammar : FlatGrammar) (selectors : List CaptureSelector) :
    SearchCode → SearchMachineCode → SearchMachineCode
  | .accept, continuation => continuation
  | .fail, _ => .fail
  | .literal text next, continuation =>
      .literal text (lowerLiveSearchCode grammar selectors next continuation)
  | .stringLiteral next, continuation =>
      .stringLiteral (lowerLiveSearchCode grammar selectors next continuation)
  | .tokenRun token length next, continuation =>
      .tokenRun token length
        (lowerLiveSearchCode grammar selectors next continuation)
  | .capture keys body next, continuation =>
      let machineNext := lowerLiveSearchCode grammar selectors next continuation
      let retainedKeys := liveCaptureKeys grammar selectors keys
      if retainedKeys.isEmpty then
        lowerLiveSearchCode grammar selectors body machineNext
      else
        .save
          (lowerLiveSearchCode grammar selectors body
            (.capture retainedKeys machineNext))
  | .choice first second, continuation =>
      .choice
        (lowerLiveSearchCode grammar selectors first continuation)
        (lowerLiveSearchCode grammar selectors second continuation)
  | .repetition separator item lower upper countKey next, continuation =>
      .repetition separator
        (lowerLiveSearchCode grammar selectors item .accept)
        lower upper countKey
        (lowerLiveSearchCode grammar selectors next continuation)
termination_by code _continuation => sizeOf code

private def lowerLiveSearchProgram (grammar : FlatGrammar)
    (selectors : List CaptureSelector) (program : SearchProgram) : SearchMachine :=
  { start := program.start
    code :=
      (lowerLiveSearchCode grammar selectors program.code .accept).fuse.reduce }

/-- An allocation bound for reserved capture frames along any acyclic execution path. -/
private def VerusSearchCode.saveCapacity : VerusSearchCode → Nat
  | .accept
  | .fail => 0
  | .literal _ next
  | .stringLiteral next
  | .tokenRun _ _ next
  | .greedyTokenRun _ _ next
  | .capturedTokenRun _ next
  | .capture _ next
  | .countCapture _ _ next => next.saveCapacity
  | .save next => next.saveCapacity + 1
  | .directRepetition _ _ _ _ _ next => max 1 next.saveCapacity
  | .choice first second => max first.saveCapacity second.saveCapacity
  | .dispatch _ present absent =>
      max present.saveCapacity absent.saveCapacity

/-- Additional capture slots required from a state. A generic `save` reserves two stable slots;
    fused terminal captures reserve exactly the number of live keys they record. -/
private def VerusSearchCode.captureCapacity : VerusSearchCode → Nat
  | .accept
  | .fail => 0
  | .literal _ next
  | .stringLiteral next
  | .tokenRun _ _ next
  | .greedyTokenRun _ _ next
  | .capture _ next
  | .countCapture _ _ next => next.captureCapacity
  | .capturedTokenRun item next => next.captureCapacity + item.keys.length
  | .save next => next.captureCapacity + 2
  | .directRepetition _ item _ upper _ next =>
      2 + item.keys.length * upper + next.captureCapacity
  | .choice first second => max first.captureCapacity second.captureCapacity
  | .dispatch _ present absent =>
      max present.captureCapacity absent.captureCapacity

private inductive VerusSearchNode where
  | accept (id : Nat)
  | fail (id : Nat)
  | literal (id : Nat) (text : String) (next : Nat)
  | stringLiteral (id next : Nat)
  | tokenRun (id : Nat) (token : TokClass) (length : LenSpec) (next : Nat)
  | greedyTokenRun (id : Nat) (token : TokClass) (length : LenSpec) (next : Nat)
  | capturedTokenRun (id : Nat) (item : VerusDirectRepeatItem) (next : Nat)
  | save (id next : Nat)
  | capture (id : Nat) (keys : List String) (next : Nat)
  | countCapture (id : Nat) (key : String) (itemCount : Nat) (next : Nat)
  | directRepetition (id : Nat) (separator : String) (item : VerusDirectRepeatItem)
      (lower upper : Nat) (countKey : String) (next : Nat)
  | choice (id first second : Nat)
  | dispatch (id : Nat) (literal : String) (present absent : Nat)
  deriving Repr, Inhabited

private def VerusSearchNode.id : VerusSearchNode → Nat
  | .accept id
  | .fail id
  | .literal id _ _
  | .stringLiteral id _
  | .tokenRun id _ _ _
  | .greedyTokenRun id _ _ _
  | .capturedTokenRun id _ _
  | .save id _
  | .capture id _ _
  | .countCapture id _ _ _
  | .directRepetition id _ _ _ _ _ _
  | .choice id _ _
  | .dispatch id _ _ _ => id

private def VerusSearchNode.successors : VerusSearchNode → List Nat
  | .accept _
  | .fail _ => []
  | .literal _ _ next
  | .stringLiteral _ next
  | .tokenRun _ _ _ next
  | .greedyTokenRun _ _ _ next
  | .capturedTokenRun _ _ next
  | .save _ next
  | .capture _ _ next
  | .countCapture _ _ _ next
  | .directRepetition _ _ _ _ _ _ next => [next]
  | .choice _ first second => [first, second]
  | .dispatch _ _ present absent => [present, absent]

private structure SearchMachineFlattenState where
  nextId : Nat := 0
  assigned : List (VerusSearchCode × Nat) := []
  nodes : List VerusSearchNode := []

private partial def internSearchMachineCode (code : VerusSearchCode)
    (state : SearchMachineFlattenState) :
    Except String (Nat × SearchMachineFlattenState) := do
  match state.assigned.find? fun (found, _) => found == code with
  | some (_, id) => pure (id, state)
  | none =>
    let id := state.nextId
    let reserved :=
      { state with
        nextId := id + 1
        assigned := (code, id) :: state.assigned }
    let addNode (node : VerusSearchNode) (nextState : SearchMachineFlattenState) :=
      (id, { nextState with nodes := node :: nextState.nodes })
    match code with
    | .accept =>
        pure (addNode (.accept id) reserved)
    | .fail =>
        pure (addNode (.fail id) reserved)
    | .literal text next =>
        let (nextRoot, nextState) ← internSearchMachineCode next reserved
        pure (addNode (.literal id text nextRoot) nextState)
    | .stringLiteral next =>
        let (nextRoot, nextState) ← internSearchMachineCode next reserved
        pure (addNode (.stringLiteral id nextRoot) nextState)
    | .tokenRun token length next =>
        let (nextRoot, nextState) ← internSearchMachineCode next reserved
        pure (addNode (.tokenRun id token length nextRoot) nextState)
    | .greedyTokenRun token length next =>
        let (nextRoot, nextState) ← internSearchMachineCode next reserved
        pure (addNode (.greedyTokenRun id token length nextRoot) nextState)
    | .capturedTokenRun item next =>
        let (nextRoot, nextState) ← internSearchMachineCode next reserved
        pure (addNode (.capturedTokenRun id item nextRoot) nextState)
    | .save next =>
        let (nextRoot, nextState) ← internSearchMachineCode next reserved
        pure (addNode (.save id nextRoot) nextState)
    | .capture keys next =>
        unless keys.length == 1 || keys.length == 2 do
          throw
            s!"Verus backend: direct search capture has {keys.length} keys; expected one or two"
        let (nextRoot, nextState) ← internSearchMachineCode next reserved
        pure (addNode (.capture id keys nextRoot) nextState)
    | .countCapture key itemCount next =>
        let (nextRoot, nextState) ← internSearchMachineCode next reserved
        pure (addNode (.countCapture id key itemCount nextRoot) nextState)
    | .directRepetition separator item lower upper countKey next =>
        let (nextRoot, nextState) ← internSearchMachineCode next reserved
        pure
          (addNode
            (.directRepetition id separator item lower upper countKey nextRoot)
            nextState)
    | .choice first second =>
        let (firstRoot, firstState) ← internSearchMachineCode first reserved
        let (secondRoot, secondState) ← internSearchMachineCode second firstState
        pure (addNode (.choice id firstRoot secondRoot) secondState)
    | .dispatch needle present absent =>
        let (presentRoot, presentState) ← internSearchMachineCode present reserved
        let (absentRoot, absentState) ← internSearchMachineCode absent presentState
        pure
          (addNode
            (.dispatch id needle presentRoot absentRoot)
            absentState)

private structure FlattenedSearchMachine where
  root : Nat
  nodes : List VerusSearchNode
  requirements : List (Nat × Nat × Nat)
  captureSlotCapacity : Nat
  markerCapacity : Nat

private def flattenSearchMachineCode (code : SearchMachineCode) :
    Except String FlattenedSearchMachine := do
  let compiled :=
    (← compileVerusSearchCode code).fuse.dispatchRequiredLiterals.reduceDeterministic
  let (root, state) ← internSearchMachineCode compiled {}
  let markerCapacity := compiled.saveCapacity
  let captureSlotCapacity := compiled.captureCapacity
  pure
    { root
      nodes := state.nodes.reverse
      requirements :=
        state.assigned.map fun (assignedCode, id) =>
          (id, assignedCode.captureCapacity, assignedCode.saveCapacity)
      captureSlotCapacity
      markerCapacity }

private def searchStateSpecFunction (format : FormatInput) (id : Nat) : String :=
  functionName format.name s!"search_state_{id}"

private def searchStateExecFunction (format : FormatInput) (id : Nat) : String :=
  searchStateSpecFunction format id ++ "_exec"

private def searchWidthSpecFunction (format : FormatInput) (id : Nat) : String :=
  functionName format.name s!"search_width_{id}"

private def searchWidthExecFunction (format : FormatInput) (id : Nat) : String :=
  searchWidthSpecFunction format id ++ "_exec"

private def renderSearchStateExecContract (specCall : String)
    (captureNeed markerNeed captureCapacity markerCapacity : Nat) : String :=
  s!"    requires
        input@.len() < usize::MAX,
        input_length == input@.len(),
        input_ascii == input.is_ascii(),
        old(state).semantic_cache.matches_input(input@),
        search_state_bounded(old(state).deep_view(), input@.len()),
        old(state).storage_well_formed(),
        old(state).captures@.len() + {captureNeed} <= {captureCapacity},
        old(state).markers.deep_view().len() + {markerNeed} <= {markerCapacity},
    ensures
        result ==> {specCall} == Some(final(state).deep_view())
            && search_state_bounded(final(state).deep_view(), input@.len())
            && final(state).storage_well_formed()
            && final(state).semantic_cache.matches_input(input@),
        !result ==> {specCall}.is_none()
            && final(state).deep_view() == old(state).deep_view()
            && final(state).storage_well_formed()
            && final(state).semantic_cache.matches_input(input@),"

private def renderMachineCaptureKey (grammar : FlatGrammar) (key : String) :
    Except String String := do
  let selector ← match captureSelector? grammar key with
    | some selector => pure selector
    | none => throw s!"Verus backend: direct search cannot resolve capture key `{key}`"
  pure (renderCaptureSelector selector)

private def renderSearchNode (format : FormatInput) (grammar : FlatGrammar)
    (cacheEntries : List SemanticCacheEntry)
    (nodes : List VerusSearchNode)
    (captureNeed markerNeed captureCapacity markerCapacity : Nat)
    (inlineExec : Bool) (node : VerusSearchNode) : Except String String := do
  let id := node.id
  let specName := searchStateSpecFunction format id
  let execName := searchStateExecFunction format id
  let specCall := s!"{specName}(input@, old(state).deep_view())"
  let contract :=
    renderSearchStateExecContract specCall
      captureNeed markerNeed captureCapacity markerCapacity
  let inlineAttribute := if inlineExec then "#[inline(always)]\n" else ""
  match node with
  | .accept _ =>
      pure s!"pub closed spec fn {specName}(
    input: Seq<char>,
    state: SearchStateSpec,
) -> Option<SearchStateSpec> {rustLeftBrace}
    if state.end == input.len() {rustLeftBrace}
        Some(state)
    {rustRightBrace} else {rustLeftBrace}
        None
    {rustRightBrace}
{rustRightBrace}

{inlineAttribute}fn {execName}(
    input: &str,
    input_length: usize,
    input_ascii: bool,
    state: &mut SearchState,
) -> (result: bool)
{contract}
{rustLeftBrace}
    proof {rustLeftBrace} reveal_with_fuel({specName}, 1); {rustRightBrace}
    if state.end == input_length {rustLeftBrace}
        true
    {rustRightBrace} else {rustLeftBrace}
        false
    {rustRightBrace}
{rustRightBrace}"
  | .fail _ =>
      pure s!"pub closed spec fn {specName}(
    input: Seq<char>,
    state: SearchStateSpec,
) -> Option<SearchStateSpec> {rustLeftBrace}
    None
{rustRightBrace}

{inlineAttribute}fn {execName}(
    input: &str,
    input_length: usize,
    input_ascii: bool,
    state: &mut SearchState,
) -> (result: bool)
{contract}
{rustLeftBrace}
    proof {rustLeftBrace} reveal_with_fuel({specName}, 1); {rustRightBrace}
    false
{rustRightBrace}"
  | .literal _ text next =>
      let nextSpec := searchStateSpecFunction format next
      let nextExec := searchStateExecFunction format next
      let literal := String.quote text
      pure s!"pub closed spec fn {specName}(
    input: Seq<char>,
    state: SearchStateSpec,
) -> Option<SearchStateSpec> {rustLeftBrace}
    if literal_matches_at(input, state.end, {literal}@) {rustLeftBrace}
        {nextSpec}(
            input,
            search_advance(state, state.end + {literal}@.len()),
        )
    {rustRightBrace} else {rustLeftBrace}
        None
    {rustRightBrace}
{rustRightBrace}

{inlineAttribute}fn {execName}(
    input: &str,
    input_length: usize,
    input_ascii: bool,
    state: &mut SearchState,
) -> (result: bool)
{contract}
{rustLeftBrace}
    proof {rustLeftBrace} reveal_with_fuel({specName}, 1); {rustRightBrace}
    match search_match_literal_at(
        input,
        input_length,
        input_ascii,
        state.end,
        {literal},
    ) {rustLeftBrace}
        Some(found) => {rustLeftBrace}
            let previous_end = state.end;
            search_advance_exec(state, found.end);
            if {nextExec}(input, input_length, input_ascii, state) {rustLeftBrace}
                true
            {rustRightBrace} else {rustLeftBrace}
                search_restore_end_exec(state, previous_end);
                false
            {rustRightBrace}
        {rustRightBrace},
        None => false,
    {rustRightBrace}
{rustRightBrace}"
  | .stringLiteral _ next =>
      let nextSpec := searchStateSpecFunction format next
      let nextExec := searchStateExecFunction format next
      let widthSpec := searchWidthSpecFunction format id
      let widthExec := searchWidthExecFunction format id
      pure s!"pub closed spec fn {widthSpec}(
    input: Seq<char>,
    state: SearchStateSpec,
    width: nat,
    fuel: nat,
) -> Option<SearchStateSpec>
    recommends
        search_state_bounded(state, input.len()),
    decreases fuel,
{rustLeftBrace}
    let remaining = (input.len() as int - state.end) as nat;
    if fuel == 0 || width > remaining {rustLeftBrace}
        None
    {rustRightBrace} else if string_literal_matches_at(
        input,
        state.end,
        width as int,
    ) {rustLeftBrace}
        match {nextSpec}(
            input,
            search_advance(state, state.end + width as int),
        ) {rustLeftBrace}
            Some(found) => Some(found),
            None =>
                if width < remaining {rustLeftBrace}
                    {widthSpec}(input, state, width + 1, (fuel - 1) as nat)
                {rustRightBrace} else {rustLeftBrace}
                    None
                {rustRightBrace},
        {rustRightBrace}
    {rustRightBrace} else {rustLeftBrace}
        if width < remaining {rustLeftBrace}
            {widthSpec}(input, state, width + 1, (fuel - 1) as nat)
        {rustRightBrace} else {rustLeftBrace}
            None
        {rustRightBrace}
    {rustRightBrace}
{rustRightBrace}

fn {widthExec}(
    input: &str,
    input_length: usize,
    input_ascii: bool,
    state: &mut SearchState,
    width: usize,
    fuel: usize,
) -> (result: bool)
    requires
        input@.len() < usize::MAX,
        input_length == input@.len(),
        input_ascii == input.is_ascii(),
        old(state).semantic_cache.matches_input(input@),
        search_state_bounded(old(state).deep_view(), input@.len()),
        old(state).storage_well_formed(),
        old(state).captures@.len() + {captureNeed} <= {captureCapacity},
        old(state).markers.deep_view().len() + {markerNeed} <= {markerCapacity},
        width <= input@.len() - old(state).end,
        fuel == input@.len() - old(state).end - width + 1,
    ensures
        result ==> {widthSpec}(
            input@,
            old(state).deep_view(),
            width as nat,
            fuel as nat,
        ) == Some(final(state).deep_view())
            && search_state_bounded(final(state).deep_view(), input@.len())
            && final(state).storage_well_formed()
            && final(state).semantic_cache.matches_input(input@),
        !result ==> {widthSpec}(
            input@,
            old(state).deep_view(),
            width as nat,
            fuel as nat,
        ).is_none()
            && final(state).deep_view() == old(state).deep_view()
            && final(state).storage_well_formed()
            && final(state).semantic_cache.matches_input(input@),
    decreases fuel,
{rustLeftBrace}
    proof {rustLeftBrace} reveal_with_fuel({widthSpec}, 1); {rustRightBrace}
    if let Some(found) =
        search_match_string_literal_at_width(input, input_length, state.end, width)
    {rustLeftBrace}
        let previous_end = state.end;
        search_advance_exec(state, found.end);
        if {nextExec}(input, input_length, input_ascii, state) {rustLeftBrace}
            return true;
        {rustRightBrace}
        search_restore_end_exec(state, previous_end);
    {rustRightBrace}
    let remaining = input_length - state.end;
    if width < remaining {rustLeftBrace}
        {widthExec}(input, input_length, input_ascii, state, width + 1, fuel - 1)
    {rustRightBrace} else {rustLeftBrace}
        false
    {rustRightBrace}
{rustRightBrace}

pub closed spec fn {specName}(
    input: Seq<char>,
    state: SearchStateSpec,
) -> Option<SearchStateSpec> {rustLeftBrace}
    {widthSpec}(
        input,
        state,
        0,
        (input.len() as int - state.end + 1) as nat,
    )
{rustRightBrace}

{inlineAttribute}fn {execName}(
    input: &str,
    input_length: usize,
    input_ascii: bool,
    state: &mut SearchState,
) -> (result: bool)
{contract}
{rustLeftBrace}
    proof {rustLeftBrace} reveal_with_fuel({specName}, 1); {rustRightBrace}
    let fuel = input_length - state.end + 1;
    {widthExec}(input, input_length, input_ascii, state, 0, fuel)
{rustRightBrace}"
  | .tokenRun _ token length next =>
      let nextSpec := searchStateSpecFunction format next
      let nextExec := searchStateExecFunction format next
      let widthSpec := searchWidthSpecFunction format id
      let widthExec := searchWidthExecFunction format id
      let renderedToken := renderTokenClass token
      let renderedLength := renderLengthSpec length
      let specSearch := match length with
        | .exactly expected =>
            s!"    let remaining = (input.len() as int - state.end) as nat;
    if {expected} > remaining {rustLeftBrace}
        None
    {rustRightBrace} else {rustLeftBrace}
        {widthSpec}(input, state, {expected}, 1)
    {rustRightBrace}"
        | .between lower upper =>
            s!"    let remaining = (input.len() as int - state.end) as nat;
    if {lower} > remaining {rustLeftBrace}
        None
    {rustRightBrace} else {rustLeftBrace}
        let limit = if {upper} < remaining {rustLeftBrace} {upper} {rustRightBrace} else {rustLeftBrace} remaining {rustRightBrace};
        {widthSpec}(input, state, {lower}, (limit - {lower} + 1) as nat)
    {rustRightBrace}"
        | .atLeastOne =>
            s!"    let remaining = (input.len() as int - state.end) as nat;
    if remaining == 0 {rustLeftBrace}
        None
    {rustRightBrace} else {rustLeftBrace}
        {widthSpec}(input, state, 1, remaining)
    {rustRightBrace}"
      let execSearch := match length with
        | .exactly expected =>
            s!"    let remaining = input_length - state.end;
    if {expected} > remaining {rustLeftBrace}
        proof {rustLeftBrace} reveal_with_fuel({specName}, 1); {rustRightBrace}
        false
    {rustRightBrace} else {rustLeftBrace}
        let prefix_limit = state.end + {expected};
        let prefix_end = search_token_prefix_end(
            input,
            input_length,
            input_ascii,
            state.end,
            prefix_limit,
            {renderedToken},
        );
        {widthExec}(
            input,
            input_length,
            input_ascii,
            state,
            {expected},
            1,
            prefix_limit,
            prefix_end,
        )
    {rustRightBrace}"
        | .between lower upper =>
            s!"    let remaining = input_length - state.end;
    if {lower} > remaining {rustLeftBrace}
        proof {rustLeftBrace} reveal_with_fuel({specName}, 1); {rustRightBrace}
        false
    {rustRightBrace} else {rustLeftBrace}
        let limit = if {upper} < remaining {rustLeftBrace} {upper} {rustRightBrace} else {rustLeftBrace} remaining {rustRightBrace};
        let prefix_limit = state.end + limit;
        let prefix_end = search_token_prefix_end(
            input,
            input_length,
            input_ascii,
            state.end,
            prefix_limit,
            {renderedToken},
        );
        {widthExec}(
            input,
            input_length,
            input_ascii,
            state,
            {lower},
            limit - {lower} + 1,
            prefix_limit,
            prefix_end,
        )
    {rustRightBrace}"
        | .atLeastOne =>
            s!"    let remaining = input_length - state.end;
    if remaining == 0 {rustLeftBrace}
        proof {rustLeftBrace} reveal_with_fuel({specName}, 1); {rustRightBrace}
        false
    {rustRightBrace} else {rustLeftBrace}
        let prefix_limit = input_length;
        let prefix_end = search_token_prefix_end(
            input,
            input_length,
            input_ascii,
            state.end,
            prefix_limit,
            {renderedToken},
        );
        {widthExec}(
            input,
            input_length,
            input_ascii,
            state,
            1,
            remaining,
            prefix_limit,
            prefix_end,
        )
    {rustRightBrace}"
      pure s!"pub closed spec fn {widthSpec}(
    input: Seq<char>,
    state: SearchStateSpec,
    width: nat,
    fuel: nat,
) -> Option<SearchStateSpec>
    recommends
        search_state_bounded(state, input.len()),
    decreases fuel,
{rustLeftBrace}
    let remaining = (input.len() as int - state.end) as nat;
    if fuel == 0 || width > remaining {rustLeftBrace}
        None
    {rustRightBrace} else if terminal_matches_at(
        input,
        state.end,
        width as int,
        {renderedToken},
        {renderedLength},
    ) {rustLeftBrace}
        match {nextSpec}(
            input,
            search_advance(state, state.end + width as int),
        ) {rustLeftBrace}
            Some(found) => Some(found),
            None =>
                if fuel > 1 {rustLeftBrace}
                    {widthSpec}(input, state, width + 1, (fuel - 1) as nat)
                {rustRightBrace} else {rustLeftBrace}
                    None
                {rustRightBrace},
        {rustRightBrace}
    {rustRightBrace} else {rustLeftBrace}
        if fuel > 1 {rustLeftBrace}
            {widthSpec}(input, state, width + 1, (fuel - 1) as nat)
        {rustRightBrace} else {rustLeftBrace}
            None
        {rustRightBrace}
    {rustRightBrace}
{rustRightBrace}

fn {widthExec}(
    input: &str,
    input_length: usize,
    input_ascii: bool,
    state: &mut SearchState,
    width: usize,
    fuel: usize,
    prefix_limit: usize,
    prefix_end: usize,
) -> (result: bool)
    requires
        input@.len() < usize::MAX,
        input_length == input@.len(),
        input_ascii == input.is_ascii(),
        old(state).semantic_cache.matches_input(input@),
        search_state_bounded(old(state).deep_view(), input@.len()),
        old(state).storage_well_formed(),
        old(state).captures@.len() + {captureNeed} <= {captureCapacity},
        old(state).markers.deep_view().len() + {markerNeed} <= {markerCapacity},
        search_token_prefix_valid(
            input@,
            old(state).deep_view().end,
            prefix_limit as int,
            prefix_end as int,
            {renderedToken},
        ),
        width <= prefix_limit - old(state).end,
        0 < fuel <= prefix_limit - old(state).end - width + 1,
    ensures
        result ==> {widthSpec}(
            input@,
            old(state).deep_view(),
            width as nat,
            fuel as nat,
        ) == Some(final(state).deep_view())
            && search_state_bounded(final(state).deep_view(), input@.len())
            && final(state).storage_well_formed()
            && final(state).semantic_cache.matches_input(input@),
        !result ==> {widthSpec}(
            input@,
            old(state).deep_view(),
            width as nat,
            fuel as nat,
        ).is_none()
            && final(state).deep_view() == old(state).deep_view()
            && final(state).storage_well_formed()
            && final(state).semantic_cache.matches_input(input@),
    decreases fuel,
{rustLeftBrace}
    proof {rustLeftBrace} reveal_with_fuel({widthSpec}, 1); {rustRightBrace}
    if let Some(found) = search_match_terminal_from_prefix(
        input,
        state.end,
        width,
        {renderedToken},
        {renderedLength},
        prefix_limit,
        prefix_end,
    ) {rustLeftBrace}
        let previous_end = state.end;
        search_advance_exec(state, found.end);
        if {nextExec}(input, input_length, input_ascii, state) {rustLeftBrace}
            return true;
        {rustRightBrace}
        search_restore_end_exec(state, previous_end);
    {rustRightBrace}
    if fuel > 1 {rustLeftBrace}
        {widthExec}(
            input,
            input_length,
            input_ascii,
            state,
            width + 1,
            fuel - 1,
            prefix_limit,
            prefix_end,
        )
    {rustRightBrace} else {rustLeftBrace}
        false
    {rustRightBrace}
{rustRightBrace}

pub closed spec fn {specName}(
    input: Seq<char>,
    state: SearchStateSpec,
) -> Option<SearchStateSpec> {rustLeftBrace}
{specSearch}
{rustRightBrace}

{inlineAttribute}fn {execName}(
    input: &str,
    input_length: usize,
    input_ascii: bool,
    state: &mut SearchState,
) -> (result: bool)
{contract}
{rustLeftBrace}
    proof {rustLeftBrace} reveal_with_fuel({specName}, 1); {rustRightBrace}
{execSearch}
{rustRightBrace}"
  | .greedyTokenRun _ token length next =>
      let nextSpec := searchStateSpecFunction format next
      let nextExec := searchStateExecFunction format next
      let renderedToken := renderTokenClass token
      let renderedLength := renderLengthSpec length
      let specBody := match length with
        | .exactly expected =>
            s!"    let remaining = input.len() - state.end;
    if {expected} > remaining {rustLeftBrace}
        None
    {rustRightBrace} else if terminal_matches_at(
        input,
        state.end,
        {expected},
        {renderedToken},
        {renderedLength},
    ) {rustLeftBrace}
        {nextSpec}(input, search_advance(state, state.end + {expected}))
    {rustRightBrace} else {rustLeftBrace}
        None
    {rustRightBrace}"
        | .between _ upper =>
            s!"    let input_length = input.len() as int;
    let remaining = input_length - state.end;
    let limit = if {upper} < remaining {rustLeftBrace}
        state.end + {upper}
    {rustRightBrace} else {rustLeftBrace}
        input_length
    {rustRightBrace};
    let end = search_token_prefix_end_spec(
        input,
        state.end,
        limit,
        {renderedToken},
    );
    let width = end - state.end;
    if terminal_matches_at(
        input,
        state.end,
        width,
        {renderedToken},
        {renderedLength},
    ) {rustLeftBrace}
        {nextSpec}(input, search_advance(state, end))
    {rustRightBrace} else {rustLeftBrace}
        None
    {rustRightBrace}"
        | .atLeastOne =>
            s!"    let end = search_token_prefix_end_spec(
        input,
        state.end,
        input.len() as int,
        {renderedToken},
    );
    let width = end - state.end;
    if terminal_matches_at(
        input,
        state.end,
        width,
        {renderedToken},
        {renderedLength},
    ) {rustLeftBrace}
        {nextSpec}(input, search_advance(state, end))
    {rustRightBrace} else {rustLeftBrace}
        None
    {rustRightBrace}"
      let execLimit := match length with
        | .exactly expected => s!"state.end + {expected}"
        | .between _ upper =>
            s!"if {upper} < input_length - state.end {rustLeftBrace}
        state.end + {upper}
    {rustRightBrace} else {rustLeftBrace}
        input_length
    {rustRightBrace}"
        | .atLeastOne => "input_length"
      let execWidth := match length with
        | .exactly expected => toString expected
        | _ => "prefix_end - state.end"
      let execBounds := match length with
        | .exactly expected =>
            s!"    if {expected} > input_length - state.end {rustLeftBrace}
        proof {rustLeftBrace} reveal_with_fuel({specName}, 1); {rustRightBrace}
        return false;
    {rustRightBrace}
"
        | _ => ""
      pure s!"pub closed spec fn {specName}(
    input: Seq<char>,
    state: SearchStateSpec,
) -> Option<SearchStateSpec> {rustLeftBrace}
{specBody}
{rustRightBrace}

{inlineAttribute}fn {execName}(
    input: &str,
    input_length: usize,
    input_ascii: bool,
    state: &mut SearchState,
) -> (result: bool)
{contract}
{rustLeftBrace}
    proof {rustLeftBrace} reveal_with_fuel({specName}, 1); {rustRightBrace}
{execBounds}    let prefix_limit = {execLimit};
    let prefix_end = search_token_prefix_end(
        input,
        input_length,
        input_ascii,
        state.end,
        prefix_limit,
        {renderedToken},
    );
    let width = {execWidth};
    if let Some(found) = search_match_terminal_from_prefix(
        input,
        state.end,
        width,
        {renderedToken},
        {renderedLength},
        prefix_limit,
        prefix_end,
    ) {rustLeftBrace}
        let previous_end = state.end;
        search_advance_exec(state, found.end);
        if {nextExec}(input, input_length, input_ascii, state) {rustLeftBrace}
            return true;
        {rustRightBrace}
        search_restore_end_exec(state, previous_end);
    {rustRightBrace}
    false
{rustRightBrace}"
  | .capturedTokenRun _ item next =>
      let nextSpec := searchStateSpecFunction format next
      let nextExec := searchStateExecFunction format next
      let renderedToken := renderTokenClass item.token
      let renderedLength := renderLengthSpec item.length
      let renderedKeys ← item.keys.mapM (renderMachineCaptureKey grammar)
      let (recordSpec, recordExec, preserveCheckpoint, recordArguments) ←
        match renderedKeys with
        | [key] =>
            pure ("search_record_capture_one", "search_record_capture_one_exec",
              "search_record_capture_one_preserves_checkpoint", key)
        | [first, second] =>
            pure ("search_record_capture_two", "search_record_capture_two_exec",
              "search_record_capture_two_preserves_checkpoint",
              first ++ ", " ++ second)
        | _ =>
            throw "Verus backend: invalid fused captured-token key count"
      let cacheWrites ←
        renderSemanticCacheWrites grammar cacheEntries item.keys "capture_start" "found.end"
      let specBody := match item.length with
        | .exactly expected =>
            s!"    let remaining = input.len() - state.end;
    if {expected} > remaining {rustLeftBrace}
        None
    {rustRightBrace} else if terminal_matches_at(
        input,
        state.end,
        {expected},
        {renderedToken},
        {renderedLength},
    ) {rustLeftBrace}
        {nextSpec}(
            input,
            {recordSpec}(
                state,
                state.end + {expected},
                {recordArguments},
            ),
        )
    {rustRightBrace} else {rustLeftBrace}
        None
    {rustRightBrace}"
        | .between _ upper =>
            s!"    let input_length = input.len() as int;
    let remaining = input_length - state.end;
    let limit = if {upper} < remaining {rustLeftBrace}
        state.end + {upper}
    {rustRightBrace} else {rustLeftBrace}
        input_length
    {rustRightBrace};
    let end = search_token_prefix_end_spec(
        input,
        state.end,
        limit,
        {renderedToken},
    );
    let width = end - state.end;
    if terminal_matches_at(
        input,
        state.end,
        width,
        {renderedToken},
        {renderedLength},
    ) {rustLeftBrace}
        {nextSpec}(
            input,
            {recordSpec}(state, end, {recordArguments}),
        )
    {rustRightBrace} else {rustLeftBrace}
        None
    {rustRightBrace}"
        | .atLeastOne =>
            s!"    let end = search_token_prefix_end_spec(
        input,
        state.end,
        input.len() as int,
        {renderedToken},
    );
    let width = end - state.end;
    if terminal_matches_at(
        input,
        state.end,
        width,
        {renderedToken},
        {renderedLength},
    ) {rustLeftBrace}
        {nextSpec}(
            input,
            {recordSpec}(state, end, {recordArguments}),
        )
    {rustRightBrace} else {rustLeftBrace}
        None
    {rustRightBrace}"
      let execLimit := match item.length with
        | .exactly expected => s!"state.end + {expected}"
        | .between _ upper =>
            s!"if {upper} < input_length - state.end {rustLeftBrace}
        state.end + {upper}
    {rustRightBrace} else {rustLeftBrace}
        input_length
    {rustRightBrace}"
        | .atLeastOne => "input_length"
      let execWidth := match item.length with
        | .exactly expected => toString expected
        | _ => "prefix_end - state.end"
      let execBounds := match item.length with
        | .exactly expected =>
            s!"    if {expected} > input_length - state.end {rustLeftBrace}
        proof {rustLeftBrace} reveal_with_fuel({specName}, 1); {rustRightBrace}
        return false;
    {rustRightBrace}
"
        | _ => ""
      pure s!"pub closed spec fn {specName}(
    input: Seq<char>,
    state: SearchStateSpec,
) -> Option<SearchStateSpec> {rustLeftBrace}
{specBody}
{rustRightBrace}

{inlineAttribute}fn {execName}(
    input: &str,
    input_length: usize,
    input_ascii: bool,
    state: &mut SearchState,
) -> (result: bool)
{contract}
{rustLeftBrace}
    let checkpoint = search_checkpoint(state);
    let ghost original_view = state.deep_view();
    let capture_start = state.end;
    proof {rustLeftBrace} reveal_with_fuel({specName}, 1); {rustRightBrace}
{execBounds}    let prefix_limit = {execLimit};
    let prefix_end = search_token_prefix_end(
        input,
        input_length,
        input_ascii,
        state.end,
        prefix_limit,
        {renderedToken},
    );
    let width = {execWidth};
    if let Some(found) = search_match_terminal_from_prefix(
        input,
        state.end,
        width,
        {renderedToken},
        {renderedLength},
        prefix_limit,
        prefix_end,
    ) {rustLeftBrace}
        {recordExec}(
            state,
            found.end,
            {recordArguments},
            Ghost(input@.len()),
        );
{cacheWrites}
        proof {rustLeftBrace}
            {preserveCheckpoint}(
                checkpoint,
                original_view,
                original_view,
                found.end as int,
                {recordArguments},
            );
            assert(search_checkpoint_matches(
                checkpoint,
                original_view,
                state.deep_view(),
            ));
        {rustRightBrace}
        if {nextExec}(input, input_length, input_ascii, state) {rustLeftBrace}
            return true;
        {rustRightBrace}
        search_restore_checkpoint_to_exec(
            state,
            checkpoint,
            Ghost(original_view),
        );
    {rustRightBrace}
    false
{rustRightBrace}"
  | .save _ next =>
      let nextSpec := searchStateSpecFunction format next
      let nextExec := searchStateExecFunction format next
      pure s!"pub closed spec fn {specName}(
    input: Seq<char>,
    state: SearchStateSpec,
) -> Option<SearchStateSpec> {rustLeftBrace}
    {nextSpec}(input, search_save(state))
{rustRightBrace}

{inlineAttribute}fn {execName}(
    input: &str,
    input_length: usize,
    input_ascii: bool,
    state: &mut SearchState,
) -> (result: bool)
{contract}
{rustLeftBrace}
    proof {rustLeftBrace} reveal_with_fuel({specName}, 1); {rustRightBrace}
    search_save_exec(state);
    if {nextExec}(input, input_length, input_ascii, state) {rustLeftBrace}
        true
    {rustRightBrace} else {rustLeftBrace}
        search_restore_save_exec(state);
        false
    {rustRightBrace}
{rustRightBrace}"
  | .capture _ keys next =>
      let nextSpec := searchStateSpecFunction format next
      let nextExec := searchStateExecFunction format next
      let renderedKeys ← keys.mapM (renderMachineCaptureKey grammar)
      let (closeSpec, closeExec, reopenExec, arguments) ← match renderedKeys with
        | [key] =>
            pure ("search_close_capture_one", "search_close_capture_one_exec",
              "search_reopen_capture_one_exec", key)
        | [first, second] =>
            pure ("search_close_capture_two", "search_close_capture_two_exec",
              "search_reopen_capture_two_exec",
              first ++ ", " ++ second)
        | _ => throw "Verus backend: invalid direct search capture key count"
      let cacheWrites ←
        renderSemanticCacheWrites grammar cacheEntries keys "marker.start" "state.end"
      pure s!"pub closed spec fn {specName}(
    input: Seq<char>,
    state: SearchStateSpec,
) -> Option<SearchStateSpec> {rustLeftBrace}
    match {closeSpec}(state, {arguments}) {rustLeftBrace}
        Some(closed) => {nextSpec}(input, closed),
        None => None,
    {rustRightBrace}
{rustRightBrace}

{inlineAttribute}fn {execName}(
    input: &str,
    input_length: usize,
    input_ascii: bool,
    state: &mut SearchState,
) -> (result: bool)
{contract}
{rustLeftBrace}
    proof {rustLeftBrace} reveal_with_fuel({specName}, 1); {rustRightBrace}
    let original = Ghost(state.deep_view());
    if state.markers.len() == 0 {rustLeftBrace}
        return false;
    {rustRightBrace}
    let marker = state.markers.get(state.markers.len() - 1);
    if !{closeExec}(state, {arguments}, Ghost(input@.len())) {rustLeftBrace}
        return false;
    {rustRightBrace}
{cacheWrites}
    if {nextExec}(input, input_length, input_ascii, state) {rustLeftBrace}
        true
    {rustRightBrace} else {rustLeftBrace}
        {reopenExec}(state, marker, {arguments}, original);
        false
    {rustRightBrace}
{rustRightBrace}"
  | .countCapture _ key itemCount next =>
      let nextSpec := searchStateSpecFunction format next
      let nextExec := searchStateExecFunction format next
      let renderedKey ← renderMachineCaptureKey grammar key
      pure s!"pub closed spec fn {specName}(
    input: Seq<char>,
    state: SearchStateSpec,
) -> Option<SearchStateSpec> {rustLeftBrace}
    match search_close_count_capture(state, {renderedKey}, {itemCount}) {rustLeftBrace}
        Some(closed) => {nextSpec}(input, closed),
        None => None,
    {rustRightBrace}
{rustRightBrace}

{inlineAttribute}fn {execName}(
    input: &str,
    input_length: usize,
    input_ascii: bool,
    state: &mut SearchState,
) -> (result: bool)
{contract}
{rustLeftBrace}
    proof {rustLeftBrace} reveal_with_fuel({specName}, 1); {rustRightBrace}
    let original = Ghost(state.deep_view());
    if state.markers.len() == 0 {rustLeftBrace}
        return false;
    {rustRightBrace}
    let marker = state.markers.get(state.markers.len() - 1);
    if !search_close_count_capture_exec(
        state,
        {renderedKey},
        {itemCount},
        Ghost(input@.len()),
    ) {rustLeftBrace}
        return false;
    {rustRightBrace}
    if {nextExec}(input, input_length, input_ascii, state) {rustLeftBrace}
        true
    {rustRightBrace} else {rustLeftBrace}
        search_reopen_count_capture_exec(
            state,
            marker,
            {renderedKey},
            {itemCount},
            original,
        );
        false
    {rustRightBrace}
{rustRightBrace}"
  | .directRepetition _ separator item lower upper countKey next =>
      let nextSpec := searchStateSpecFunction format next
      let nextExec := searchStateExecFunction format next
      let itemSpec := specName ++ "_item"
      let itemExec := itemSpec ++ "_exec"
      let tailSpec := specName ++ "_tail"
      let tailExec := tailSpec ++ "_exec"
      let separatorLiteral := String.quote separator
      let (separatorMatcherPrelude, separatorMatcher) :=
        if separator.toList.length == 1 then
          (s!"    proof {rustLeftBrace}
        reveal_strlit({separatorLiteral});
        assert({separatorLiteral}@.len() == 1);
    {rustRightBrace}
",
           "search_match_single_literal_at")
        else
          ("", "search_match_literal_at")
      let renderedToken := renderTokenClass item.token
      let renderedLength := renderLengthSpec item.length
      let renderedKeys ← item.keys.mapM (renderMachineCaptureKey grammar)
      let itemCaptureCount := renderedKeys.length
      let fusedCacheEntry? :=
        -- H16 prefix arithmetic is single-load and statically proved overflow-free.
        if separator == ":" && item.token == .hexDigit &&
            match item.length with
            | .exactly width => width ≤ 4
            | .between _ upper => upper ≤ 4
            | .atLeastOne => false then
          match nodes.find? fun candidate => candidate.id == next with
          | some (.capture _ keys _) =>
              (keys.filterMap fun key =>
                semanticCacheEntryForKey grammar cacheEntries key).find?
                  (·.kind == .hexSequence)
          | _ => none
        else
          none
      let (recordSpecExpression, recordExecStatement) ← match renderedKeys with
        | [] =>
            pure
              ("search_advance(state, end)",
               "search_advance_exec(state, found.end);")
        | [key] =>
            pure
              (s!"search_record_capture_one(state, end, {key})",
               s!"search_record_capture_one_exec(
            state,
            found.end,
            {key},
            Ghost(input@.len()),
        );")
        | [first, second] =>
            pure
              (s!"search_record_capture_two(state, end, {first}, {second})",
               s!"search_record_capture_two_exec(
            state,
            found.end,
            {first}, {second},
            Ghost(input@.len()),
        );")
        | _ => throw "Verus backend: invalid deterministic repetition capture key count"
      let renderedCountKey ← renderMachineCaptureKey grammar (countKey ++ "#count")
      let specLimit := match item.length with
        | .exactly width
        | .between _ width =>
            s!"if {width} < remaining {rustLeftBrace}
        state.end + {width}
    {rustRightBrace} else {rustLeftBrace}
        input_length
    {rustRightBrace}"
        | .atLeastOne => "input_length"
      let execLimit := match item.length with
        | .exactly width
        | .between _ width =>
            s!"if {width} < input_length - state.end {rustLeftBrace}
        state.end + {width}
    {rustRightBrace} else {rustLeftBrace}
        input_length
    {rustRightBrace}"
        | .atLeastOne => "input_length"
      let itemExecDeclaration :=
        match fusedCacheEntry? with
        | some _ =>
            s!"#[inline(always)]
fn {itemExec}(
    input: &str,
    input_length: usize,
    input_ascii: bool,
    state: &mut SearchState,
) -> (result: Option<SemanticHexPrefixSummary>)
    requires
        input@.len() < usize::MAX,
        input_length == input@.len(),
        input_ascii == input.is_ascii(),
        old(state).semantic_cache.matches_input(input@),
        search_state_bounded(old(state).deep_view(), input@.len()),
        old(state).storage_well_formed(),
        old(state).captures@.len() + {itemCaptureCount} <= {captureCapacity},
        old(state).markers.deep_view().len() <= {markerCapacity},
    ensures
        match result {rustLeftBrace}
            Some(summary) =>
                {itemSpec}(input@, old(state).deep_view())
                    == Some(final(state).deep_view())
                && search_state_bounded(final(state).deep_view(), input@.len())
                && final(state).storage_well_formed()
                && final(state).captures@.len()
                    == old(state).captures@.len() + {itemCaptureCount}
                && final(state).captures@.take(old(state).captures@.len() as int)
                    == old(state).captures@
                && final(state).markers.deep_view()
                    == old(state).markers.deep_view()
                && final(state).semantic_cache.matches_input(input@)
                && old(state).end < summary.end
                && summary.end == final(state).end
                && summary.value as int == triptych_hex_seq_of(
                    input@.subrange(old(state).end as int, summary.end as int)
                )
                && forall|index: int| old(state).end <= index < summary.end ==>
                    #[trigger] input@[index] != ':',
            None =>
                {itemSpec}(input@, old(state).deep_view()).is_none()
                && final(state).deep_view() == old(state).deep_view()
                && final(state).storage_well_formed()
                && final(state).semantic_cache.matches_input(input@),
        {rustRightBrace},
{rustLeftBrace}
    proof {rustLeftBrace} reveal_with_fuel({itemSpec}, 1); {rustRightBrace}
    let capture_start = state.end;
    let prefix_limit = {execLimit};
    proof {rustLeftBrace}
        assert((prefix_limit as int) - (capture_start as int) <= 4);
    {rustRightBrace}
    let prefix = semantic_hex_prefix_summary(
        input,
        input_length,
        input_ascii,
        capture_start,
        prefix_limit,
    );
    let width = prefix.end - capture_start;
    if let Some(found) = search_match_terminal_from_prefix(
        input,
        capture_start,
        width,
        {renderedToken},
        {renderedLength},
        prefix_limit,
        prefix.end,
    ) {rustLeftBrace}
        {recordExecStatement}
        proof {rustLeftBrace}
            assert(found.end == prefix.end);
            reveal(terminal_matches_at);
            reveal(length_accepts);
            assert(capture_start < prefix.end);
        {rustRightBrace}
        return Some(prefix);
    {rustRightBrace}
    None
{rustRightBrace}"
        | none =>
            s!"#[inline(always)]
fn {itemExec}(
    input: &str,
    input_length: usize,
    input_ascii: bool,
    state: &mut SearchState,
) -> (result: bool)
    requires
        input@.len() < usize::MAX,
        input_length == input@.len(),
        input_ascii == input.is_ascii(),
        old(state).semantic_cache.matches_input(input@),
        search_state_bounded(old(state).deep_view(), input@.len()),
        old(state).storage_well_formed(),
        old(state).captures@.len() + {itemCaptureCount} <= {captureCapacity},
        old(state).markers.deep_view().len() <= {markerCapacity},
    ensures
        result ==> {itemSpec}(input@, old(state).deep_view())
            == Some(final(state).deep_view())
            && search_state_bounded(final(state).deep_view(), input@.len())
            && final(state).storage_well_formed()
            && final(state).captures@.len()
                == old(state).captures@.len() + {itemCaptureCount}
            && final(state).captures@.take(old(state).captures@.len() as int)
                == old(state).captures@
            && final(state).markers.deep_view().len()
                == old(state).markers.deep_view().len()
            && final(state).markers.deep_view() == old(state).markers.deep_view()
            && final(state).semantic_cache.matches_input(input@),
        !result ==> {itemSpec}(input@, old(state).deep_view()).is_none()
            && final(state).deep_view() == old(state).deep_view()
            && final(state).storage_well_formed()
            && final(state).semantic_cache.matches_input(input@),
{rustLeftBrace}
    proof {rustLeftBrace} reveal_with_fuel({itemSpec}, 1); {rustRightBrace}
    let prefix_limit = {execLimit};
    let prefix_end = search_token_prefix_end(
        input,
        input_length,
        input_ascii,
        state.end,
        prefix_limit,
        {renderedToken},
    );
    let width = prefix_end - state.end;
    if let Some(found) = search_match_terminal_from_prefix(
        input,
        state.end,
        width,
        {renderedToken},
        {renderedLength},
        prefix_limit,
        prefix_end,
    ) {rustLeftBrace}
        {recordExecStatement}
        return true;
    {rustRightBrace}
    false
{rustRightBrace}"
      let tailAccumulatorParameter :=
        if fusedCacheEntry?.isSome then
          ",\n    accumulator: &mut SemanticHexSequenceAccumulator"
        else ""
      let tailAccumulatorRequires :=
        if fusedCacheEntry?.isSome then
          "        old(accumulator).source_matches(input@),\n" ++
            "        old(accumulator).end == old(state).end,\n"
        else ""
      let tailAccumulatorEnsures :=
        if fusedCacheEntry?.isSome then
          "        final(accumulator).source_matches(input@),\n" ++
            "        final(accumulator).start == old(accumulator).start,\n" ++
            "        final(accumulator).end == final(state).end,\n"
        else ""
      let tailItemExecution :=
        if fusedCacheEntry?.isSome then
          s!"let group_start = found.end;
            search_advance_exec(state, group_start);
            match {itemExec}(input, input_length, input_ascii, state) {rustLeftBrace}
                Some(prefix) => {rustLeftBrace}
                    proof {rustLeftBrace}
                        assert(
                            {itemCaptureCount} * (remaining - 1)
                                + {itemCaptureCount}
                            == {itemCaptureCount} * remaining
                        );
                        reveal(literal_matches_at);
                        reveal_strlit({separatorLiteral});
                        assert({separatorLiteral}@.len() == 1);
                        assert(group_start == previous_end + 1);
                        assert(input@.subrange(
                            previous_end as int,
                            previous_end as int + 1,
                        ) == {separatorLiteral}@);
                        assert(input@[previous_end as int]
                            == {separatorLiteral}@[0]);
                        assert({separatorLiteral}@[0] == ':');
                        assert(input@[previous_end as int] == ':');
                    {rustRightBrace}
                    accumulator.push_group(Ghost(input@), group_start, prefix);
                    return {tailExec}(
                        input,
                        input_length,
                        input_ascii,
                        state,
                        remaining - 1,
                        count + 1,
                        accumulator,
                    );
                {rustRightBrace},
                None => {rustLeftBrace}{rustRightBrace},
            {rustRightBrace}"
        else
          s!"search_advance_exec(state, found.end);
            if {itemExec}(input, input_length, input_ascii, state) {rustLeftBrace}
                proof {rustLeftBrace}
                    assert(
                        {itemCaptureCount} * (remaining - 1)
                            + {itemCaptureCount}
                        == {itemCaptureCount} * remaining
                    );
                {rustRightBrace}
                return {tailExec}(
                    input,
                    input_length,
                    input_ascii,
                    state,
                    remaining - 1,
                    count + 1,
                );
            {rustRightBrace}"
      let firstItemExecution :=
        if fusedCacheEntry?.isSome then
          s!"let sequence_start = state.end;
    let first_prefix = match {itemExec}(input, input_length, input_ascii, state) {rustLeftBrace}
        Some(prefix) => prefix,
        None => {rustLeftBrace}
            search_restore_checkpoint_to_exec(
                state,
                checkpoint,
                Ghost(original_view),
            );
            return false;
        {rustRightBrace},
    {rustRightBrace};
    let mut semantic_accumulator = SemanticHexSequenceAccumulator::first(
        Ghost(input@),
        sequence_start,
        first_prefix,
    );"
        else
          s!"if !{itemExec}(input, input_length, input_ascii, state) {rustLeftBrace}
        search_restore_checkpoint_to_exec(
            state,
            checkpoint,
            Ghost(original_view),
        );
        return false;
    {rustRightBrace}"
      let tailAccumulatorArgument :=
        if fusedCacheEntry?.isSome then ",\n        &mut semantic_accumulator" else ""
      let semanticCacheWrite :=
        match fusedCacheEntry? with
        | some entry =>
            s!"    if let Some(cached_value) = CachedSemanticHexSequence::from_accumulator(
        Ghost(input@),
        semantic_accumulator,
    ) {rustLeftBrace}
        state.semantic_cache.{semanticCacheSetter entry}(Ghost(input@), cached_value);
    {rustRightBrace}
"
        | none => ""
      pure s!"pub closed spec fn {itemSpec}(
    input: Seq<char>,
    state: SearchStateSpec,
) -> Option<SearchStateSpec> {rustLeftBrace}
    let input_length = input.len() as int;
    let remaining = input_length - state.end;
    let limit = {specLimit};
    let end = search_token_prefix_end_spec(
        input,
        state.end,
        limit,
        {renderedToken},
    );
    let width = end - state.end;
    if terminal_matches_at(
        input,
        state.end,
        width,
        {renderedToken},
        {renderedLength},
    ) {rustLeftBrace}
        Some({recordSpecExpression})
    {rustRightBrace} else {rustLeftBrace}
        None
    {rustRightBrace}
{rustRightBrace}

{itemExecDeclaration}

pub closed spec fn {tailSpec}(
    input: Seq<char>,
    state: SearchStateSpec,
    remaining: nat,
    count: nat,
) -> SearchRepeatResultSpec
    decreases remaining,
{rustLeftBrace}
    if remaining == 0 {rustLeftBrace}
        SearchRepeatResultSpec {rustLeftBrace} state, count {rustRightBrace}
    {rustRightBrace} else if literal_matches_at(input, state.end, {separatorLiteral}@) {rustLeftBrace}
        let separated = search_advance(
            state,
            state.end + {separatorLiteral}@.len(),
        );
        match {itemSpec}(input, separated) {rustLeftBrace}
            Some(found) =>
                {tailSpec}(
                    input,
                    found,
                    (remaining - 1) as nat,
                    count + 1,
                ),
            None => SearchRepeatResultSpec {rustLeftBrace} state, count {rustRightBrace},
        {rustRightBrace}
    {rustRightBrace} else {rustLeftBrace}
        SearchRepeatResultSpec {rustLeftBrace} state, count {rustRightBrace}
    {rustRightBrace}
{rustRightBrace}

fn {tailExec}(
    input: &str,
    input_length: usize,
    input_ascii: bool,
    state: &mut SearchState,
    remaining: usize,
    count: usize{tailAccumulatorParameter},
) -> (result: usize)
    requires
        input@.len() < usize::MAX,
        input_length == input@.len(),
        input_ascii == input.is_ascii(),
        old(state).semantic_cache.matches_input(input@),
{tailAccumulatorRequires}        search_state_bounded(old(state).deep_view(), input@.len()),
        old(state).storage_well_formed(),
        old(state).captures@.len()
            + {itemCaptureCount} * remaining <= {captureCapacity},
        old(state).markers.deep_view().len() <= {markerCapacity},
        count + remaining < usize::MAX,
    ensures
        {tailSpec}(
            input@,
            old(state).deep_view(),
            remaining as nat,
            count as nat,
        ) == (SearchRepeatResultSpec {rustLeftBrace}
            state: final(state).deep_view(),
            count: result as nat,
        {rustRightBrace}),
        search_state_bounded(final(state).deep_view(), input@.len()),
        final(state).storage_well_formed(),
        final(state).captures@.len()
            == old(state).captures@.len()
                + {itemCaptureCount} * (result - count),
        final(state).captures@.take(old(state).captures@.len() as int)
            == old(state).captures@,
        final(state).markers.deep_view() == old(state).markers.deep_view(),
        final(state).semantic_cache.matches_input(input@),
{tailAccumulatorEnsures}        count <= result <= count + remaining,
    decreases remaining,
{rustLeftBrace}
    proof {rustLeftBrace} reveal_with_fuel({tailSpec}, 1); {rustRightBrace}
    if remaining == 0 {rustLeftBrace}
        return count;
    {rustRightBrace}
    let previous_end = state.end;
{separatorMatcherPrelude}    match {separatorMatcher}(
        input,
        input_length,
        input_ascii,
        state.end,
        {separatorLiteral},
    ) {rustLeftBrace}
        Some(found) => {rustLeftBrace}
            {tailItemExecution}
            search_restore_end_exec(state, previous_end);
        {rustRightBrace},
        None => {rustLeftBrace}{rustRightBrace},
    {rustRightBrace}
    count
{rustRightBrace}

pub closed spec fn {specName}(
    input: Seq<char>,
    state: SearchStateSpec,
) -> Option<SearchStateSpec> {rustLeftBrace}
    match {itemSpec}(input, search_save(state)) {rustLeftBrace}
        Some(first) => {rustLeftBrace}
            let repeated = {tailSpec}(input, first, {upper - 1}, 1);
            if {lower} <= repeated.count {rustLeftBrace}
                match search_close_count_capture(
                    repeated.state,
                    {renderedCountKey},
                    repeated.count as usize,
                ) {rustLeftBrace}
                    Some(closed) => {nextSpec}(input, closed),
                    None => None,
                {rustRightBrace}
            {rustRightBrace} else {rustLeftBrace}
                None
            {rustRightBrace}
        {rustRightBrace},
        None => None,
    {rustRightBrace}
{rustRightBrace}

#[verifier::rlimit(200)]
{inlineAttribute}fn {execName}(
    input: &str,
    input_length: usize,
    input_ascii: bool,
    state: &mut SearchState,
) -> (result: bool)
{contract}
{rustLeftBrace}
    let checkpoint = search_checkpoint(state);
    let ghost original_view = state.deep_view();
    proof {rustLeftBrace}
        reveal_with_fuel({specName}, 1);
    {rustRightBrace}
    search_save_exec(state);
    let ghost saved_view = state.deep_view();
    proof {rustLeftBrace}
        search_save_preserves_checkpoint(
            checkpoint,
            original_view,
            original_view,
        );
        assert(search_checkpoint_matches(
            checkpoint,
            original_view,
            saved_view,
        ));
    {rustRightBrace}
    {firstItemExecution}
    proof {rustLeftBrace}
        search_checkpoint_matches_transitive(
            checkpoint,
            original_view,
            saved_view,
            state.deep_view(),
        );
    {rustRightBrace}
    let ghost first_view = state.deep_view();
    let count = {tailExec}(
        input,
        input_length,
        input_ascii,
        state,
        {upper - 1},
        1{tailAccumulatorArgument},
    );
    proof {rustLeftBrace}
        search_checkpoint_matches_transitive(
            checkpoint,
            original_view,
            first_view,
            state.deep_view(),
        );
    {rustRightBrace}
    let ghost repeated_view = state.deep_view();
    if count < {lower} {rustLeftBrace}
        search_restore_checkpoint_to_exec(
            state,
            checkpoint,
            Ghost(original_view),
        );
        return false;
    {rustRightBrace}
    let ghost repeated_marker = state.deep_view().markers.last();
    if !search_close_count_capture_exec(
        state,
        {renderedCountKey},
        count,
        Ghost(input@.len()),
    ) {rustLeftBrace}
        search_restore_checkpoint_to_exec(
            state,
            checkpoint,
            Ghost(original_view),
        );
        return false;
    {rustRightBrace}
    proof {rustLeftBrace}
        assert(checkpoint.capture_length <= repeated_marker.capture_count);
        assert(repeated_marker.capture_count < repeated_marker.second_capture_count);
        assert(checkpoint.marker_length < repeated_view.markers.len());
        search_close_count_capture_preserves_checkpoint(
            checkpoint,
            original_view,
            repeated_view,
            {renderedCountKey},
            count,
            state.deep_view(),
        );
    {rustRightBrace}
{semanticCacheWrite}    if {nextExec}(input, input_length, input_ascii, state) {rustLeftBrace}
        true
    {rustRightBrace} else {rustLeftBrace}
        search_restore_checkpoint_to_exec(
            state,
            checkpoint,
            Ghost(original_view),
        );
        false
    {rustRightBrace}
{rustRightBrace}"
  | .choice _ first second =>
      let firstSpec := searchStateSpecFunction format first
      let firstExec := searchStateExecFunction format first
      let secondSpec := searchStateSpecFunction format second
      let secondExec := searchStateExecFunction format second
      pure s!"pub closed spec fn {specName}(
    input: Seq<char>,
    state: SearchStateSpec,
) -> Option<SearchStateSpec> {rustLeftBrace}
    match {firstSpec}(input, state) {rustLeftBrace}
        Some(found) => Some(found),
        None => {secondSpec}(input, state),
    {rustRightBrace}
{rustRightBrace}

{inlineAttribute}fn {execName}(
    input: &str,
    input_length: usize,
    input_ascii: bool,
    state: &mut SearchState,
) -> (result: bool)
{contract}
{rustLeftBrace}
    proof {rustLeftBrace} reveal_with_fuel({specName}, 1); {rustRightBrace}
    if {firstExec}(input, input_length, input_ascii, state) {rustLeftBrace}
        true
    {rustRightBrace} else {rustLeftBrace}
    {secondExec}(input, input_length, input_ascii, state)
    {rustRightBrace}
{rustRightBrace}"
  | .dispatch _ needle present absent =>
      let presentSpec := searchStateSpecFunction format present
      let presentExec := searchStateExecFunction format present
      let absentSpec := searchStateSpecFunction format absent
      let absentExec := searchStateExecFunction format absent
      let renderedLiteral := String.quote needle
      pure s!"pub closed spec fn {specName}(
    input: Seq<char>,
    state: SearchStateSpec,
) -> Option<SearchStateSpec> {rustLeftBrace}
    if search_contains_pair_from_spec(
        input,
        state.end,
        {renderedLiteral}@,
    ) {rustLeftBrace}
        match {presentSpec}(input, state) {rustLeftBrace}
            Some(found) => Some(found),
            None => {absentSpec}(input, state),
        {rustRightBrace}
    {rustRightBrace} else {rustLeftBrace}
        {absentSpec}(input, state)
    {rustRightBrace}
{rustRightBrace}

{inlineAttribute}fn {execName}(
    input: &str,
    input_length: usize,
    input_ascii: bool,
    state: &mut SearchState,
) -> (result: bool)
{contract}
{rustLeftBrace}
    proof {rustLeftBrace} reveal_with_fuel({specName}, 1); {rustRightBrace}
    if search_contains_pair_from(
        input,
        input_length,
        input_ascii,
        state.end,
        {renderedLiteral},
    ) {rustLeftBrace}
        if {presentExec}(input, input_length, input_ascii, state) {rustLeftBrace}
            true
        {rustRightBrace} else {rustLeftBrace}
            {absentExec}(input, input_length, input_ascii, state)
        {rustRightBrace}
    {rustRightBrace} else {rustLeftBrace}
        {absentExec}(input, input_length, input_ascii, state)
    {rustRightBrace}
{rustRightBrace}"

private def renderSearchMachineParser (format : FormatInput) (grammar : FlatGrammar)
    (program : SearchProgram) (semanticPlan? : Option ExecutableSemanticPlan) :
    Except String String := do
  let cacheEntries := (semanticPlan?.map ExecutableSemanticPlan.semanticCacheEntries).getD []
  let machine :=
    match semanticPlan? with
    | some semanticPlan =>
        lowerLiveSearchProgram grammar semanticPlan.captureSelectors program
    | none => lowerSearchProgram program
  let flattened ← flattenSearchMachineCode machine.code
  let incomingCount (id : Nat) : Nat :=
    flattened.nodes.foldl
      (fun total node => total + (node.successors.filter (· == id)).length)
      0
  let requirementsFor (id : Nat) : Nat × Nat :=
    match flattened.requirements.find? fun (foundId, _, _) => foundId == id with
    | some (_, captureNeed, markerNeed) => (captureNeed, markerNeed)
    | none => (0, 0)
  let declarations ← flattened.nodes.mapM fun node =>
    let (captureNeed, markerNeed) := requirementsFor node.id
    renderSearchNode format grammar cacheEntries flattened.nodes
      captureNeed markerNeed flattened.captureSlotCapacity flattened.markerCapacity
      (node.id != flattened.root && incomingCount node.id == 1)
      node
  let specFunction := functionName format.name "search_parse_candidate"
  let scanStateFunction := functionName format.name "scan_state"
  let recognizeFunction := functionName format.name "recognize"
  let parserFunction := functionName format.name "parse_candidate"
  let rootSpec := searchStateSpecFunction format flattened.root
  let rootExec := searchStateExecFunction format flattened.root
  let semanticRuntime := (semanticPlan?.map fun plan =>
    plan.runtimeSemanticBase ++ "\n\n" ++ renderRuntimeSemanticSupport plan ++ "\n\n" ++
      renderSemanticCacheSupport cacheEntries).getD ""
  let semanticCache := renderSemanticCache format cacheEntries
  let captureCapacity := max 1 flattened.captureSlotCapacity
  let semanticParser ← match semanticPlan? with
    | some plan => renderRuntimeSemanticParser format plan true captureCapacity
    | none => pure ""
  let markerCapacity := max 1 flattened.markerCapacity
  let instantiatedSearchTemplate :=
    (searchMachineParserTemplate.replace
      "__TRIPTYCH_CAPTURE_CAPACITY__" (toString captureCapacity)).replace
      "__TRIPTYCH_MARKER_CAPACITY__" (toString markerCapacity)
    |>.replace "__TRIPTYCH_SEMANTIC_CACHE_TYPE__" (semanticCacheType format)
  pure s!"// Generated by Triptych from `triptych {format.name}`.
// SearchPlan is verified-lowered to callback-free, literal-dispatched SearchMachine states.
// Semantic evaluation reads the fixed capture stack without materializing a heap candidate.
// This file is regenerated; it contains no external parser or manually supplied parser proof.

{runtimeParserTemplate}
verus! {rustLeftBrace}

{instantiatedSearchTemplate}

{semanticRuntime}

{semanticCache}

{String.intercalate "\n\n" declarations}

pub closed spec fn {specFunction}(input: Seq<char>) -> Option<CandidateSpec> {rustLeftBrace}
    if input.len() >= usize::MAX {rustLeftBrace}
        None
    {rustRightBrace} else {rustLeftBrace}
        let initial = SearchStateSpec {rustLeftBrace}
            end: 0,
            captures: seq![],
            markers: seq![],
        {rustRightBrace};
        match {rootSpec}(input, initial) {rustLeftBrace}
            Some(found) if found.end == input.len() && found.markers.len() == 0 =>
                Some(search_candidate_of(found)),
            _ => None,
        {rustRightBrace}
    {rustRightBrace}
{rustRightBrace}

#[inline(always)]
#[verifier::rlimit(1000)]
fn {scanStateFunction}(
    input: &str,
    input_length: usize,
    input_ascii: bool,
) -> (result: Option<SearchState>)
    requires
        input_length == input@.len(),
        input_ascii == input.is_ascii(),
    ensures
        match result {rustLeftBrace}
            Some(state) =>
                {specFunction}(input@) == Some(search_candidate_of(state.deep_view()))
                    && state.end == input@.len()
                    && state.markers.deep_view().len() == 0
                    && state.storage_well_formed()
                    && state.semantic_cache.matches_input(input@),
            None => {specFunction}(input@).is_none(),
        {rustRightBrace},
{rustLeftBrace}
    if input_length >= usize::MAX {rustLeftBrace}
        proof {rustLeftBrace} reveal_with_fuel({specFunction}, 1); {rustRightBrace}
        return None;
    {rustRightBrace}
    proof {rustLeftBrace} reveal_with_fuel({specFunction}, 1); {rustRightBrace}
    let mut initial = SearchState {rustLeftBrace}
        end: 0,
        captures: SearchCaptureStack::new(),
        markers: SearchMarkerStack::new(),
        semantic_cache: {semanticCacheType format}::new(Ghost(input@)),
    {rustRightBrace};
    let ghost initial_view = initial.deep_view();
    proof {rustLeftBrace}
        assert(initial_view == SearchStateSpec {rustLeftBrace}
            end: 0,
            captures: seq![],
            markers: seq![],
        {rustRightBrace});
    {rustRightBrace}
    if {rootExec}(input, input_length, input_ascii, &mut initial) {rustLeftBrace}
        let ghost found_view = initial.deep_view();
        proof {rustLeftBrace}
            assert({rootSpec}(input@, initial_view) == Some(found_view));
        {rustRightBrace}
        if initial.end != input_length || initial.markers.len() != 0 {rustLeftBrace}
            proof {rustLeftBrace}
                assert(
                    found_view.end != input@.len()
                        || found_view.markers.len() != 0
                );
                assert({specFunction}(input@).is_none());
            {rustRightBrace}
            return None;
        {rustRightBrace}
        proof {rustLeftBrace}
            assert({specFunction}(input@) == Some(search_candidate_of(found_view)));
            assert(initial.end == input@.len());
            assert(initial.markers.deep_view().len() == 0);
        {rustRightBrace}
        Some(initial)
    {rustRightBrace} else {rustLeftBrace}
        proof {rustLeftBrace}
            assert({rootSpec}(input@, initial_view).is_none());
            assert({specFunction}(input@).is_none());
        {rustRightBrace}
        None
    {rustRightBrace}
{rustRightBrace}

#[inline(always)]
pub fn {recognizeFunction}(input: &str) -> (result: Option<usize>)
    ensures
        match result {rustLeftBrace}
            Some(end) => {specFunction}(input@).is_some() && end == input@.len(),
            None => {specFunction}(input@).is_none(),
        {rustRightBrace},
{rustLeftBrace}
    let input_ascii = input.is_ascii();
    let input_length = search_input_length(input, input_ascii);
    let state = match {scanStateFunction}(input, input_length, input_ascii) {rustLeftBrace}
        Some(state) => state,
        None => return None,
    {rustRightBrace};
    proof {rustLeftBrace}
        assert({specFunction}(input@) == Some(search_candidate_of(state.deep_view())));
    {rustRightBrace}
    Some(state.end)
{rustRightBrace}

#[inline(always)]
pub fn {parserFunction}(input: &str) -> (result: Option<Candidate>)
    ensures
        match result {rustLeftBrace}
            Some(candidate) =>
                {specFunction}(input@) == Some(candidate.deep_view())
                    && candidate.end == input@.len(),
            None => {specFunction}(input@).is_none(),
        {rustRightBrace},
{rustLeftBrace}
    let input_ascii = input.is_ascii();
    let input_length = search_input_length(input, input_ascii);
    if input_length >= usize::MAX {rustLeftBrace}
        proof {rustLeftBrace} reveal_with_fuel({specFunction}, 1); {rustRightBrace}
        return None;
    {rustRightBrace};
    proof {rustLeftBrace}
        reveal_with_fuel({specFunction}, 1);
    {rustRightBrace}
    let mut initial = SearchState {rustLeftBrace}
        end: 0,
        captures: SearchCaptureStack::new(),
        markers: SearchMarkerStack::new(),
        semantic_cache: {semanticCacheType format}::new(Ghost(input@)),
    {rustRightBrace};
    let ghost initial_view = initial.deep_view();
    proof {rustLeftBrace}
        assert(initial_view == SearchStateSpec {rustLeftBrace}
            end: 0,
            captures: seq![],
            markers: seq![],
        {rustRightBrace});
    {rustRightBrace}
    if {rootExec}(input, input_length, input_ascii, &mut initial) {rustLeftBrace}
        let ghost found_view = initial.deep_view();
        proof {rustLeftBrace}
            assert({rootSpec}(input@, initial_view) == Some(found_view));
        {rustRightBrace}
        if initial.end != input_length || initial.markers.len() != 0 {rustLeftBrace}
            proof {rustLeftBrace}
                assert(
                    found_view.end != input@.len()
                        || found_view.markers.len() != 0
                );
                assert({specFunction}(input@).is_none());
            {rustRightBrace}
            return None;
        {rustRightBrace}
        let candidate = search_candidate_of_exec(initial);
        proof {rustLeftBrace}
            assert(candidate.deep_view() == search_candidate_of(found_view));
            assert({specFunction}(input@) == Some(candidate.deep_view()));
            assert(candidate.end == input@.len());
        {rustRightBrace}
        Some(candidate)
    {rustRightBrace} else {rustLeftBrace}
        proof {rustLeftBrace}
            assert({rootSpec}(input@, initial_view).is_none());
            assert({specFunction}(input@).is_none());
        {rustRightBrace}
        None
    {rustRightBrace}
{rustRightBrace}

{semanticPlan?.map (renderRuntimeSemanticSpec format) |>.getD ""}

{semanticParser}

{rustRightBrace} // verus!
"

private def renderPlanTokenClass : TokClass → String
  | .digit => "PlanTokenClass::Digit"
  | .hexDigit => "PlanTokenClass::HexDigit"
  | .bit => "PlanTokenClass::Bit"
  | .asciiRange lower upper =>
      "PlanTokenClass::AsciiRange { lower: " ++ toString lower ++
        ", upper: " ++ toString upper ++ " }"

private def captureField (capture : String) : String :=
  snakeCase (Triptych.surfaceBinder capture)

private def parseSpecType (format : FormatInput) : String :=
  typeName format.name ++ "ParseSpec"

private def parseResultType (format : FormatInput) : String :=
  typeName format.name ++ "ParseResult"

private def parsePlanFunction (format : FormatInput) : String :=
  functionName format.name "parse_plan"

private def parseCandidateFunction (format : FormatInput) : String :=
  functionName format.name "parse_candidate"

private def parseViewFunction (format : FormatInput) : String :=
  functionName format.name "parse_view"

private def parseFunction (format : FormatInput) : String :=
  functionName format.name "parse"

private def parsePlanCompletenessFunction (format : FormatInput) : String :=
  functionName format.name "is_wf_implies_parse_plan"

private def grammarWfFunction (format : FormatInput) : String :=
  productionName format.name format.grammar.start

private def viewType (format : FormatInput) : String :=
  typeName format.name ++ "View"

private def matchesViewFunction (format : FormatInput) : String :=
  functionName format.name "matches_view"

private def positionName (index : Nat) : String :=
  s!"position_{index}"

private structure FixedPointSemanticPlan where
  signCapture : String
  naturalCapture : String
  fractionCapture : String
  scale : Nat
  deriving Repr, Inhabited, DecidableEq

private def fixedPointValue? : ValExpr → Option FixedPointSemanticPlan
  | .mul (.signOf signCapture)
      (.add
        (.mul (.nat naturalCapture) (.pow (.lit 10) (.lit scale)))
        (.mul (.nat fractionCapture)
          (.pow (.lit 10) (.sub (.lit fractionScale) (.len fractionLengthCapture))))) =>
      if scale < 0 || fractionScale != scale || fractionLengthCapture != fractionCapture then
        none
      else
        some
          { signCapture
            naturalCapture
            fractionCapture
            scale := scale.toNat }
  | _ => none

private def isInt64Bounds (expression : ValExpr) : Constraint → Bool
  | .and (.le (.lit lower) lowerValue) (.le upperValue (.lit upper)) =>
      lower == (-9223372036854775808) &&
        upper == 9223372036854775807 &&
        lowerValue == expression && upperValue == expression
  | _ => false

private def captureSlot? (program : CursorProgram) (capture : String) : Option String :=
  (program.captureKeys.find? fun (_, keys) => keys.contains capture).map (·.1)

private def soleProductionItem? (grammar : Grammar) (name : String) : Option SymItem := do
  let production ← grammar.prod? name
  let [alternative] := production.alts | none
  let [item] := alternative | none
  pure item

private def isSignProduction (grammar : Grammar) (name : String) : Bool :=
  match soleProductionItem? grammar name with
  | some ⟨.lit "-", true⟩ => true
  | _ => false

private def digitRunBounds? (grammar : Grammar) (name : String) :
    Option (Nat × Option Nat) := do
  let ⟨.term .digit length, false⟩ ← soleProductionItem? grammar name
    | none
  match length with
  | .atLeastOne => some (1, none)
  | .exactly width => some (width, some width)
  | .between lower upper => some (lower, some upper)

private def fixedPointSemanticPlan? (format : FormatInput) (program : CursorProgram) :
    Option FixedPointSemanticPlan := do
  guard (format.ofSpec == "Int64.ofInt")
  guard format.wfConstraints.isEmpty
  guard (format.valueConstraints == [.and
    (.le (.lit (-9223372036854775808)) format.valueExpr)
    (.le format.valueExpr (.lit 9223372036854775807))])
  guard (format.valueConstraints.all (isInt64Bounds format.valueExpr))
  let plan ← fixedPointValue? format.valueExpr
  guard (plan.scale ≤ 18)
  let signSlot ← captureSlot? program plan.signCapture
  let naturalSlot ← captureSlot? program plan.naturalCapture
  let fractionSlot ← captureSlot? program plan.fractionCapture
  guard (isSignProduction format.grammar signSlot)
  let (naturalLower, _) ← digitRunBounds? format.grammar naturalSlot
  guard (1 ≤ naturalLower)
  let (fractionLower, some fractionUpper) ←
    digitRunBounds? format.grammar fractionSlot | none
  guard (1 ≤ fractionLower && fractionUpper ≤ plan.scale)
  pure plan

private def renderRunCondition (run : CursorRun) (start finish : String) : String :=
  let width := s!"({finish} - {start})"
  match run with
  | .fixed widthValue => s!"{width} == {widthValue}"
  | .greedyBetween lower upper => s!"{lower} <= {width} && {width} <= {upper}"
  | .greedyAtLeastOne => s!"1 <= {width}"

private def renderParseSpecResult (format : FormatInput) (program : CursorProgram)
    (position : String) : String :=
  let fields := program.captures.flatMap fun capture =>
    let field := captureField capture
    [s!"{field}_start: {field}_start", s!"{field}_end: {field}_end"]
  "Some(" ++ parseSpecType format ++ " {\n" ++
    indentText 1 (String.intercalate ",\n" (s!"end: {position}" :: fields)) ++ "\n})"

private def verusCharacterLiteral (character : Char) : String :=
  "'\\u{" ++ String.ofList (Nat.toDigits 16 character.toNat) ++ "}'"
private def renderParseExecResult (format : FormatInput) (program : CursorProgram)
    (position : String) : String :=
  let fields := program.captures.flatMap fun capture =>
    let field := captureField capture
    [s!"{field}_start", s!"{field}_end"]
  "Some(" ++ parseResultType format ++ " {\n" ++
    indentText 1 (String.intercalate ",\n" (s!"end: {position}" :: fields)) ++ "\n})"

private def renderSpecOps (format : FormatInput) (program : CursorProgram) :
    List CursorOp → Nat → String → String
  | [], _, position =>
      "if " ++ position ++ " == (input.len() as int) {\n" ++
        indentText 1 (renderParseSpecResult format program position) ++
        "\n} else {\n    None\n}"
  | .beginCapture capture _ :: rest, index, position =>
      let field := captureField capture
      s!"let {field}_start = {position};\n" ++
        renderSpecOps format program rest index position
  | .endCapture capture :: rest, index, position =>
      let field := captureField capture
      s!"let {field}_end = {position};\n" ++
        renderSpecOps format program rest index position
  | .consumeOptional character :: rest, index, position =>
      let next := positionName (index + 1)
      s!"let {next} = if {position} < (input.len() as int) && " ++
        s!"(input[{position}] as int) == {character.toNat} " ++ "{\n" ++
        s!"    {position} + 1\n" ++
        "} else {\n" ++
        s!"    {position}\n" ++
        "};\n" ++
        renderSpecOps format program rest (index + 1) next
  | .expect character :: rest, index, position =>
      let next := positionName (index + 1)
      s!"if {position} < (input.len() as int) && " ++
        s!"(input[{position}] as int) == {character.toNat} " ++
        "{\n" ++
        indentText 1
          (s!"let {next} = {position} + 1;\n" ++
            renderSpecOps format program rest (index + 1) next) ++
        "\n} else {\n    None\n}"
  | .consumeRun token (.fixed width) :: rest, index, position =>
      let next := positionName (index + 1)
      let limit := positionName (index + 1) ++ "_limit"
      s!"if {position} + {width} <= (input.len() as int) " ++ "{\n" ++
        indentText 1
          (s!"let {limit} = {position} + {width};\n" ++
            s!"let {next} = plan_scan_token_end(input, {position}, {limit}, " ++
            renderPlanTokenClass token ++ ");\n" ++
            s!"if {next} == {limit} " ++ "{\n" ++
            indentText 1 (renderSpecOps format program rest (index + 1) next) ++
            "\n} else {\n    None\n}") ++
        "\n} else {\n    None\n}"
  | .consumeRun token run :: rest, index, position =>
      let next := positionName (index + 1)
      let condition := renderRunCondition run position next
      s!"let {next} = plan_scan_token_end(input, {position}, (input.len() as int), " ++
        renderPlanTokenClass token ++ ");\n" ++
        s!"if {condition} " ++ "{\n" ++
        indentText 1 (renderSpecOps format program rest (index + 1) next) ++
        "\n} else {\n    None\n}"

private def renderExecOps (format : FormatInput) (program : CursorProgram)
    (successProof : String) :
    List CursorOp → Nat → String → String
  | [], _, position =>
      "if " ++ position ++ " == input_length {\n" ++
        indentText 1
          ((if successProof.isEmpty then "" else successProof ++ "\n") ++
            renderParseExecResult format program position) ++
        "\n} else {\n    None\n}"
  | .beginCapture capture _ :: rest, index, position =>
      let field := captureField capture
      s!"let {field}_start = {position};\n" ++
        renderExecOps format program successProof rest index position
  | .endCapture capture :: rest, index, position =>
      let field := captureField capture
      s!"let {field}_end = {position};\n" ++
        renderExecOps format program successProof rest index position
  | .consumeOptional character :: rest, index, position =>
      let next := positionName (index + 1)
      s!"let {next} = if {position} < input_length && " ++
        s!"plan_ascii_character_at(input, {position}) == {character.toNat}u8 " ++ "{\n" ++
        s!"    {position} + 1\n" ++
        "} else {\n" ++
        s!"    {position}\n" ++
        "};\n" ++
        renderExecOps format program successProof rest (index + 1) next
  | .expect character :: rest, index, position =>
      let next := positionName (index + 1)
      s!"if {position} < input_length && " ++
        s!"plan_ascii_character_at(input, {position}) == {character.toNat}u8 " ++ "{\n" ++
        indentText 1
          (s!"let {next} = {position} + 1;\n" ++
            renderExecOps format program successProof rest (index + 1) next) ++
        "\n} else {\n    None\n}"
  | .consumeRun token (.fixed width) :: rest, index, position =>
      let next := positionName (index + 1)
      let limit := positionName (index + 1) ++ "_limit"
      s!"if {position} <= input_length && {width} <= input_length - {position} " ++ "{\n" ++
        indentText 1
          (s!"let {limit} = {position} + {width};\n" ++
            s!"let {next} = plan_scan_token_end_exec(input, {position}, {limit}, " ++
            renderPlanTokenClass token ++ ");\n" ++
            s!"if {next} == {limit} " ++ "{\n" ++
            indentText 1
              (renderExecOps format program successProof rest (index + 1) next) ++
            "\n} else {\n    None\n}") ++
        "\n} else {\n    None\n}"
  | .consumeRun token run :: rest, index, position =>
      let next := positionName (index + 1)
      let condition := renderRunCondition run position next
      s!"let {next} = plan_scan_token_end_exec(input, {position}, input_length, " ++
        renderPlanTokenClass token ++ ");\n" ++
        s!"if {condition} " ++ "{\n" ++
        indentText 1 (renderExecOps format program successProof rest (index + 1) next) ++
        "\n} else {\n    None\n}"

private def renderParseStructures (format : FormatInput) (program : CursorProgram) : String :=
  let leftBrace := "{"
  let rightBrace := "}"
  let specFields := program.captures.flatMap fun capture =>
    let field := captureField capture
    [s!"pub {field}_start: int", s!"pub {field}_end: int"]
  let execFields := program.captures.flatMap fun capture =>
    let field := captureField capture
    [s!"pub {field}_start: usize", s!"pub {field}_end: usize"]
  let viewFields := program.captures.flatMap fun capture =>
    let field := captureField capture
    [s!"{field}_start: self.{field}_start as int",
     s!"{field}_end: self.{field}_end as int"]
  "#[verifier::ext_equal]\n" ++
    s!"pub struct {parseSpecType format} " ++ leftBrace ++ "\n" ++
    indentText 1 (String.intercalate ",\n" (["pub end: int"] ++ specFields)) ++ "\n" ++
    rightBrace ++ "\n\n" ++
    "#[derive(Copy, Clone)]\n" ++
    s!"pub struct {parseResultType format} " ++ leftBrace ++ "\n" ++
    indentText 1 (String.intercalate ",\n" (["pub end: usize"] ++ execFields)) ++ "\n" ++
    rightBrace ++ "\n\n" ++
    s!"impl DeepView for {parseResultType format} " ++ leftBrace ++ "\n" ++
    s!"    type V = {parseSpecType format};\n\n" ++
    s!"    open spec fn deep_view(&self) -> {parseSpecType format} " ++ leftBrace ++ "\n" ++
    s!"        {parseSpecType format} " ++ leftBrace ++ "\n" ++
    indentText 3 (String.intercalate ",\n" (["end: self.end as int"] ++ viewFields)) ++ "\n" ++
    "        " ++ rightBrace ++ "\n" ++
    "    " ++ rightBrace ++ "\n" ++
    rightBrace

private def renderParseView (format : FormatInput) (program : CursorProgram) : String :=
  let viewType := typeName format.name ++ "View"
  let fields := fieldsFor format
  let fieldInitializers := fields.map fun field =>
    let slot := (captureSlot? program field.capture).getD field.capture
    let sourceField := captureField slot
    s!"{field.ident}: input.subrange(parsed.{sourceField}_start, parsed.{sourceField}_end)"
  "pub open spec fn " ++ parseViewFunction format ++
    s!"(input: Seq<char>, parsed: {parseSpecType format}) -> {viewType} " ++ "{\n" ++
    indentText 1
      (viewType ++ " {\n" ++
        indentText 1 (String.intercalate ",\n" ("input" :: fieldInitializers)) ++ "\n}") ++
    "\n}"

private def renderParseViewProof (format : FormatInput) (program : CursorProgram)
    (rootStop viewProof : String) : String :=
  let parsedFields := program.captures.flatMap fun capture =>
    let field := captureField capture
    [s!"{field}_start: {field}_start as int", s!"{field}_end: {field}_end as int"]
  let parsedExpression :=
    parseSpecType format ++ " {\n" ++
      indentText 1
        (String.intercalate ",\n" (s!"end: {rootStop} as int" :: parsedFields)) ++ "\n}"
  String.intercalate "\n"
    [ s!"let parsed_spec = {parsedExpression};",
      s!"reveal({parseViewFunction format});",
      s!"let parsed_view = {parseViewFunction format}(input@, parsed_spec);",
      viewProof,
      s!"reveal({functionName format.name "matches_view"});",
      s!"assert({functionName format.name "matches_view"}(" ++
        "input@, parsed_view));" ]

private def renderDigitCaptureFacts (format : FormatInput) (_program : CursorProgram)
    (capture slot : String) : String :=
  let field := fieldIdent (fieldsFor format) capture
  let slotField := captureField slot
  let wf := productionName format.name slot
  String.intercalate "\n"
    [ s!"reveal({wf});",
      s!"let {field}_digits = choose|digits: Seq<char>|",
      s!"    parsed_view.{field} == digits &&",
      "        1 <= digits.len() &&",
      "        forall|i: int| #![auto] 0 <= i < digits.len() ==>",
      "            triptych_is_digit(digits[i]);",
      s!"assert(parsed_view.{field} == {field}_digits);",
      s!"assert forall|index: int| parsed.{slotField}_start <= index < " ++
        s!"parsed.{slotField}_end implies",
      "    #[trigger] triptych_is_digit(input@[index]) by {",
      s!"    let local = index - parsed.{slotField}_start;",
      s!"    assert(parsed_view.{field}[local] == input@[index]);",
      s!"    assert(triptych_is_digit({field}_digits[local]));",
      "}" ]

private def renderFixedPointSemanticParser (format : FormatInput) (program : CursorProgram)
    (plan : FixedPointSemanticPlan) : String :=
  let signSlot := (captureSlot? program plan.signCapture).getD plan.signCapture
  let naturalSlot := (captureSlot? program plan.naturalCapture).getD plan.naturalCapture
  let fractionSlot := (captureSlot? program plan.fractionCapture).getD plan.fractionCapture
  let signField := captureField signSlot
  let naturalField := captureField naturalSlot
  let fractionField := captureField fractionSlot
  let viewType := typeName format.name ++ "View"
  let semanticFields := fieldsFor format
  let signViewField := fieldIdent semanticFields plan.signCapture
  let naturalViewField := fieldIdent semanticFields plan.naturalCapture
  let fractionViewField := fieldIdent semanticFields plan.fractionCapture
  let parsedType := parseResultType format
  let formatPrefix := snakeCase format.name
  let matchesView := formatPrefix ++ "_matches_view"
  let viewValid := formatPrefix ++ "_view_valid"
  let viewDenotation := formatPrefix ++ "_view_denotation"
  let viewRuntimeSafe := formatPrefix ++ "_view_runtime_safe"
  let isValid := formatPrefix ++ "_is_valid"
  let naturalFacts :=
    renderDigitCaptureFacts format program plan.naturalCapture naturalSlot
  let fractionFacts :=
    renderDigitCaptureFacts format program plan.fractionCapture fractionSlot
  let minusLiteral := "'\\u{2d}'"
  let leftBrace := "{"
  let rightBrace := "}"
  s!"
{checkedSemanticTemplate}

pub open spec fn {viewRuntimeSafe}(view: {viewType}) -> bool {leftBrace}
    let natural = triptych_nat_of(view.{naturalViewField});
    let fraction = triptych_nat_of(view.{fractionViewField});
    let natural_scale = triptych_int_pow(10, {plan.scale});
    let fraction_scale =
        triptych_int_pow(10, {plan.scale} - view.{fractionViewField}.len());
    let scaled_natural = natural * natural_scale;
    let scaled_fraction = fraction * fraction_scale;
    let magnitude = scaled_natural + scaled_fraction;
    natural <= u64::MAX
        && fraction <= u64::MAX
        && natural_scale <= u64::MAX
        && fraction_scale <= u64::MAX
        && scaled_natural <= u64::MAX
        && scaled_fraction <= u64::MAX
        && magnitude <= u64::MAX
{rightBrace}

/// Parse a complete input through grammar recognition, semantic evaluation, constraints, and
/// the declared `Int64.ofInt` conversion.
#[inline(always)]
pub fn {parseFunction format}(input: &str) -> (result: Option<i64>)
    ensures
        match result {leftBrace}
            Some(value) =>
                match {parsePlanFunction format}(input@) {leftBrace}
                    Some(parsed) => {leftBrace}
                        let view = {parseViewFunction format}(input@, parsed);
                        {viewValid}(view)
                            && {viewDenotation}(view) == value as int
                    {rightBrace},
                    None => false,
                {rightBrace},
            None =>
                match {parsePlanFunction format}(input@) {leftBrace}
                    Some(parsed) => {leftBrace}
                        let view = {parseViewFunction format}(input@, parsed);
                        !{viewRuntimeSafe}(view) || !{viewValid}(view)
                    {rightBrace},
                    None => true,
                {rightBrace},
        {rightBrace},
{leftBrace}
    let parsed: {parsedType} = match {parseCandidateFunction format}(input) {leftBrace}
        Some(parsed) => parsed,
        None => return None,
    {rightBrace};
    let ghost parsed_view =
        {parseViewFunction format}(input@, parsed.deep_view());
    proof {leftBrace}
        broadcast use lemma_seq_subrange_index;
        reveal({matchesView});
        assert({productionName format.name signSlot}(parsed_view.{signViewField}));
        reveal({productionName format.name signSlot});
        let {signViewField}_literal = choose|literal: Seq<char>|
            parsed_view.{signViewField} == literal
                && (literal.len() == 0 || literal == seq![{minusLiteral}]);
        assert(parsed_view.{signViewField} == {signViewField}_literal);
{indentText 2 naturalFacts}
{indentText 2 fractionFacts}
    {rightBrace}
    let natural = triptych_checked_nat_range(
        input,
        parsed.{naturalField}_start,
        parsed.{naturalField}_end,
    );
    let fraction = triptych_checked_nat_range(
        input,
        parsed.{fractionField}_start,
        parsed.{fractionField}_end,
    );
    let fraction_length = parsed.{fractionField}_end - parsed.{fractionField}_start;
    if fraction_length > {plan.scale} {leftBrace}
        return None;
    {rightBrace}
    let natural_scale = triptych_checked_pow10({plan.scale});
    let fraction_scale = triptych_checked_pow10({plan.scale} - fraction_length);
    let scaled_natural = natural.mul_checked(&natural_scale);
    let scaled_fraction = fraction.mul_checked(&fraction_scale);
    let magnitude = scaled_natural.add_checked(&scaled_fraction);
    let unsigned = match magnitude.to_option() {leftBrace}
        Some(value) => value,
        None => return None,
    {rightBrace};
    let negative = parsed.{signField}_end > parsed.{signField}_start;
    let value: i64;
    if negative {leftBrace}
        if unsigned > 9223372036854775808u64 {leftBrace}
            return None;
        {rightBrace}
        if unsigned == 9223372036854775808u64 {leftBrace}
            value = i64::MIN;
            proof {leftBrace}
                assert(value as int == -(unsigned as int));
            {rightBrace}
        {rightBrace} else {leftBrace}
            value = -(unsigned as i64);
            proof {leftBrace}
                assert(value as int == -(unsigned as int));
            {rightBrace}
        {rightBrace}
    {rightBrace} else {leftBrace}
        if unsigned > i64::MAX as u64 {leftBrace}
            return None;
        {rightBrace}
        value = unsigned as i64;
        proof {leftBrace}
            assert(value as int == unsigned as int);
        {rightBrace}
    {rightBrace}
    proof {leftBrace}
        reveal({parseViewFunction format});
        assert(natural@ as int == triptych_nat_of(parsed_view.{naturalViewField}));
        assert(fraction@ as int == triptych_nat_of(parsed_view.{fractionViewField}));
        assert(natural_scale@ as int == triptych_int_pow(10, {plan.scale}));
        assert(fraction_length as int == parsed_view.{fractionViewField}.len());
        assert(fraction_scale@ as int
            == triptych_int_pow(10, {plan.scale} - parsed_view.{fractionViewField}.len()));
        assert(scaled_natural@ as int
            == triptych_nat_of(parsed_view.{naturalViewField})
                * triptych_int_pow(10, {plan.scale}));
        assert(scaled_fraction@ as int
            == triptych_nat_of(parsed_view.{fractionViewField})
                * triptych_int_pow(
                    10,
                    {plan.scale} - parsed_view.{fractionViewField}.len(),
                ));
        assert(magnitude@ as int
            == triptych_nat_of(parsed_view.{naturalViewField})
                    * triptych_int_pow(10, {plan.scale})
                + triptych_nat_of(parsed_view.{fractionViewField})
                    * triptych_int_pow(
                        10,
                        {plan.scale} - parsed_view.{fractionViewField}.len(),
                    ));
        assert(magnitude@ == unsigned);
        reveal({viewDenotation});
        reveal({functionName format.name "value"});
        if negative {leftBrace}
            assert(parsed_view.{signViewField}.len() > 0);
            assert(parsed_view.{signViewField} == seq![{minusLiteral}]);
            reveal(triptych_sign_of);
            assert(triptych_sign_of(parsed_view.{signViewField}) == -1);
            assert({viewDenotation}(parsed_view) == -(magnitude@ as int));
            assert({viewDenotation}(parsed_view) == value as int);
        {rightBrace} else {leftBrace}
            assert(parsed_view.{signViewField}.len() == 0);
            reveal(triptych_sign_of);
            assert(triptych_sign_of(parsed_view.{signViewField}) == 1);
            assert({viewDenotation}(parsed_view) == magnitude@ as int);
            assert({viewDenotation}(parsed_view) == value as int);
        {rightBrace}
        assert({viewDenotation}(parsed_view) == value as int);
        reveal({viewValid});
        reveal({functionName format.name "view_constraints"});
        reveal({functionName format.name "constraints"});
        assert({viewValid}(parsed_view));
        reveal({isValid});
        reveal({functionName format.name "is_wf"});
        reveal({functionName format.name "satisfies_constraints"});
        assert({isValid}(input@));
        assert(exists|view: {viewType}|
            {matchesView}(input@, view)
                && {viewValid}(view)
                && {viewDenotation}(view) == value as int) by {leftBrace}
            assert({matchesView}(input@, parsed_view));
        {rightBrace}
    {rightBrace}
    Some(value)
{rightBrace}
"

private def instantiateDirectParser (format : FormatInput) (program : CursorProgram)
    (rootStop successProof viewProof completenessProof : String) : String :=
  let leftBrace := "{"
  let rightBrace := "}"
  let specBody :=
    "if !is_ascii_chars(input) {\n    None\n} else {\n" ++
      indentText 1
        ("let position_0: int = 0;\n" ++
          renderSpecOps format program program.operations 0 "position_0") ++
      "\n}"
  let execBody :=
    "proof {\n" ++
      s!"    if {grammarWfFunction format}(input@) " ++ "{\n" ++
      s!"        {parsePlanCompletenessFunction format}(input@);\n" ++
      "    }\n" ++
      "}\n" ++
      "if !input.is_ascii() {\n    return None;\n}\n" ++
      "proof {\n    broadcast use is_ascii_spec_bytes;\n}\n" ++
      "let input_length = input.unicode_len();\n" ++
      "let position_0 = 0usize;\n" ++
      renderExecOps format program
        (successProof ++ "\nproof {\n" ++
          indentText 1 (renderParseViewProof format program rootStop viewProof) ++ "\n}")
        program.operations 0 "position_0"
  s!"// Generated by Triptych from `triptych {format.name}`.
// ScanPlan is verified-lowered to CursorProgram, which is compiled away.
// This file is regenerated; it contains no external parser or manually supplied parser proof.

{directParserTemplate}

{renderParseStructures format program}

{renderParseView format program}

pub open spec fn {parsePlanFunction format}(input: Seq<char>)
    -> Option<{parseSpecType format}>
{leftBrace}
{indentText 1 specBody}
{rightBrace}

{completenessProof}

/// Direct single-pass parser generated from the format's verified-lowered CursorProgram.
#[inline(always)]
#[verifier::rlimit(20)]
pub fn {parseCandidateFunction format}(input: &str)
    -> (result: Option<{parseResultType format}>)
    ensures
        match result {leftBrace}
            Some(parsed) =>
                {parsePlanFunction format}(input@) == Some(parsed.deep_view())
                    && {grammarWfFunction format}(input@)
                    && {matchesViewFunction format}(
                        input@,
                        {parseViewFunction format}(input@, parsed.deep_view()),
                    ),
            None =>
                {parsePlanFunction format}(input@).is_none()
                    && !{grammarWfFunction format}(input@),
        {rightBrace},
{leftBrace}
{indentText 1 execBody}
{rightBrace}

{match fixedPointSemanticPlan? format program with
 | some semanticPlan => renderFixedPointSemanticParser format program semanticPlan
 | none => ""}

{rightBrace} // verus!
"

private def textLength (expression : IR.Expr) : IR.Expr :=
  .textLen expression

private def tokenRunCondition (token : TokClass) (length : LenSpec)
    (input : IR.Expr) : IR.Expr :=
  let size := textLength input
  let lengthCondition := match length with
    | .exactly width => .intEq size (.intLit (Int.ofNat width))
    | .between lower upper =>
        .boolAnd
          (.intLe (.intLit (Int.ofNat lower)) size)
          (.intLe size (.intLit (Int.ofNat upper)))
    | .atLeastOne => .intLe (.intLit 1) size
  let index : IR.Expr := .var "i"
  let inRange :=
    .boolAnd (.intLe (.intLit 0) index) (.intLt index size)
  let charactersValid :=
    .forallE [{ name := "i", ty := .int }] true
      (.boolImplies inRange (.isToken token (.textIndex input index)))
  .boolAnd lengthCondition charactersValid

private def charEq (expression : IR.Expr) (character : Char) : IR.Expr :=
  .byteEq expression (.byteLit character.toNat)

private def stringHexCondition (expression : IR.Expr) : IR.Expr :=
  let numericValue := .byteToInt expression
  .orAll
    [ .boolAnd
        (.intLe (.intLit 48) numericValue) (.intLe numericValue (.intLit 57)),
      .boolAnd
        (.intLe (.intLit 65) numericValue) (.intLe numericValue (.intLit 70)),
      .boolAnd
        (.intLe (.intLit 97) numericValue) (.intLe numericValue (.intLit 102)) ]

private def stringTailName : String := "triptych_string_tail"
private def stringLiteralName : String := "triptych_is_string_literal"

private def grammarBoolFunction (name : String) (params : List IR.Param) (body : IR.Expr)
    (doc : Option String := none) : IR.Decl :=
  .function { name, params, returnType := .bool, body, doc }

private def stringGrammarDeclarations : List IR.Decl :=
  let input : IR.Expr := .var "input"
  let index : IR.Expr := .var "index"
  let limit : IR.Expr := .var "limit"
  let one : IR.Expr := .intLit 1
  let next := .intAdd index one
  let characterAt (position : IR.Expr) := IR.Expr.textIndex input position
  let whitespace (position : IR.Expr) :=
    IR.Expr.call "is_white_space" [characterAt position]
  let escaped := characterAt next
  let simpleEscape : IR.Expr :=
    IR.Expr.orAll
      [charEq escaped '\\', charEq escaped '"', charEq escaped '\'',
       charEq escaped 'r', charEq escaped 'n', charEq escaped 't']
  let xEscape : IR.Expr :=
    IR.Expr.boolAnd (charEq escaped 'x')
      (.boolAnd
        (.intLt (.intAdd index (.intLit 3)) limit)
        (.boolAnd
          (stringHexCondition (characterAt (.intAdd index (.intLit 2))))
          (stringHexCondition (characterAt (.intAdd index (.intLit 3))))))
  let uEscape : IR.Expr :=
    IR.Expr.boolAnd (charEq escaped 'u')
      (.boolAnd
        (.intLt (.intAdd index (.intLit 5)) limit)
        (.andAll
          [ stringHexCondition (characterAt (.intAdd index (.intLit 2))),
            stringHexCondition (characterAt (.intAdd index (.intLit 3))),
            stringHexCondition (characterAt (.intAdd index (.intLit 4))),
            stringHexCondition (characterAt (.intAdd index (.intLit 5))) ]))
  let escapedTail : IR.Expr :=
    IR.Expr.ifThenElse simpleEscape
      (.call stringTailName [input, .intAdd index (.intLit 2), limit])
      (.ifThenElse xEscape
        (.call stringTailName [input, .intAdd index (.intLit 4), limit])
        (.ifThenElse uEscape
          (.call stringTailName [input, .intAdd index (.intLit 6), limit])
          (.ifThenElse (whitespace next)
            (.call stringTailName [input, .intAdd index (.intLit 2), limit])
            (.boolLit false))))
  let stringTail :=
    grammarBoolFunction stringTailName
      [{ name := "input", ty := .text }, { name := "index", ty := .int },
       { name := "limit", ty := .int }]
      (.ifThenElse (.intGe index limit) (.boolLit false)
        (.ifThenElse (charEq (characterAt index) '"') (.boolLit true)
          (.ifThenElse (.intGe next limit) (.boolLit false)
            (.ifThenElse (charEq (characterAt index) '\\') escapedTail
              (.call stringTailName [input, next, limit])))))
  let length : IR.Expr := .textLen input
  let stringLiteral :=
    grammarBoolFunction stringLiteralName [{ name := "input", ty := .text }]
      (.ifThenElse (.intGt length (.intLit 0))
        (.ifThenElse (charEq (characterAt (.intLit 0)) 'r') (.boolLit true)
          (.call stringTailName [input, .intLit 1, length]))
        (.boolLit false))
  let addContracts : IR.Decl → IR.Decl
    | .function function =>
        if function.name == stringTailName then
          .function
            { function with
              recommends :=
                [.boolAnd
                  (.boolAnd (.intLe (.intLit 0) index) (.intLe index limit))
                  (.intLe limit (.textLen input))]
              decreases := some (.intSub limit index) }
        else
          .function function
    | declaration => declaration
  [stringTail, stringLiteral].map addContracts

private def indexOfSym? (needle : Sym) : List Sym → Option Nat
  | [] => none
  | symbol :: rest =>
      if symbol == needle then some 0 else (indexOfSym? needle rest).map (· + 1)

private def repetitionFunctionName (formatName : String) (repetitions : List Sym)
    (symbol : Sym) : String :=
  let index := (indexOfSym? symbol repetitions).getD 0
  functionName formatName s!"rep_{index}_matches"

private def repetitionCountFunctionName (formatName : String) (repetitions : List Sym)
    (symbol : Sym) : String :=
  let index := (indexOfSym? symbol repetitions).getD 0
  functionName formatName s!"rep_{index}_matches_count"

private def symbolCondition (formatName : String) (repetitions : List Sym) (symbol : Sym)
    (input : IR.Expr) : IR.Expr :=
  match symbol with
  | .lit literal => .textEq input (.textLit literal)
  | .ref name => .call (productionName formatName name) [input]
  | .term token length => tokenRunCondition token length input
  | .str => .call stringLiteralName [input]
  | repetition@(.rep _ _ _ _) =>
      .call (repetitionFunctionName formatName repetitions repetition) [input, .intLit 0]

private def repetitionDeclaration (formatName : String) (repetitions : List Sym)
    (symbol : Sym) : Option IR.Decl :=
  match symbol with
  | repetition@(.rep separator item lower upper) =>
      let name := repetitionFunctionName formatName repetitions repetition
      let input : IR.Expr := .var "input"
      let itemCount : IR.Expr := .var "count"
      let split : IR.Expr := .var "split"
      let length := .textLen input
      let separatorLength := .intLit (Int.ofNat separator.length)
      let afterSeparator := .intAdd split separatorLength
      let segmentPrefix := .textSubrange input (.intLit 0) split
      let segmentSuffix := .textSubrange input afterSeparator length
      let nextCount := .intAdd itemCount (.intLit 1)
      let countAccepted :=
        .boolAnd
          (.intLe (.intLit (Int.ofNat lower)) nextCount)
          (match upper with
           | none => .boolLit true
           | some bound => .intLe nextCount (.intLit (Int.ofNat bound)))
      let canContinue :=
        match upper with
        | none => .boolLit true
        | some bound => .intLt nextCount (.intLit (Int.ofNat bound))
      let stop := .boolAnd countAccepted (.intEq split length)
      let continuation :=
        .andAll
          [ canContinue,
            .intLe afterSeparator length,
            .textEq (.textSubrange input split afterSeparator) (.textLit separator),
            .call name [segmentSuffix, nextCount] ]
      some <| .function
        { name
          params := [{ name := "input", ty := .text }, { name := "count", ty := .int }]
          returnType := .bool
          body :=
            .existsE [{ name := "split", ty := .int }]
              (.andAll
                [ .intLe (.intLit 0) split,
                  .intLe split length,
                  (symbolCondition formatName repetitions item segmentPrefix),
                  .boolOr stop continuation ])
          recommends := [.intLe (.intLit 0) itemCount]
          decreases := some length
          doc := some "Recognition predicate for one separated-repetition grammar symbol." }
  | _ => none

private def repetitionCountDeclaration (formatName : String) (repetitions : List Sym)
    (symbol : Sym) : Option IR.Decl :=
  match symbol with
  | repetition@(.rep separator item lower upper) =>
      let name := repetitionCountFunctionName formatName repetitions repetition
      let input : IR.Expr := .var "input"
      let itemCount : IR.Expr := .var "count"
      let targetCount : IR.Expr := .var "target"
      let split : IR.Expr := .var "split"
      let length := .textLen input
      let separatorLength := .intLit (Int.ofNat separator.length)
      let afterSeparator := .intAdd split separatorLength
      let segmentPrefix := .textSubrange input (.intLit 0) split
      let segmentSuffix := .textSubrange input afterSeparator length
      let nextCount := .intAdd itemCount (.intLit 1)
      let countAccepted :=
        .boolAnd
          (.intLe (.intLit (Int.ofNat lower)) nextCount)
          (match upper with
           | none => .boolLit true
           | some bound => .intLe nextCount (.intLit (Int.ofNat bound)))
      let canContinue :=
        match upper with
        | none => .boolLit true
        | some bound => .intLt nextCount (.intLit (Int.ofNat bound))
      let stop :=
        .andAll [countAccepted, .intEq split length, .intEq targetCount nextCount]
      let continuation :=
        .andAll
          [ canContinue,
            .intLe afterSeparator length,
            .textEq (.textSubrange input split afterSeparator) (.textLit separator),
            .call name [segmentSuffix, nextCount, targetCount] ]
      some <| .function
        { name
          params :=
            [{ name := "input", ty := .text },
             { name := "count", ty := .int },
             { name := "target", ty := .int }]
          returnType := .bool
          body :=
            .existsE [{ name := "split", ty := .int }]
              (.andAll
                [ .intLe (.intLit 0) split,
                  .intLe split length,
                  symbolCondition formatName repetitions item segmentPrefix,
                  .boolOr stop continuation ])
          recommends :=
            [.boolAnd (.intLe (.intLit 0) itemCount) (.intLe itemCount targetCount)]
          decreases := some length
          doc := some
            "Recognition predicate exposing the number of separated-repetition items." }
  | _ => none

private def grammarSupportDeclarations (format : FormatInput)
    (repetitions : List Sym) : List IR.Decl :=
  let hasString := (allSymbols format.grammar).any containsStringSymbol
  (if hasString then stringGrammarDeclarations else []) ++
    repetitions.filterMap (repetitionDeclaration format.name repetitions) ++
    repetitions.filterMap (repetitionCountDeclaration format.name repetitions)

private def binderBase (item : SymItem) : Option String :=
  match item.sym with
  | .lit _ => if item.optional then some "literal" else none
  | .ref name => some (snakeCase (Triptych.surfaceBinder name))
  | .term .digit _ => some "digits"
  | .term .hexDigit _ => some "hex_digits"
  | .term .bit _ => some "bits"
  | .term (.asciiRange _ _) _ => some "characters"
  | .str => some "string_literal"
  | .rep _ _ _ _ => some "items"

private def assignBinders (items : List SymItem) : List (Option String) := Id.run do
  let bases := items.map binderBase
  let mut seen : List String := []
  let mut result : List (Option String) := []
  for base? in bases do
    match base? with
    | none => result := result ++ [none]
    | some base =>
        let total := (bases.filter (· == some base)).length
        let index := (seen.filter (· == base)).length
        seen := seen ++ [base]
        result := result ++
          [some (if total == 1 then base else base ++ toString index)]
  return result

private def itemExpression (item : SymItem) (binder? : Option String) : IR.Expr :=
  match binder? with
  | some binder => .var binder
  | none =>
      match item.sym with
      | .lit literal => .textLit literal
      | _ => .textLit ""

private def itemCondition (formatName : String) (repetitions : List Sym) (item : SymItem)
    (binder? : Option String) : Option IR.Expr :=
  match binder? with
  | none => none
  | some binder =>
      let input : IR.Expr := .var binder
      let present := symbolCondition formatName repetitions item.sym input
      if item.optional then
        some (.boolOr (.intEq (textLength input) (.intLit 0)) present)
      else
        some present

private def fieldsInSymbol (grammar : Grammar) (fields : List FieldSpec)
    (qual : String) (symbol : Sym) : List FieldSpec :=
  let captures := referencesInSymbol grammar qual symbol
  fields.filter fun field => captures.contains field.capture

private def fieldsInSequence (grammar : Grammar) (fields : List FieldSpec)
    (qual : String) (items : List SymItem) : List FieldSpec :=
  let captures := (items.map fun item => referencesInSymbol grammar qual item.sym).flatten
  fields.filter fun field => captures.contains field.capture

private def fieldsInProduction (grammar : Grammar) (fields : List FieldSpec)
    (production : Production) : List FieldSpec :=
  let qual := productionQualifier grammar production
  let captures := (production.alts.map fun alternative =>
    (alternative.map fun item => referencesInSymbol grammar qual item.sym).flatten).flatten
  fields.filter fun field => captures.contains field.capture

private def emptyFieldConditions (fields : List FieldSpec) (view : IR.Expr) : List IR.Expr :=
  fields.map fun field => .textEq (.field view field.ident) (.textLit "")

private def referenceViewCondition (formatName : String) (grammar : Grammar)
    (fields : List FieldSpec) (qual : String) (item : SymItem) (binder : String) (view : IR.Expr) :
    Option IR.Expr :=
  match item.sym with
  | .ref capture =>
      let input : IR.Expr := .var binder
      let directField :=
        fields.filterMap fun field =>
          if (captureKeys qual capture).contains field.capture then
            some (.textEq (.field view field.ident) input)
          else
            none
      let nested :=
        .call (productionViewName formatName capture) [input, view]
      let present := .andAll (directField ++ [nested])
      if item.optional then
        let absent :=
          .andAll
            (.intEq (textLength input) (.intLit 0) ::
              emptyFieldConditions (fieldsInSymbol grammar fields qual item.sym) view)
        some (.boolOr absent present)
      else
        some present
  | _ => none

private def sequenceCondition (formatName : String) (grammar : Grammar)
    (repetitions : List Sym) (fields scopeFields : List FieldSpec) (qual : String)
    (input : IR.Expr) (items : List SymItem) (view? : Option IR.Expr := none) : IR.Expr :=
  let binders := assignBinders items
  let pieces := (items.zip binders).map fun (item, binder?) =>
    itemExpression item binder?
  let itemConditions := (items.zip binders).filterMap fun (item, binder?) =>
    match view?, binder? with
    | some view, some binder =>
        (referenceViewCondition formatName grammar fields qual item binder view).orElse fun _ =>
          itemCondition formatName repetitions item binder?
    | _, _ => itemCondition formatName repetitions item binder?
  let decomposition := .textEq input (.concatAll pieces)
  let viewConditions := match view? with
    | none => []
    | some view =>
        let presentFields := fieldsInSequence grammar fields qual items
        let absentFields := scopeFields.filter fun field =>
          !(presentFields.any (·.capture == field.capture))
        emptyFieldConditions absentFields view
  let body := .andAll (decomposition :: itemConditions ++ viewConditions)
  let quantified := binders.filterMap (·.map fun name => IR.Binder.mk name .text)
  if quantified.isEmpty then body else .existsE quantified body

private def productionCondition (formatName : String) (grammar : Grammar)
    (repetitions : List Sym) (fields : List FieldSpec)
    (input : IR.Expr) (production : Production) : IR.Expr :=
  .orAll (production.alts.map
    (sequenceCondition formatName grammar repetitions fields []
      (productionQualifier grammar production) input ·))

private def productionViewCondition (formatName : String) (grammar : Grammar)
    (repetitions : List Sym) (fields : List FieldSpec)
    (input view : IR.Expr) (production : Production) : IR.Expr :=
  let scopeFields := fieldsInProduction grammar fields production
  .orAll (production.alts.map
    (sequenceCondition formatName grammar repetitions fields scopeFields
      (productionQualifier grammar production) input · (some view)))

/-! ### Compositional certificates for straight-line cursor plans

The runtime program is flat, but grammar predicates are nested at production references. This
proof-only representation restores those production boundaries while retaining the exact cursor
position attached to each consuming operation. It is built by checking the grammar sequence and
the certified `ScanPattern` in lockstep. -/

private inductive StraightProofPiece where
  | literal (character : Char) (start stop : String)
  | optionalLiteral (binder : String) (character : Char) (start stop : String)
  | tokenRun (binder : String) (token : TokClass) (length : LenSpec)
      (start stop : String)
  | capture (binder production : String) (start stop : String)

private inductive StraightProofAtom where
  | literal (character : Char)
  | optionalLiteral (binder : String) (character : Char)
  | tokenRun (binder : String) (token : TokClass) (length : LenSpec)

private structure StraightProofProduction where
  name : String
  source : String
  isRoot : Bool
  start : String
  stop : String
  sequence : Triptych.Seq
  binders : List (Option String)
  pieces : List StraightProofPiece

private structure BuiltStraightSequence where
  pieces : List StraightProofPiece
  descendants : List StraightProofProduction
  atoms : List StraightProofAtom
  stop : String
  nextPosition : Nat

private structure BuiltStraightProduction where
  root : StraightProofProduction
  descendants : List StraightProofProduction
  atoms : List StraightProofAtom
  nextPosition : Nat

private structure StraightProofPlan where
  root : StraightProofProduction
  descendants : List StraightProofProduction
  atoms : List StraightProofAtom

private def proofBinder (production binder : String) : String :=
  snakeCase production ++ "_" ++ binder

private def singlePlanCharacter (text : String) : Except String Char :=
  match ScanPattern.singleAsciiCharacter? text with
  | some character => pure character
  | none => throw "Verus direct proof: expected one ASCII literal"

mutual

private partial def buildStraightProduction (grammar : Grammar) (name source : String)
    (isRoot : Bool) (pattern : ScanPattern) (start : String) (position : Nat) :
    Except String BuiltStraightProduction := do
  let production ← match grammar.prod? name with
    | some production => pure production
    | none => throw s!"Verus direct proof: missing production `{name}`"
  let sequence ← match production.alts with
    | [sequence] => pure sequence
    | _ => throw s!"Verus direct proof: production `{name}` is not straight-line"
  let assigned := assignBinders sequence
  let built ←
    buildStraightSequence grammar name sequence assigned pattern start position
  pure
    { root :=
        { name
          source
          isRoot
          start
          stop := built.stop
          sequence
          binders := built.pieces.map fun
            | .literal _ _ _ => none
            | .optionalLiteral binder _ _ _ => some binder
            | .tokenRun binder _ _ _ _ => some binder
            | .capture binder _ _ _ => some binder
          pieces := built.pieces }
      descendants := built.descendants
      atoms := built.atoms
      nextPosition := built.nextPosition }

private partial def buildStraightSequence (grammar : Grammar) (owner : String) :
    Triptych.Seq → List (Option String) → ScanPattern → String → Nat →
      Except String BuiltStraightSequence
  | [], [], .empty, start, position =>
      pure
        { pieces := []
          descendants := []
          atoms := []
          stop := start
          nextPosition := position }
  | ⟨.lit text, true⟩ :: rest, some assigned :: binders,
      .optionalLiteral character tail, start, position => do
      let expected ← singlePlanCharacter text
      unless expected == character do
        throw "Verus direct proof: optional literal disagrees with ScanPattern"
      let stop := positionName (position + 1)
      let binder := proofBinder owner assigned
      let tailBuilt ←
        buildStraightSequence grammar owner rest binders tail stop (position + 1)
      pure
        { tailBuilt with
          pieces := .optionalLiteral binder character start stop :: tailBuilt.pieces
          atoms := .optionalLiteral binder character :: tailBuilt.atoms }
  | ⟨.lit text, false⟩ :: rest, none :: binders,
      .literal character tail, start, position => do
      let expected ← singlePlanCharacter text
      unless expected == character do
        throw "Verus direct proof: literal disagrees with ScanPattern"
      let stop := positionName (position + 1)
      let tailBuilt ←
        buildStraightSequence grammar owner rest binders tail stop (position + 1)
      pure
        { tailBuilt with
          pieces := .literal character start stop :: tailBuilt.pieces
          atoms := .literal character :: tailBuilt.atoms }
  | ⟨.term token length, false⟩ :: rest, some assigned :: binders,
      .tokenRun foundToken foundLength tail, start, position => do
      unless token == foundToken && length == foundLength do
        throw "Verus direct proof: token run disagrees with ScanPattern"
      let stop := positionName (position + 1)
      let binder := proofBinder owner assigned
      let tailBuilt ←
        buildStraightSequence grammar owner rest binders tail stop (position + 1)
      pure
        { tailBuilt with
          pieces := .tokenRun binder token length start stop :: tailBuilt.pieces
          atoms := .tokenRun binder token length :: tailBuilt.atoms }
  | ⟨.ref name, false⟩ :: rest, some _ :: binders,
      .capture foundName _ body tail, start, position => do
      unless name == foundName do
        throw "Verus direct proof: capture disagrees with ScanPattern"
      let source := captureField name
      let child ← buildStraightProduction grammar name source false body start position
      let tailBuilt ←
        buildStraightSequence grammar owner rest binders tail child.root.stop
          child.nextPosition
      pure
        { pieces :=
            .capture source name start child.root.stop :: tailBuilt.pieces
          descendants := child.root :: child.descendants ++ tailBuilt.descendants
          atoms := child.atoms ++ tailBuilt.atoms
          stop := tailBuilt.stop
          nextPosition := tailBuilt.nextPosition }
  | _, _, _, _, _ =>
      throw "Verus direct proof: grammar sequence and ScanPattern have different shapes"

end

private def buildStraightProofPlan (format : FormatInput) (scanPlan : ScanPlan) :
    Except String StraightProofPlan := do
  let built ←
    buildStraightProduction format.grammar format.grammar.start "input" true
      scanPlan.pattern "position_0" 0
  pure { root := built.root, descendants := built.descendants, atoms := built.atoms }

private def allProofProductions (plan : StraightProofPlan) :
    List StraightProofProduction :=
  plan.root :: plan.descendants

private def productionSource (success : Bool) (production : StraightProofProduction) : String :=
  if production.isRoot then
    if success then "input@" else "input"
  else
    production.source

private def sequenceBodyWithBinders (formatName : String) (repetitions : List Sym)
    (input : IR.Expr) (items : List SymItem) (binders : List (Option String)) : IR.Expr :=
  let pieces := (items.zip binders).map fun (item, binder?) =>
    itemExpression item binder?
  let itemConditions := (items.zip binders).filterMap fun (item, binder?) =>
    itemCondition formatName repetitions item binder?
  .andAll (.textEq input (.concatAll pieces) :: itemConditions)

private def sequenceViewBodyWithBinders (formatName : String) (grammar : Grammar)
    (repetitions : List Sym) (fields scopeFields : List FieldSpec) (qual : String)
    (input view : IR.Expr) (items : List SymItem) (binders : List (Option String)) : IR.Expr :=
  let pieces := (items.zip binders).map fun (item, binder?) =>
    itemExpression item binder?
  let itemConditions := (items.zip binders).filterMap fun (item, binder?) =>
    match binder? with
    | some binder =>
        (referenceViewCondition formatName grammar fields qual item binder view).orElse fun _ =>
          itemCondition formatName repetitions item binder?
    | none => none
  let presentFields := fieldsInSequence grammar fields qual items
  let absentFields := scopeFields.filter fun field =>
    !(presentFields.any (·.capture == field.capture))
  .andAll
    (.textEq input (.concatAll pieces) ::
      itemConditions ++ emptyFieldConditions absentFields view)

private def sequenceConditionWithBinders (formatName : String) (repetitions : List Sym)
    (input : IR.Expr) (items : List SymItem) (binders : List (Option String)) : IR.Expr :=
  let body := sequenceBodyWithBinders formatName repetitions input items binders
  let quantified := binders.filterMap (·.map fun name => IR.Binder.mk name .text)
  if quantified.isEmpty then body else .existsE quantified body

private def renderProofExpr (expression : IR.Expr) : String :=
  prettyPrintExpr (lowerExpr expression)

private def proofConcatExpression (production : StraightProofProduction) : IR.Expr :=
  let pieces := (production.sequence.zip production.binders).map fun (item, binder?) =>
    itemExpression item binder?
  .concatAll pieces

private def proofBodyExpression (format : FormatInput) (success : Bool)
    (production : StraightProofProduction) : IR.Expr :=
  sequenceBodyWithBinders format.name (repetitionsFor format.grammar)
    (.var (productionSource success production)) production.sequence production.binders

private def proofExistsExpression (format : FormatInput) (success : Bool)
    (production : StraightProofProduction) : IR.Expr :=
  sequenceConditionWithBinders format.name (repetitionsFor format.grammar)
    (.var (productionSource success production)) production.sequence production.binders

private def renderSpan (name start stop : String) : String :=
  s!"let {name} = input@.subrange({start} as int, {stop} as int);"

private def renderProofSpanDeclarations (plan : StraightProofPlan) : String :=
  let productionSpans := plan.descendants.map fun production =>
    renderSpan production.source production.start production.stop
  let pieceSpans := (allProofProductions plan).flatMap fun production =>
    production.pieces.filterMap fun
      | .optionalLiteral binder _ start stop => some (renderSpan binder start stop)
      | .tokenRun binder _ _ start stop => some (renderSpan binder start stop)
      | _ => none
  String.intercalate "\n" (productionSpans ++ pieceSpans)

private def tokenPredicate (token : TokClass) (source index : String) : String :=
  renderProofExpr (.isToken token (.textIndex (.var source) (.var index)))

private def tokenRevealLines : TokClass → List String
  | .digit => ["reveal(triptych_is_digit);"]
  | .hexDigit => ["reveal(triptych_is_hex_digit);", "reveal(triptych_is_digit);"]
  | .bit => ["reveal(triptych_is_bit);"]
  | .asciiRange _ _ => []

private def renderLengthFacts (source : String) : LenSpec → List String
  | .exactly width => [s!"assert({source}.len() == {width});"]
  | .between lower upper =>
      [s!"assert({lower} <= {source}.len());", s!"assert({source}.len() <= {upper});"]
  | .atLeastOne => [s!"assert(1 <= {source}.len());"]

private def renderSuccessOptional (binder : String) (character : Char)
    (start stop : String) : String :=
  String.intercalate "\n"
    [ s!"assert({binder}.len() == {stop} as int - {start} as int);",
      s!"if {stop} == {start} " ++ "{",
      s!"    assert({binder}.len() == 0);",
      "} else {",
      s!"    assert({stop} == {start} + 1);",
      s!"    assert(input@[{start} as int] == {verusCharacterLiteral character});",
      s!"    assert({binder} =~= seq![{verusCharacterLiteral character}]) by " ++ "{",
      s!"        assert_seqs_equal!({binder} == seq![{verusCharacterLiteral character}]);",
      "    }",
      "}",
      s!"assert({binder}.len() == 0 || " ++
        s!"{binder} == seq![{verusCharacterLiteral character}]);" ]

private def renderSuccessToken (binder : String) (token : TokClass) (length : LenSpec)
    (start stop : String) : String :=
  let predicate := tokenPredicate token binder "i"
  let reveals := (tokenRevealLines token).map ("    " ++ ·)
  String.intercalate "\n" <|
    [s!"assert({binder}.len() == {stop} as int - {start} as int);"] ++
    renderLengthFacts binder length ++
    [ s!"assert forall|i: int| #![auto] 0 <= i < {binder}.len() implies",
      s!"    {predicate} by " ++ "{",
      s!"    assert({binder}[i] == input@[{start} as int + i]);",
      s!"    assert(plan_token_accepts({renderPlanTokenClass token}, " ++
        s!"input@[{start} as int + i]));",
      "    reveal(plan_token_accepts);" ] ++ reveals ++ ["}"]

private def renderSuccessPieceFacts (production : StraightProofProduction) : String :=
  String.intercalate "\n\n" <| production.pieces.filterMap fun
    | .literal character start _ =>
        some s!"assert(input@[{start} as int] == {verusCharacterLiteral character});"
    | .optionalLiteral binder character start stop =>
        some (renderSuccessOptional binder character start stop)
    | .tokenRun binder token length start stop =>
        some (renderSuccessToken binder token length start stop)
    | .capture _ _ _ _ => none

private def renderSuccessProduction (format : FormatInput)
    (production : StraightProofProduction) : String :=
  let source := productionSource true production
  let concatenation := renderProofExpr (proofConcatExpression production)
  let body := renderProofExpr (proofBodyExpression format true production)
  let existsCondition := renderProofExpr (proofExistsExpression format true production)
  let wf := productionName format.name production.name
  String.intercalate "\n"
    [ renderSuccessPieceFacts production,
      s!"assert({source} =~= {concatenation}) by " ++ "{",
      s!"    assert_seqs_equal!({source} == {concatenation});",
      "}",
      s!"assert({source} == {concatenation});",
      s!"assert({wf}({source})) by " ++ "{",
      s!"    reveal({wf});",
      s!"    assert({existsCondition}) by " ++ "{",
      s!"        assert({body});",
      "    }",
      "}" ]

private def renderStraightSuccessProof (format : FormatInput)
    (plan : StraightProofPlan) : String :=
  let productionProofs :=
    ((allProofProductions plan).reverse.map (renderSuccessProduction format))
  "proof {\n" ++
    indentText 1
      (renderProofSpanDeclarations plan ++ "\n\n" ++
        String.intercalate "\n\n" productionProofs) ++
    "\n}"

private def renderViewSuccessProduction (format : FormatInput)
    (production : StraightProofProduction) : String :=
  match format.grammar.prod? production.name with
  | none =>
      "assert(false); // direct proof plan references a missing production"
  | some grammarProduction =>
      let fields := fieldsFor format
      let body :=
        sequenceViewBodyWithBinders format.name format.grammar
          (repetitionsFor format.grammar) fields
          (fieldsInProduction format.grammar fields grammarProduction)
          (productionQualifier format.grammar grammarProduction)
          (.var (productionSource true production)) (.var "parsed_view")
          production.sequence production.binders
      let quantified :=
        production.binders.filterMap (·.map fun name => IR.Binder.mk name .text)
      let existsCondition :=
        if quantified.isEmpty then body else .existsE quantified body
      let matchesFn := productionViewName format.name production.name
      String.intercalate "\n"
        [ s!"assert({matchesFn}({productionSource true production}, parsed_view)) by " ++ "{",
          s!"    reveal({matchesFn});",
          s!"    assert({renderProofExpr existsCondition}) by " ++ "{",
          s!"        assert({renderProofExpr body});",
          "    }",
          "}" ]

private def renderStraightViewProof (format : FormatInput)
    (plan : StraightProofPlan) : String :=
  renderProofSpanDeclarations plan ++ "\n\n" ++
    String.intercalate "\n\n"
      ((allProofProductions plan).reverse.map (renderViewSuccessProduction format))

private def renderBinderTypes (binders : List String) : String :=
  match binders with
  | [binder] => s!"{binder}: Seq<char>"
  | _ =>
      "(" ++ String.intercalate ", " binders ++ "): (" ++
        String.intercalate ", " (binders.map fun _ => "Seq<char>") ++ ")"

private def renderChooseBinders (binders : List String) : String :=
  String.intercalate ", " (binders.map fun binder => s!"{binder}: Seq<char>")

private def renderUnpackProduction (format : FormatInput)
    (production : StraightProofProduction) : String :=
  let source := productionSource false production
  let body := renderProofExpr (proofBodyExpression format false production)
  let binders := production.binders.filterMap id
  let wf := productionName format.name production.name
  let choose :=
    if binders.isEmpty then
      s!"assert({body});"
    else
      s!"let {renderBinderTypes binders} =\n" ++
        s!"    choose|{renderChooseBinders binders}| {body};\n" ++
        s!"assert({body});"
  s!"reveal({wf});\n{choose}\nassert({source} == " ++
    s!"{renderProofExpr (proofConcatExpression production)});"

private def atomExpression : StraightProofAtom → IR.Expr
  | .literal character => .textLit (String.singleton character)
  | .optionalLiteral binder _ => .var binder
  | .tokenRun binder _ _ => .var binder

private def atomWidth : StraightProofAtom → String
  | .literal _ => "1"
  | .optionalLiteral binder _ | .tokenRun binder _ _ =>
      s!"({binder}.len() as int)"

private def renderAsciiAtom : StraightProofAtom → String
  | .literal character =>
      s!"assert(is_ascii_chars(seq![{verusCharacterLiteral character}]));"
  | .optionalLiteral binder character =>
      String.intercalate "\n"
        [ s!"assert(is_ascii_chars({binder})) by " ++ "{",
          s!"    assert forall|i: int| 0 <= i < {binder}.len() implies",
          s!"        {verusCharacterLiteral (Char.ofNat 0)} <= #[trigger] {binder}[i] <= " ++
            s!"{verusCharacterLiteral (Char.ofNat 127)} by " ++ "{",
          s!"        assert({binder} == seq![{verusCharacterLiteral character}]);",
          "    }",
          "}" ]
  | .tokenRun binder token _ =>
      let predicate := tokenPredicate token binder "i"
      let reveals := (tokenRevealLines token).map ("        " ++ ·)
      String.intercalate "\n" <|
        [ s!"assert(is_ascii_chars({binder})) by " ++ "{",
          s!"    assert forall|i: int| 0 <= i < {binder}.len() implies",
          s!"        {verusCharacterLiteral (Char.ofNat 0)} <= #[trigger] {binder}[i] <= " ++
            s!"{verusCharacterLiteral (Char.ofNat 127)} by " ++ "{",
          s!"        assert({predicate});" ] ++ reveals ++ ["    }", "}"]

private def renderAsciiFacts (plan : StraightProofPlan) : String :=
  let atomFacts := plan.atoms.map renderAsciiAtom
  let expressions := plan.atoms.map atomExpression
  let concatenation := renderProofExpr (.concatAll expressions)
  let prefixFacts :=
    match expressions with
    | [] => ["assert(is_ascii_chars(seq![]));"]
    | first :: rest =>
        let (_, facts) := rest.foldl
          (fun (accumulated, facts) expression =>
            let next := IR.Expr.textConcat accumulated expression
            (next, facts ++ [s!"assert(is_ascii_chars({renderProofExpr next}));"]))
          (first, [])
        facts
  String.intercalate "\n" <|
    atomFacts ++
    ["broadcast use is_ascii_chars_concat;"] ++
    prefixFacts ++
    [ s!"assert(input =~= {concatenation}) by " ++ "{",
      s!"    assert_seqs_equal!(input == {concatenation});",
      "}",
      s!"assert(input == {concatenation});",
      "assert(is_ascii_chars(input));" ]

private def proofPositionName (index : Nat) : String :=
  s!"proof_position_{index}"

private def renderExpectedPositions (atoms : List StraightProofAtom) : String :=
  let (_, lines) := atoms.foldl
    (fun (index, lines) atom =>
      let start := proofPositionName index
      let stop := proofPositionName (index + 1)
      (index + 1, lines ++ [s!"let {stop}: int = {start} + {atomWidth atom};"]))
    (0, ["let proof_position_0: int = 0;"])
  String.intercalate "\n" <|
    lines ++ [s!"assert({proofPositionName atoms.length} == input.len());"]

private def renderTokenBridge (token : TokClass) (source index character : String)
    (indent : String := "") : List String :=
  let predicate := tokenPredicate token source index
  [s!"{indent}assert({predicate});"] ++
    (tokenRevealLines token).map (indent ++ ·) ++
    [s!"{indent}assert(plan_token_accepts({renderPlanTokenClass token}, {character})) by " ++
       "{",
     s!"{indent}    reveal(plan_token_accepts);",
     s!"{indent}}"]

private partial def renderOptionalAbsentBoundary (character : Char) (start : String) :
    List StraightProofAtom → List String
  | [] => [s!"assert({start} == input.len());"]
  | .literal next :: _ =>
      [ s!"assert({start} < input.len());",
        s!"assert(input[{start}] == {verusCharacterLiteral next});",
        s!"assert(input[{start}] != {verusCharacterLiteral character});" ]
  | .optionalLiteral _ _ :: _ =>
      ["assert(false); // certified plans never put two optional consumers at one boundary"]
  | .tokenRun binder token _ :: rest =>
      [s!"if {binder}.len() == 0 " ++ "{"] ++
        (renderOptionalAbsentBoundary character start rest).map ("    " ++ ·) ++
        [ "} else {",
          s!"    assert({start} < input.len());",
          s!"    assert(input[{start}] == {binder}[0]);" ] ++
        renderTokenBridge token binder "0" s!"input[{start}]" "    " ++
        [ s!"    assert(!plan_token_accepts({renderPlanTokenClass token}, " ++
            s!"{verusCharacterLiteral character}));",
          s!"    assert(input[{start}] != {verusCharacterLiteral character});",
          "}" ]

private def renderCompletenessOptional (binder : String) (character : Char)
    (start stop : String) (rest : List StraightProofAtom) : String :=
  String.intercalate "\n" <|
    [s!"assert({binder}.len() == 0 || {binder} == " ++
      s!"seq![{verusCharacterLiteral character}]);",
     s!"if {binder}.len() == 0 " ++ "{"] ++
    (renderOptionalAbsentBoundary character start rest).map ("    " ++ ·) ++
    [ s!"    assert({stop} == {start});",
      "} else {",
      s!"    assert({binder} == seq![{verusCharacterLiteral character}]);",
      s!"    assert({binder}.len() == 1);",
      s!"    assert({start} < input.len());",
      s!"    assert(input[{start}] == {verusCharacterLiteral character});",
      s!"    assert({stop} == {start} + 1);",
      "}" ]

private def renderCompletenessToken (binder : String) (token : TokClass)
    (length : LenSpec) (start stop : String) (rest : List StraightProofAtom) : String :=
  let accepted :=
    [ s!"assert forall|index: int| {start} <= index < {stop} implies",
      s!"    #[trigger] plan_token_accepts({renderPlanTokenClass token}, input[index]) by " ++
        "{",
      s!"    let item_index = index - {start};",
      s!"    assert(0 <= item_index < {binder}.len());",
      s!"    assert(input[index] == {binder}[item_index]);" ] ++
      renderTokenBridge token binder "item_index" "input[index]" "    " ++ ["}"]
  let limit :=
    match length with
    | .exactly _ => stop
    | _ => "input.len() as int"
  let boundary :=
    match length with
    | .exactly _ => []
    | _ =>
        match rest with
        | [] => [s!"assert({stop} == input.len());"]
        | .literal character :: _ =>
            [ s!"assert({stop} < input.len());",
              s!"assert(input[{stop}] == {verusCharacterLiteral character});",
              s!"assert(!plan_token_accepts({renderPlanTokenClass token}, input[{stop}])) by " ++
                "{",
              "    reveal(plan_token_accepts);",
              "}" ]
        | _ =>
            ["assert(false); // deterministic variable runs end at a literal or input end"]
  String.intercalate "\n" <|
    renderLengthFacts binder length ++
    [s!"assert({stop} == {start} + ({binder}.len() as int));"] ++
    accepted ++ boundary ++
    [ s!"plan_scan_token_end_at_boundary(",
      "    input,",
      s!"    {start},",
      s!"    {stop},",
      s!"    {limit},",
      s!"    {renderPlanTokenClass token},",
      ");" ]

private def renderCompletenessAtom (atom : StraightProofAtom) (index : Nat)
    (rest : List StraightProofAtom) : String :=
  let start := proofPositionName index
  let stop := proofPositionName (index + 1)
  match atom with
  | .literal character =>
      String.intercalate "\n"
        [ s!"assert({start} < input.len());",
          s!"assert(input[{start}] == {verusCharacterLiteral character});",
          s!"assert({stop} == {start} + 1);" ]
  | .optionalLiteral binder character =>
      renderCompletenessOptional binder character start stop rest
  | .tokenRun binder token length =>
      renderCompletenessToken binder token length start stop rest

private def renderCompletenessAtoms : List StraightProofAtom → Nat → List String
  | [], _ => []
  | atom :: rest, index =>
      renderCompletenessAtom atom index rest ::
        renderCompletenessAtoms rest (index + 1)

private def renderStraightCompletenessProof (format : FormatInput)
    (plan : StraightProofPlan) : String :=
  let unpack :=
    String.intercalate "\n\n" <|
      (allProofProductions plan).map (renderUnpackProduction format)
  let atomProofs := String.intercalate "\n\n" (renderCompletenessAtoms plan.atoms 0)
  s!"pub proof fn {parsePlanCompletenessFunction format}(input: Seq<char>)
    requires
        {grammarWfFunction format}(input),
    ensures
        {parsePlanFunction format}(input).is_some(),
" ++ "{\n" ++
    indentText 1 unpack ++ "\n\n" ++
    indentText 1 (renderAsciiFacts plan) ++ "\n\n" ++
    indentText 1 (renderExpectedPositions plan.atoms) ++ "\n\n" ++
    indentText 1 atomProofs ++ "\n\n" ++
    s!"    reveal({parsePlanFunction format});\n" ++
    "}"

private def captureParams (fields : List FieldSpec) (captures : List String) : List IR.Param :=
  captures.map fun capture =>
    { name := fieldIdent fields capture, ty := .text }

private def captureArgs (fields : List FieldSpec) (captures : List String) : List IR.Expr :=
  captures.map fun capture => .capture (fieldIdent fields capture) capture

private def viewArgs (fields : List FieldSpec) (captures : List String) : List IR.Expr :=
  captures.map fun capture => .field (.var "view") (fieldIdent fields capture)

private def boolFunction (name : String) (params : List IR.Param) (body : IR.Expr)
    (doc : Option String := none) : IR.Decl :=
  .function { name, params, returnType := .bool, body, doc }

private def intFunction (name : String) (params : List IR.Param) (body : IR.Expr)
    (doc : Option String := none) : IR.Decl :=
  .function { name, params, returnType := .int, body, doc }

private def productionDeclarations (format : FormatInput) (repetitions : List Sym)
    (fields : List FieldSpec) : List IR.Decl :=
  format.grammar.prods.map fun production =>
    boolFunction (productionName format.name production.name)
      [{ name := "input", ty := .text }]
      (productionCondition format.name format.grammar repetitions fields (.var "input") production)
      (some s!"Lean counterpart: `{format.name}.IsWf.{production.name}`.")

private def productionViewDeclarations (format : FormatInput) (repetitions : List Sym)
    (fields : List FieldSpec) : List IR.Decl :=
  let viewType := typeName format.name ++ "View"
  format.grammar.prods.map fun production =>
    boolFunction (productionViewName format.name production.name)
      [{ name := "input", ty := .text }, { name := "view", ty := .named viewType }]
      (productionViewCondition format.name format.grammar repetitions fields
        (.var "input") (.var "view") production)
      (some s!"Capture relation for `{format.name}.IsWf.{production.name}`.")

private def constraintDeclarations (format : FormatInput) (fields : List FieldSpec)
    (formatPrefix viewType : String) : List IR.Decl :=
  let makePhase (constraints : List Constraint) (functionSuffix viewSuffix satisfiesSuffix
      leanName : String) : List IR.Decl :=
    if constraints.isEmpty then
      []
    else
      let captures := (constraints.flatMap Constraint.captures).eraseDups
      let function := functionName format.name functionSuffix
      let viewFunction := functionName format.name viewSuffix
      let satisfiesFunction := functionName format.name satisfiesSuffix
      let translated :=
        constraints.map
          (translateConstraintNamed (fieldIdent fields) format.valueExpr
            (functionName format.name "value") (captureArgs fields format.valueExpr.captures))
      [ boolFunction function (captureParams fields captures) (.andAll translated)
          (some s!"Lean counterpart: `{format.name}.{leanName}`."),
        boolFunction viewFunction [{ name := "view", ty := .named viewType }]
          (.call function (viewArgs fields captures)),
        boolFunction satisfiesFunction [{ name := "input", ty := .text }]
          (.existsE [{ name := "view", ty := .named viewType }]
            (.boolAnd
              (.call (formatPrefix ++ "_matches_view") [.var "input", .var "view"])
              (.call viewFunction [.var "view"])))
          (some s!"Lean counterpart: `{format.name}.Satisfies{leanName}`.") ]
  makePhase format.wfConstraints "wf_constraints" "view_wf_constraints"
      "satisfies_wf_constraints" "WfConstraints" ++
    makePhase format.valueConstraints "constraints" "view_constraints"
      "satisfies_constraints" "Constraints"

private def formatDeclarations (format : FormatInput)
    (fields : List FieldSpec) : Except String (List IR.Decl) := do
  let root ← match format.grammar.startProd? with
    | some production => pure production
    | none => throw s!"Verus backend: start production `{format.grammar.start}` is missing"
  let formatPrefix := snakeCase format.name
  let viewType := typeName format.name ++ "View"
  let valueCaptures := format.valueExpr.captures
  let valueFunction := functionName format.name "value"
  let hasWfConstraints := !format.wfConstraints.isEmpty
  let hasValueConstraints := !format.valueConstraints.isEmpty
  let viewFields :=
    { name := "input", ty := .text : IR.FieldDecl } ::
      fields.map fun (field : FieldSpec) => { name := field.ident, ty := .text }
  let rootWf := productionName format.name format.grammar.start
  let matchesView := formatPrefix ++ "_matches_view"
  let wfConstraintCall : IR.Expr :=
    if hasWfConstraints then
      .call (formatPrefix ++ "_view_wf_constraints") [.var "view"]
    else
      .boolLit true
  let valueConstraintCall : IR.Expr :=
    if hasValueConstraints then
      .call (formatPrefix ++ "_view_constraints") [.var "view"]
    else
      .boolLit true
  let viewValid : IR.Expr := .boolAnd wfConstraintCall valueConstraintCall
  let isWfBody : IR.Expr :=
    if hasWfConstraints then
      .boolAnd
        (.call rootWf [.var "input"])
        (.call (formatPrefix ++ "_satisfies_wf_constraints") [.var "input"])
    else
      .call rootWf [.var "input"]
  let isValidBody : IR.Expr :=
    if hasValueConstraints then
      .boolAnd
        (.call (formatPrefix ++ "_is_wf") [.var "input"])
        (.call (formatPrefix ++ "_satisfies_constraints") [.var "input"])
    else
      .call (formatPrefix ++ "_is_wf") [.var "input"]
  let declarations : List IR.Decl :=
    [ IR.Decl.structure { name := viewType, fields := viewFields },
      boolFunction matchesView
        [{ name := "input", ty := .text }, { name := "view", ty := .named viewType }]
        (.boolAnd
          (.textEq (.field (.var "view") "input") (.var "input"))
          (.call (productionViewName format.name root.name) [.var "input", .var "view"])),
      intFunction valueFunction (captureParams fields valueCaptures)
        (translateValExpr (fieldIdent fields) format.valueExpr)
        (some s!"Lean counterpart: `{format.name}.value`.") ] ++
    constraintDeclarations format fields formatPrefix viewType ++
    [ boolFunction (formatPrefix ++ "_is_wf") [{ name := "input", ty := .text }]
        isWfBody (some s!"Lean counterpart: `{format.name}.IsWf`."),
      boolFunction (formatPrefix ++ "_view_valid")
        [{ name := "view", ty := .named viewType }] viewValid,
      intFunction (formatPrefix ++ "_view_denotation")
        [{ name := "view", ty := .named viewType }]
        (.call valueFunction (viewArgs fields valueCaptures))
        (some s!"Lean counterpart: `{format.name}.View.denotation`."),
      boolFunction (formatPrefix ++ "_is_valid") [{ name := "input", ty := .text }]
        isValidBody (some s!"Lean counterpart: `{format.name}.IsValid`.") ]
  pure declarations

/-- Validate and translate one elaborated Triptych format into the Verus specification IR. -/
def translateSpecToIR (format : FormatInput) : Except String IR.Module := do
  validateReadableSpecInput format
  let fields := fieldsFor format
  let repetitions := repetitionsFor format.grammar
  let formatDecls ← formatDeclarations format fields
  let declarations :=
    grammarSupportDeclarations format repetitions ++
      productionDeclarations format repetitions fields ++
      productionViewDeclarations format repetitions fields ++
      formatDecls
  pure
    { header :=
        [s!"Generated by Triptych from `triptych {format.name}`.",
         "Source ASTs: Grammar -> IsWf, ValExpr -> value, Constraint -> constraint phases.",
         s!"Lean conversion boundary: ofSpec `{format.ofSpec}`, toSpec `{format.toSpec}`."]
      imports :=
        ["vstd::arithmetic::div_mod::rust_div"] ++
          (if (allSymbols format.grammar).any containsStringSymbol then
            ["vstd::std_specs::char::is_white_space"]
          else
            []) ++
          ["vstd::prelude::*"]
      declarations }

/-- Generate the readable Verus specification for one elaborated Triptych format. -/
def emitSpec (format : FormatInput) : Except String String := do
  let irModule ← translateSpecToIR format
  let astModule := lowerModule irModule
  pure (prettyPrintModule astModule)

private def optionEqualsSome (option result : Ast.Expr) : Ast.Expr :=
  .matchOption option { name := "parsed", ty := .int }
    (.intEq (.var "parsed") result)
    (.boolLit false)

private def optionIsNone (option : Ast.Expr) : Ast.Expr :=
  .matchOption option { name := "parsed", ty := .int }
    (.boolLit false)
    (.boolLit true)

private def boolNot (expression : Ast.Expr) : Ast.Expr :=
  .boolNot expression

private def soundnessDeclarations (format : FormatInput) : List Ast.Decl :=
  let formatPrefix := snakeCase format.name
  let viewType := typeName format.name ++ "View"
  let contractTrait := typeName format.name ++ "ExternalParserContract"
  let resultPredicate := formatPrefix ++ "_matches_result"
  let hasResultPredicate := formatPrefix ++ "_has_result"
  let input : Ast.Expr := .var "input"
  let result : Ast.Expr := .var "value"
  let view : Ast.Expr := .var "view"
  let parseResult := Ast.Expr.call "Self::parse_to_spec" [input]
  let parsesValue := optionEqualsSome parseResult result
  let rejects := optionIsNone parseResult
  let isValid := Ast.Expr.call (formatPrefix ++ "_is_valid") [input]
  let matchesResult := Ast.Expr.call resultPredicate [input, result]
  let resultBody :=
    Ast.Expr.existsE [{ name := "view", ty := .named viewType }]
      (.andAll
        [ .call (formatPrefix ++ "_matches_view") [input, view],
          .call (formatPrefix ++ "_view_valid") [view],
          .intEq (.call (formatPrefix ++ "_view_denotation") [view]) result ])
  let hasResultBody :=
    Ast.Expr.existsE [{ name := "input", ty := .text }]
      (.call resultPredicate [.var "input", result])
  let baseItems : List Ast.TraitItem :=
    [ .specMethod
        { name := "parse_to_spec"
          params := [{ name := "input", ty := .text }]
          returnType := .option .int
          doc := some
            "Specification view of the external parser result after its toSpec conversion." },
      .proofMethod
        { name := "extparse_sound"
          params := [{ name := "input", ty := .text }, { name := "value", ty := .int }]
          requires := [parsesValue]
          ensures := [isValid, matchesResult]
          doc := some "Every successful external parse is valid and has the specified value." },
      .proofMethod
        { name := "extparse_complete"
          params := [{ name := "input", ty := .text }, { name := "value", ty := .int }]
          requires := [isValid, matchesResult]
          ensures := [parsesValue]
          doc := some "Every valid input with this value is accepted with that value." },
      .proofMethod
        { name := "extparse_reject"
          params := [{ name := "input", ty := .text }]
          ensures :=
            [ .boolImplies rejects (boolNot isValid),
              .boolImplies (boolNot isValid) rejects ]
          doc := some "The external parser rejects exactly the invalid inputs." } ]
  let printerItems : List Ast.TraitItem :=
    if format.hasPrinter then
      let serializer (valueExpr : Ast.Expr) :=
        Ast.Expr.call "Self::to_string_to_spec" [valueExpr]
      let parserResult (source : Ast.Expr) :=
        Ast.Expr.call "Self::parse_to_spec" [source]
      let normalized (source : Ast.Expr) :=
        Ast.Expr.matchOption (parserResult source) { name := "parsed", ty := .int }
          (.optionSome (serializer (.var "parsed")))
          .optionNone
      let left := Ast.Expr.var "left"
      let right := Ast.Expr.var "right"
      let leftParse := parserResult left
      let rightParse := parserResult right
      let normalizedEqual := Ast.Expr.textEq (normalized left) (normalized right)
      let parseEqual := Ast.Expr.textEq leftParse rightParse
      [ .specMethod
          { name := "to_string_to_spec"
            params := [{ name := "value", ty := .int }]
            returnType := .text
            doc := some "Specification characters emitted by the external canonical serializer." },
        .proofMethod
          { name := "extparse_to_string_roundtrip"
            params := [{ name := "value", ty := .int }]
            requires := [.call hasResultPredicate [.var "value"]]
            ensures :=
              [optionEqualsSome
                (parserResult (serializer (.var "value")))
                (.var "value")]
            doc := some "Parsing the external serializer returns the original representable value." },
        .proofMethod
          { name := "extparse_to_string_injective"
            params := [{ name := "left", ty := .int }, { name := "right", ty := .int }]
            requires :=
              [ .call hasResultPredicate [left],
                .call hasResultPredicate [right],
                .textEq (serializer left) (serializer right) ]
            ensures := [.intEq left right]
            doc := some "The external serializer is injective on representable values." },
        .proofMethod
          { name := "extparse_normalize_eq_iff_parse_eq"
            params := [{ name := "left", ty := .text }, { name := "right", ty := .text }]
            ensures :=
              [ .boolImplies normalizedEqual parseEqual,
                .boolImplies parseEqual normalizedEqual ]
            doc := some
              "Canonicalized external parses are equal exactly when their parse results are equal." } ]
    else
      []
  let resultDecl : Ast.Decl :=
    .function
      { name := resultPredicate
        params := [{ name := "input", ty := .text }, { name := "value", ty := .int }]
        returnType := .bool
        body := resultBody
        doc := some "The input has a valid typed view whose denotation is this result." }
  let hasResultDecl : Ast.Decl :=
    .function
      { name := hasResultPredicate
        params := [{ name := "value", ty := .int }]
        returnType := .bool
        body := hasResultBody
        doc := some "Some valid external-parser input denotes this representable value." }
  let traitDecl : Ast.Decl :=
    .trait
      { name := contractTrait
        doc := some
          "Proof obligations for an external parser after mapping its output to Triptych's \
          specification integer."
        items := baseItems ++ printerItems }
  if format.hasPrinter then
    [resultDecl, hasResultDecl, traitDecl]
  else
    [resultDecl, traitDecl]

/-- Build the Verus AST for the external-parser proof obligations. -/
def buildSoundnessAst (format : FormatInput) : Except String Ast.Module := do
  validateReadableSpecInput format
  pure
    { header :=
        [s!"Generated by Triptych from `triptych {format.name}`.",
         "External-parser proof obligations; no parser implementation or proof is assumed.",
         "Implement the generated trait for the optimized production parser."]
      imports := ["super::spec::*", "vstd::prelude::*"]
      declarations := soundnessDeclarations format }

/-- Generate the Verus external-parser soundness-contract scaffold. -/
def emitSoundness (format : FormatInput) : Except String String := do
  pure (prettyPrintModule (← buildSoundnessAst format))

private def emitParserSource (format : FormatInput) (parsePlan : ParsePlan) :
    Except String String :=
  match parsePlan with
  | .cursor scanPlan => do
      let proofPlan ← buildStraightProofPlan format scanPlan
      let program := lowerScanPlan scanPlan
      pure <|
        instantiateDirectParser format program proofPlan.root.stop
          (renderStraightSuccessProof format proofPlan)
          (renderStraightViewProof format proofPlan)
          (renderStraightCompletenessProof format proofPlan)
  | .search searchPlan => do
      let grammar ← compileFlatGrammar format.grammar
      let executablePlan? ←
        match compileSemanticPlan format.valueExpr format.wfConstraints format.valueConstraints
            format.ofSpec with
        | .ok semanticPlan =>
            match compileExecutableSemanticPlan grammar semanticPlan with
            | .ok executablePlan => pure (some executablePlan)
            | .error _ => pure none
        | .error _ => pure none
      let program := lowerSearchPlan searchPlan
      match renderSearchMachineParser format grammar program executablePlan? with
      | .ok source => pure source
      | .error message =>
          throw
            s!"Verus backend: specialized search-machine emission failed; \
              the runtime fallback is disabled: {message}"
  | .scanner reason =>
      throw
        s!"Verus backend: grammar could not be lowered to a specialized parser: {reason}"

/-- The regenerated files that jointly form one proof-carrying Rust parser artifact.
    `parser` is never returned without the specification named by its Verus contract. -/
structure CertifiedRustOutput where
  spec : String
  parser : String

/-- Emit a readable specification and executable certificate from an already selected shared
    parser plan. A supplied cursor plan is rechecked against the format grammar before code
    generation, so callers cannot attach an unrelated optimized program. -/
def emitCertifiedRustWithPlan (format : FormatInput) (parsePlan : ParsePlan) :
    Except String CertifiedRustOutput := do
  let _ ← compileFlatGrammar format.grammar
  match parsePlan with
  | .cursor scanPlan =>
      unless scanPlan.certifiedFor format.grammar do
        throw "Verus backend: cursor ParsePlan does not match the format grammar"
  | .search searchPlan =>
      unless searchPlan.matchesGrammar format.grammar do
        throw "Verus backend: search ParsePlan does not match the format grammar"
  | .scanner reason =>
      throw
        s!"Verus backend: scanner ParsePlans are not emitted; specialized lowering failed: \
          {reason}"
  let spec ← emitSpec format
  let parser ← emitParserSource format parsePlan
  pure { spec, parser }

/-- Compile the shared parser plan, then emit the readable specification and executable
    certificate atomically. -/
def emitCertifiedRust (format : FormatInput) : Except String CertifiedRustOutput :=
  emitCertifiedRustWithPlan format (compileParsePlan format.grammar)

end Triptych.Backend.Verus

namespace Triptych.Verus

/-- DSL-facing adapter used by the `verus "path"` Triptych clause. -/
def emitSpec (name : String) (grammar : Grammar) (valueExpr : ValExpr)
    (wfConstraints valueConstraints : List Constraint) (ofSpec toSpec : Lean.Name) :
    Except String String := do
  Backend.Verus.emitSpec
    { name
      grammar
      valueExpr
      wfConstraints
      valueConstraints
      ofSpec := ofSpec.toString
      toSpec := toSpec.toString }

/-- DSL-facing adapter for the sibling Verus `soundness.rs` scaffold. -/
def emitSoundness (name : String) (grammar : Grammar) (valueExpr : ValExpr)
    (wfConstraints valueConstraints : List Constraint) (ofSpec toSpec : Lean.Name)
    (hasPrinter : Bool := false) :
    Except String String := do
  Backend.Verus.emitSoundness
    { name
      grammar
      valueExpr
      wfConstraints
      valueConstraints
      ofSpec := ofSpec.toString
      toSpec := toSpec.toString
      hasPrinter }

/-- DSL-facing adapter for one proof-carrying Rust parser artifact. -/
def emitCertifiedRust (name : String) (grammar : Grammar) (valueExpr : ValExpr)
    (wfConstraints valueConstraints : List Constraint) (ofSpec toSpec : Lean.Name) :
    Except String Backend.Verus.CertifiedRustOutput := do
  Backend.Verus.emitCertifiedRust
    { name
      grammar
      valueExpr
      wfConstraints
      valueConstraints
      ofSpec := ofSpec.toString
      toSpec := toSpec.toString }

/-- DSL-facing adapter when the elaborator has already compiled the shared parser plan used by
    the Lean backend. -/
def emitCertifiedRustWithPlan (name : String) (grammar : Grammar) (valueExpr : ValExpr)
    (wfConstraints valueConstraints : List Constraint) (ofSpec toSpec : Lean.Name)
    (parsePlan : ParsePlan) : Except String Backend.Verus.CertifiedRustOutput := do
  Backend.Verus.emitCertifiedRustWithPlan
    { name
      grammar
      valueExpr
      wfConstraints
      valueConstraints
      ofSpec := ofSpec.toString
      toSpec := toSpec.toString }
    parsePlan

end Triptych.Verus
