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
import Triptych.Architecture.CursorProgram
import Triptych.Backend.Verus.RuntimeModel

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
fallback. Eligible deterministic fixed-point grammars compile through the shared `ScanPlan`,
whose verified lowering produces `CursorProgram`, and then to direct single-cursor code with
generated grammar-witness proofs. Other constructors in the shared acyclic `Grammar` AST use the
complete proof-carrying source-grammar scanner. A separate write-once `soundness.rs` states
obligations only for an optional external parser.
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
  functionName formatName ("is_wf_" ++ snakeCase production)

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

private def fieldsFor (grammar : Grammar) : List FieldSpec :=
  (rootCaptures grammar).map fun capture =>
    { capture, ident := snakeCase (Triptych.surfaceBinder capture) }

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

private def validateReadableSpecInput (format : FormatInput) : Except String Unit := do
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
  if !format.valueExpr.countCaptures.isEmpty ||
      !(format.wfConstraints ++ format.valueConstraints).all
        (·.countCaptures.isEmpty) then
    throw "Verus backend: repeated-capture `count` expressions are not yet supported"
  validateCaptureShape format.grammar
  let available := rootCaptures format.grammar
  let required :=
    (format.valueExpr.captures ++
      (format.wfConstraints ++ format.valueConstraints).flatMap Constraint.captures).eraseDups
  for capture in required do
    if !available.contains capture then
      throw s!"Verus backend: capture `{capture}` must be a direct reference in the root \
        production"
  let equalityCaptures :=
    (format.wfConstraints ++ format.valueConstraints).flatMap stringEqualityCaptures
  for capture in equalityCaptures.eraseDups do
    if !requiredInEveryRootAlternative format.grammar capture then
      throw s!"Verus backend: string equality on `{capture}` requires that capture to be a \
        non-optional direct reference in every root alternative"

/-! ## Generic proof-carrying Rust parser -/

/-- Canonical direct scanner. Verus proves its source-grammar semantics once; generated format
    modules only serialize their grammar tables and call its checked entry point. -/
private def runtimeParserTemplate : String :=
  include_str "Verus/RuntimeParser.rs.in"

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
      "GrammarSymbol::Repetition { separator: " ++ String.quote separator ++
        ", item: " ++ toString item ++
        ", lower: " ++ toString lower ++
        ", upper: " ++ renderNatOption upper ++ " }"

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

private def instantiateRuntimeParser (format : FormatInput) (grammar : FlatGrammar) : String :=
  let function := functionName format.name "parse_candidate"
  let grammarSymbols := renderArray "        " (grammar.symbols.map renderGrammarSymbol)
  let grammarItems := renderArray "        " (grammar.items.map renderGrammarItem)
  let grammarAlternatives :=
    renderArray "        " (grammar.alternatives.map renderGrammarAlternative)
  let grammarProductions :=
    renderArray "        " (grammar.productions.map renderGrammarProduction)
  let leftBrace := "{"
  let rightBrace := "}"
  s!"// Generated by Triptych from `triptych {format.name}`.
// Proof-carrying direct scanner: Verus checks execution against the emitted source grammar.
// This file is regenerated; it contains no external parser or manually supplied parser proof.
{productionTableComment grammar}

{runtimeParserTemplate}

verus! {leftBrace}

/// Parse one complete input using the source grammar emitted from `triptych {format.name}`.
///
/// The checked runtime first validates every table index and termination invariant. It then
/// executes the same ordered grammar semantics used by `checked_grammar_parse_candidate`.
pub fn {function}(input: &str) -> (result: Option<Candidate>)
    ensures
        match result {leftBrace}
            Some(candidate) => candidate.end == input@.len(),
            None => true,
        {rightBrace},
{leftBrace}
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

    parse_checked_grammar_candidate(&source_grammar, input)
{rightBrace}

{rightBrace} // verus!
"

/-- Generate the parser source used inside `emitCertifiedRust`. Keeping this private prevents
    callers from treating executable Rust as a separate, potentially uncertified artifact. -/
private def emitCertifiedParserSource (format : FormatInput) : Except String String := do
  let grammar ← compileFlatGrammar format.grammar
  pure (instantiateRuntimeParser format grammar)

/-! ## Grammar-specialized direct parser -/

/-- Verified runtime primitives shared by specialized plans. The template deliberately leaves
    its `verus!` block open so generated plan declarations are checked in the same module. -/
private def directParserTemplate : String :=
  include_str "Verus/DirectParser.rs.in"

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

private def parsePlanCompletenessFunction (format : FormatInput) : String :=
  functionName format.name "is_wf_implies_parse_plan"

private def grammarWfFunction (format : FormatInput) : String :=
  productionName format.name format.grammar.start

private def positionName (index : Nat) : String :=
  s!"position_{index}"

private def indentText (depth : Nat) (source : String) : String :=
  let indent := String.ofList (List.replicate (depth * 4) ' ')
  String.intercalate "\n" ((source.splitOn "\n").map fun line =>
    if line.isEmpty then line else indent ++ line)

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

private structure FixedPointPlan where
  signCapture : String
  signCharacter : Char
  naturalCapture : String
  separatorCharacter : Char
  fractionCapture : String
  fractionLower : Nat
  fractionUpper : Nat

private def fixedPointPlan? : List CursorOp → Option FixedPointPlan
  | [ .beginCapture signCapture _,
      .consumeOptional signCharacter,
      .endCapture signCapture',
      .beginCapture naturalCapture _,
      .consumeRun .digit .greedyAtLeastOne,
      .endCapture naturalCapture',
      .expect separatorCharacter,
      .beginCapture fractionCapture _,
      .consumeRun .digit (.greedyBetween fractionLower fractionUpper),
      .endCapture fractionCapture' ] =>
      if signCapture == signCapture' &&
          naturalCapture == naturalCapture' &&
          fractionCapture == fractionCapture' then
        some
          { signCapture
            signCharacter
            naturalCapture
            separatorCharacter
            fractionCapture
            fractionLower
            fractionUpper }
      else
        none
  | _ => none

private def verusCharacterLiteral (character : Char) : String :=
  "'\\u{" ++ String.ofList (Nat.toDigits 16 character.toNat) ++ "}'"

private def fixedPointProofTemplate : String :=
  include_str "Verus/FixedPointPlanProof.rs.in"

private def fixedPointCompletenessTemplate : String :=
  include_str "Verus/FixedPointPlanCompleteness.rs.in"

private def fixedPointReplacements (format : FormatInput) (shape : FixedPointPlan) :
    List (String × String) :=
  let sign := captureField shape.signCapture
  let natural := captureField shape.naturalCapture
  let fraction := captureField shape.fractionCapture
  [ ("__COMPLETENESS_FUNCTION__", parsePlanCompletenessFunction format),
    ("__PARSE_PLAN__", parsePlanFunction format),
    ("__SIGN_WF__", productionName format.name shape.signCapture),
    ("__NATURAL_WF__", productionName format.name shape.naturalCapture),
    ("__FRACTION_WF__", productionName format.name shape.fractionCapture),
    ("__ROOT_WF__", productionName format.name format.grammar.start),
    ("__SIGN_CHAR_CODE__", toString shape.signCharacter.toNat),
    ("__SIGN_CHAR_LITERAL__", verusCharacterLiteral shape.signCharacter),
    ("__SEPARATOR_CHAR_LITERAL__", verusCharacterLiteral shape.separatorCharacter),
    ("__FRACTION_LOWER__", toString shape.fractionLower),
    ("__FRACTION_UPPER__", toString shape.fractionUpper),
    ("__SIGN__", sign),
    ("__NATURAL__", natural),
    ("__FRACTION__", fraction) ]

private def instantiateFixedPointTemplate (format : FormatInput) (shape : FixedPointPlan)
    (template : String) : String :=
  (fixedPointReplacements format shape).foldl (fun source replacement =>
    source.replace replacement.1 replacement.2) template

private def renderSuccessProof? (format : FormatInput) (program : CursorProgram) :
    Option String := do
  let shape ← fixedPointPlan? program.operations
  pure (instantiateFixedPointTemplate format shape fixedPointProofTemplate)

private def renderCompletenessProof? (format : FormatInput) (program : CursorProgram) :
    Option String := do
  let shape ← fixedPointPlan? program.operations
  pure (instantiateFixedPointTemplate format shape fixedPointCompletenessTemplate)

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

private def renderExecOps (format : FormatInput) (program : CursorProgram) :
    List CursorOp → Nat → String → String
  | [], _, position =>
      "if " ++ position ++ " == input_length {\n" ++
        indentText 1
          ((match renderSuccessProof? format program with
            | some proof => proof ++ "\n"
            | none => "") ++
            renderParseExecResult format program position) ++
        "\n} else {\n    None\n}"
  | .beginCapture capture _ :: rest, index, position =>
      let field := captureField capture
      s!"let {field}_start = {position};\n" ++
        renderExecOps format program rest index position
  | .endCapture capture :: rest, index, position =>
      let field := captureField capture
      s!"let {field}_end = {position};\n" ++
        renderExecOps format program rest index position
  | .consumeOptional character :: rest, index, position =>
      let next := positionName (index + 1)
      s!"let {next} = if {position} < input_length && " ++
        s!"plan_ascii_character_at(input, {position}) == {character.toNat}u8 " ++ "{\n" ++
        s!"    {position} + 1\n" ++
        "} else {\n" ++
        s!"    {position}\n" ++
        "};\n" ++
        renderExecOps format program rest (index + 1) next
  | .expect character :: rest, index, position =>
      let next := positionName (index + 1)
      s!"if {position} < input_length && " ++
        s!"plan_ascii_character_at(input, {position}) == {character.toNat}u8 " ++ "{\n" ++
        indentText 1
          (s!"let {next} = {position} + 1;\n" ++
            renderExecOps format program rest (index + 1) next) ++
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
            indentText 1 (renderExecOps format program rest (index + 1) next) ++
            "\n} else {\n    None\n}") ++
        "\n} else {\n    None\n}"
  | .consumeRun token run :: rest, index, position =>
      let next := positionName (index + 1)
      let condition := renderRunCondition run position next
      s!"let {next} = plan_scan_token_end_exec(input, {position}, input_length, " ++
        renderPlanTokenClass token ++ ");\n" ++
        s!"if {condition} " ++ "{\n" ++
        indentText 1 (renderExecOps format program rest (index + 1) next) ++
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

private def instantiateDirectParser (format : FormatInput) (program : CursorProgram) : String :=
  let leftBrace := "{"
  let rightBrace := "}"
  let completenessProof := (renderCompletenessProof? format program).getD ""
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
      renderExecOps format program program.operations 0 "position_0"
  s!"// Generated by Triptych from `triptych {format.name}`.
// ScanPlan is verified-lowered to CursorProgram, which is compiled away.
// This file is regenerated; it contains no external parser or manually supplied parser proof.

{directParserTemplate}

{renderParseStructures format program}

pub open spec fn {parsePlanFunction format}(input: Seq<char>)
    -> Option<{parseSpecType format}>
{leftBrace}
{indentText 1 specBody}
{rightBrace}

{completenessProof}

/// Direct single-pass parser generated from the format's verified-lowered CursorProgram.
pub fn {parseCandidateFunction format}(input: &str)
    -> (result: Option<{parseResultType format}>)
    ensures
        match result {leftBrace}
            Some(parsed) =>
                {parsePlanFunction format}(input@) == Some(parsed.deep_view())
                    && {grammarWfFunction format}(input@),
            None =>
                {parsePlanFunction format}(input@).is_none()
                    && !{grammarWfFunction format}(input@),
        {rightBrace},
{leftBrace}
{indentText 1 execBody}
{rightBrace}

{rightBrace} // verus!
"

private def emitParserSource (format : FormatInput) : Except String String :=
  match compileScanPlan format.grammar with
  | .ok plan =>
      let program := lowerScanPlan plan
      match renderSuccessProof? format program, renderCompletenessProof? format program with
      | some _, some _ => pure (instantiateDirectParser format program)
      | _, _ => emitCertifiedParserSource format
  | .error _ => emitCertifiedParserSource format

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

private def grammarSupportDeclarations (format : FormatInput)
    (repetitions : List Sym) : List IR.Decl :=
  let hasString := (allSymbols format.grammar).any containsStringSymbol
  (if hasString then stringGrammarDeclarations else []) ++
    repetitions.filterMap (repetitionDeclaration format.name repetitions)

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

private def directCaptureBindings (fields : List FieldSpec)
    (items : List SymItem) (binders : List (Option String)) : List (String × String) :=
  (items.zip binders).filterMap fun (item, binder?) =>
    match item.sym, binder? with
    | .ref capture, some binder =>
        if fields.any (·.capture == capture) then some (capture, binder) else none
    | _, _ => none

private def sequenceCondition (formatName : String) (repetitions : List Sym)
    (fields : List FieldSpec)
    (input : IR.Expr) (items : List SymItem) (view? : Option IR.Expr := none) : IR.Expr :=
  let binders := assignBinders items
  let pieces := (items.zip binders).map fun (item, binder?) =>
    itemExpression item binder?
  let itemConditions := (items.zip binders).filterMap fun (item, binder?) =>
    itemCondition formatName repetitions item binder?
  let decomposition := .textEq input (.concatAll pieces)
  let viewConditions := match view? with
    | none => []
    | some view =>
        let bindings := directCaptureBindings fields items binders
        fields.map fun field =>
          let captured := match bindings.find? (·.1 == field.capture) with
            | some (_, binder) => IR.Expr.var binder
            | none => .textLit ""
          .textEq (.field view field.ident) captured
  let body := .andAll (decomposition :: itemConditions ++ viewConditions)
  let quantified := binders.filterMap (·.map fun name => IR.Binder.mk name .text)
  if quantified.isEmpty then body else .existsE quantified body

private def productionCondition (formatName : String) (repetitions : List Sym)
    (fields : List FieldSpec)
    (input : IR.Expr) (production : Production) : IR.Expr :=
  .orAll (production.alts.map (sequenceCondition formatName repetitions fields input ·))

private def rootViewCondition (formatName : String) (repetitions : List Sym)
    (fields : List FieldSpec)
    (input view : IR.Expr) (production : Production) : IR.Expr :=
  .orAll (production.alts.map
    (sequenceCondition formatName repetitions fields input · (some view)))

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
      (productionCondition format.name repetitions fields (.var "input") production)
      (some s!"Lean counterpart: `{format.name}.IsWf.{production.name}`.")

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

private def formatDeclarations (format : FormatInput) (repetitions : List Sym)
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
          (rootViewCondition format.name repetitions fields
            (.var "input") (.var "view") root)),
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
  let fields := fieldsFor format.grammar
  let repetitions := repetitionsFor format.grammar
  let formatDecls ← formatDeclarations format repetitions fields
  let declarations :=
    grammarSupportDeclarations format repetitions ++
      productionDeclarations format repetitions fields ++ formatDecls
  pure
    { header :=
        [s!"Generated by Triptych from `triptych {format.name}`.",
         "Source ASTs: Grammar -> IsWf, ValExpr -> value, Constraint -> constraint phases.",
         s!"Lean conversion boundary: ofSpec `{format.ofSpec}`, toSpec `{format.toSpec}`."]
      imports :=
        ["vstd::prelude::*"] ++
          if (allSymbols format.grammar).any containsStringSymbol then
            ["vstd::std_specs::char::is_white_space"]
          else
            []
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
  [ .function
      { name := resultPredicate
        params := [{ name := "input", ty := .text }, { name := "value", ty := .int }]
        returnType := .bool
        body := resultBody
        doc := some "The input has a valid typed view whose denotation is this result." },
    .trait
      { name := contractTrait
        doc := some
          "Proof obligations for an external parser after mapping its output to Triptych's \
          specification integer."
        items :=
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
                doc := some "The external parser rejects exactly the invalid inputs." } ] } ]

/-- Build the Verus AST for the external-parser proof obligations. -/
def buildSoundnessAst (format : FormatInput) : Except String Ast.Module := do
  validateReadableSpecInput format
  pure
    { header :=
        [s!"Generated by Triptych from `triptych {format.name}`.",
         "External-parser proof obligations; no parser implementation or proof is assumed.",
         "Implement the generated trait for an adapter connected to the production parser."]
      imports := ["vstd::prelude::*", "crate::spec::*"]
      declarations := soundnessDeclarations format }

/-- Generate the Verus external-parser soundness-contract scaffold. -/
def emitSoundness (format : FormatInput) : Except String String := do
  pure (prettyPrintModule (← buildSoundnessAst format))

/-- The regenerated files that jointly form one proof-carrying Rust parser artifact.
    `parser` is never returned without the specification named by its Verus contract. -/
structure CertifiedRustOutput where
  spec : String
  parser : String

/-- Compile the shared grammar model, then emit the readable specification and executable
    certificate atomically. No parser source is returned unless the direct grammar scanner and
    the specification side have both been generated successfully. -/
def emitCertifiedRust (format : FormatInput) : Except String CertifiedRustOutput := do
  let _ ← compileFlatGrammar format.grammar
  let spec ← emitSpec format
  let parser ← emitParserSource format
  pure { spec, parser }

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
    (wfConstraints valueConstraints : List Constraint) (ofSpec toSpec : Lean.Name) :
    Except String String := do
  Backend.Verus.emitSoundness
    { name
      grammar
      valueExpr
      wfConstraints
      valueConstraints
      ofSpec := ofSpec.toString
      toSpec := toSpec.toString }

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

end Triptych.Verus
