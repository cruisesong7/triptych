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
import Triptych.Backend.Verus.Desugar
import Triptych.Backend.Verus.Alignment
import Triptych.Backend.Verus.PrettyPrint

/-!
# Verus backend

The Verus generation pipeline has four stages:

1. the Triptych elaborator supplies the already-parsed grammar, value expression, phased
   constraints, and conversion names in `Verus.FormatInput`;
2. this module validates that input and translates the readable specification to the semantic
   Verus AST;
3. `Triptych.Backend.Verus.Desugar` realizes semantic operations as concrete Verus syntax;
4. `Triptych.Backend.Verus.PrettyPrint` pretty-prints that Surface AST as Verus source.

`Verus.FormatInput` is only a convenience record at the elaborator/backend boundary. It is not
another intermediate language: its grammar, value, and constraint fields are the same Triptych
values used by Lean generation.

Value and constraint translation is checked against the Triptych denotation in
`Triptych.Backend.Verus.Translation`. Concrete value and arithmetic-constraint expressions are
checked after desugaring in `Triptych.Backend.Verus.Alignment`, while generated helper bodies are
checked in `Triptych.Backend.Verus.SurfaceSemantics`. The target pretty-printer remains a separate
trusted boundary.

This module emits the readable specification and a separate soundness-contract scaffold. The
scaffold states the obligations for an external parser without assuming or implementing that
parser. A concrete Rust integration implements the generated trait and proves its methods.
-/

namespace Triptych.Backend.Verus

open Semantic

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

private def allLiteralsAsciiSym : Sym → Bool
  | .lit literal => literal.toList.all (·.toNat < 128)
  | .rep separator item _ _ =>
      separator.toList.all (·.toNat < 128) && allLiteralsAsciiSym item
  | _ => true

private def supportedSym : Sym → Bool
  | .lit literal => literal.toList.all (·.toNat < 128)
  | .ref _ => true
  | .term _ _ => true
  | .str => false
  | .rep _ _ _ _ => false

private def allSymbols (grammar : Grammar) : List Sym :=
  grammar.prods.flatMap fun production =>
    production.alts.flatMap fun sequence => sequence.map (·.sym)

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

private def validateInput (format : FormatInput) : Except String Unit := do
  let names := format.grammar.prods.map (·.name)
  if duplicate? names then
    throw "Verus backend: production names must be unique"
  if !format.grammar.refsResolve then
    throw "Verus backend: every nonterminal reference must resolve"
  if let some cycle := format.grammar.cycle? then
    throw s!"Verus backend: recursive grammars are unsupported: \
      {String.intercalate " -> " cycle}"
  if !format.grammar.staticUnique then
    throw "Verus backend: the grammar must pass Triptych's static uniqueness checker"
  if !(allSymbols format.grammar).all allLiteralsAsciiSym then
    throw "Verus backend: only ASCII literals are currently supported"
  if !(allSymbols format.grammar).all supportedSym then
    throw "Verus backend: string literals and separated repetition are not yet supported"
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

private def textLength (expression : Semantic.Expr) : Semantic.Expr :=
  .textLen expression

private def tokenRunCondition (token : TokClass) (length : LenSpec)
    (input : Semantic.Expr) : Semantic.Expr :=
  let size := textLength input
  let lengthCondition := match length with
    | .exactly width => .intEq size (.intLit (Int.ofNat width))
    | .between lower upper =>
        .boolAnd
          (.intLe (.intLit (Int.ofNat lower)) size)
          (.intLe size (.intLit (Int.ofNat upper)))
    | .atLeastOne => .intLe (.intLit 1) size
  let index : Semantic.Expr := .var "i"
  let inRange :=
    .boolAnd (.intLe (.intLit 0) index) (.intLt index size)
  let charactersValid :=
    .forallE [{ name := "i", ty := .int }] true
      (.boolImplies inRange (.isToken token (.textIndex input index)))
  .boolAnd lengthCondition charactersValid

private def symbolCondition (formatName : String) (symbol : Sym)
    (input : Semantic.Expr) : Semantic.Expr :=
  match symbol with
  | .lit literal => .textEq input (.textLit literal)
  | .ref name => .call (productionName formatName name) [input]
  | .term token length => tokenRunCondition token length input
  | .str => .boolLit false
  | .rep _ _ _ _ => .boolLit false

private def binderBase (item : SymItem) : Option String :=
  match item.sym with
  | .lit _ => if item.optional then some "literal" else none
  | .ref name => some (snakeCase (Triptych.surfaceBinder name))
  | .term .digit _ => some "digits"
  | .term .hexDigit _ => some "hex_digits"
  | .term .bit _ => some "bits"
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

private def itemExpression (item : SymItem) (binder? : Option String) : Semantic.Expr :=
  match binder? with
  | some binder => .var binder
  | none =>
      match item.sym with
      | .lit literal => .textLit literal
      | _ => .textLit ""

private def itemCondition (formatName : String) (item : SymItem)
    (binder? : Option String) : Option Semantic.Expr :=
  match binder? with
  | none => none
  | some binder =>
      let input : Semantic.Expr := .var binder
      let present := symbolCondition formatName item.sym input
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

private def sequenceCondition (formatName : String) (fields : List FieldSpec)
    (input : Semantic.Expr) (items : List SymItem) (view? : Option Semantic.Expr := none) : Semantic.Expr :=
  let binders := assignBinders items
  let pieces := (items.zip binders).map fun (item, binder?) =>
    itemExpression item binder?
  let itemConditions := (items.zip binders).filterMap fun (item, binder?) =>
    itemCondition formatName item binder?
  let decomposition := .textEq input (.concatAll pieces)
  let viewConditions := match view? with
    | none => []
    | some view =>
        let bindings := directCaptureBindings fields items binders
        fields.map fun field =>
          let captured := match bindings.find? (·.1 == field.capture) with
            | some (_, binder) => Semantic.Expr.var binder
            | none => .textLit ""
          .textEq (.field view field.ident) captured
  let body := .andAll (decomposition :: itemConditions ++ viewConditions)
  let quantified := binders.filterMap (·.map fun name => Semantic.Binder.mk name .text)
  if quantified.isEmpty then body else .existsE quantified body

private def productionCondition (formatName : String) (fields : List FieldSpec)
    (input : Semantic.Expr) (production : Production) : Semantic.Expr :=
  .orAll (production.alts.map (sequenceCondition formatName fields input ·))

private def rootViewCondition (formatName : String) (fields : List FieldSpec)
    (input view : Semantic.Expr) (production : Production) : Semantic.Expr :=
  .orAll (production.alts.map
    (sequenceCondition formatName fields input · (some view)))

private def captureParams (fields : List FieldSpec) (captures : List String) : List Semantic.Param :=
  captures.map fun capture =>
    { name := fieldIdent fields capture, ty := .text }

private def captureArgs (fields : List FieldSpec) (captures : List String) : List Semantic.Expr :=
  captures.map fun capture => .capture (fieldIdent fields capture) capture

private def viewArgs (fields : List FieldSpec) (captures : List String) : List Semantic.Expr :=
  captures.map fun capture => .field (.var "view") (fieldIdent fields capture)

private def boolFunction (name : String) (params : List Semantic.Param) (body : Semantic.Expr)
    (doc : Option String := none) : Semantic.Decl :=
  .function { name, params, returnType := .bool, body, doc }

private def intFunction (name : String) (params : List Semantic.Param) (body : Semantic.Expr)
    (doc : Option String := none) : Semantic.Decl :=
  .function { name, params, returnType := .int, body, doc }

private def productionDeclarations (format : FormatInput)
    (fields : List FieldSpec) : List Semantic.Decl :=
  format.grammar.prods.map fun production =>
    boolFunction (productionName format.name production.name)
      [{ name := "input", ty := .text }]
      (productionCondition format.name fields (.var "input") production)
      (some s!"Lean counterpart: `{format.name}.IsWf.{production.name}`.")

private def constraintDeclarations (format : FormatInput) (fields : List FieldSpec)
    (formatPrefix viewType : String) : List Semantic.Decl :=
  let makePhase (constraints : List Constraint) (functionSuffix viewSuffix satisfiesSuffix
      leanName : String) : List Semantic.Decl :=
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
    (fields : List FieldSpec) : Except String (List Semantic.Decl) := do
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
    { name := "input", ty := .text : Semantic.FieldDecl } ::
      fields.map fun (field : FieldSpec) => { name := field.ident, ty := .text }
  let rootWf := productionName format.name format.grammar.start
  let matchesView := formatPrefix ++ "_matches_view"
  let wfConstraintCall : Semantic.Expr :=
    if hasWfConstraints then
      .call (formatPrefix ++ "_view_wf_constraints") [.var "view"]
    else
      .boolLit true
  let valueConstraintCall : Semantic.Expr :=
    if hasValueConstraints then
      .call (formatPrefix ++ "_view_constraints") [.var "view"]
    else
      .boolLit true
  let viewValid : Semantic.Expr := .boolAnd wfConstraintCall valueConstraintCall
  let isWfBody : Semantic.Expr :=
    if hasWfConstraints then
      .boolAnd
        (.call rootWf [.var "input"])
        (.call (formatPrefix ++ "_satisfies_wf_constraints") [.var "input"])
    else
      .call rootWf [.var "input"]
  let isValidBody : Semantic.Expr :=
    if hasValueConstraints then
      .boolAnd
        (.call (formatPrefix ++ "_is_wf") [.var "input"])
        (.call (formatPrefix ++ "_satisfies_constraints") [.var "input"])
    else
      .call (formatPrefix ++ "_is_wf") [.var "input"]
  let declarations : List Semantic.Decl :=
    [ Semantic.Decl.structure { name := viewType, fields := viewFields },
      boolFunction matchesView
        [{ name := "input", ty := .text }, { name := "view", ty := .named viewType }]
        (.boolAnd
          (.textEq (.field (.var "view") "input") (.var "input"))
          (rootViewCondition format.name fields (.var "input") (.var "view") root)),
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

/-- Validate and translate one elaborated Triptych format into its semantic Verus specification. -/
def translateSpecModule (format : FormatInput) : Except String Semantic.Module := do
  validateInput format
  let fields := fieldsFor format.grammar
  let formatDecls ← formatDeclarations format fields
  let declarations := productionDeclarations format fields ++ formatDecls
  pure
    { header :=
        [s!"Generated by Triptych from `triptych {format.name}`.",
         "Source ASTs: Grammar -> IsWf, ValExpr -> value, Constraint -> constraint phases.",
         s!"Lean conversion boundary: ofSpec `{format.ofSpec}`, toSpec `{format.toSpec}`."]
      imports := ["vstd::prelude::*"]
      declarations }

/-- Generate the readable Verus specification for one elaborated Triptych format. -/
def emitSpec (format : FormatInput) : Except String String := do
  let semanticModule ← translateSpecModule format
  let targetModule := desugarModule semanticModule
  pure (prettyPrintModule targetModule)

private def optionEqualsSome (option result : Surface.Expr) : Surface.Expr :=
  .matchOption option { name := "parsed", ty := .int }
    (.intEq (.var "parsed") result)
    (.boolLit false)

private def optionIsNone (option : Surface.Expr) : Surface.Expr :=
  .matchOption option { name := "parsed", ty := .int }
    (.boolLit false)
    (.boolLit true)

private def boolNot (expression : Surface.Expr) : Surface.Expr :=
  .boolNot expression

private def soundnessDeclarations (format : FormatInput) : List Surface.Decl :=
  let formatPrefix := snakeCase format.name
  let viewType := typeName format.name ++ "View"
  let contractTrait := typeName format.name ++ "ExternalParserContract"
  let resultPredicate := formatPrefix ++ "_matches_result"
  let input : Surface.Expr := .var "input"
  let result : Surface.Expr := .var "value"
  let view : Surface.Expr := .var "view"
  let parseResult := Surface.Expr.call "Self::parse_to_spec" [input]
  let parsesValue := optionEqualsSome parseResult result
  let rejects := optionIsNone parseResult
  let isValid := Surface.Expr.call (formatPrefix ++ "_is_valid") [input]
  let matchesResult := Surface.Expr.call resultPredicate [input, result]
  let resultBody :=
    Surface.Expr.existsE [{ name := "view", ty := .named viewType }]
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

/-- Generate a Verus trait that states the external-parser proof obligations. -/
def translateSoundnessModule (format : FormatInput) : Except String Surface.Module := do
  validateInput format
  pure
    { header :=
        [s!"Generated by Triptych from `triptych {format.name}`.",
         "External-parser proof obligations; no parser implementation or proof is assumed.",
         "Implement the generated trait for an adapter connected to the production parser."]
      imports := ["vstd::prelude::*", "crate::spec::*"]
      declarations := soundnessDeclarations format }

/-- Generate the Verus external-parser soundness-contract scaffold. -/
def emitSoundness (format : FormatInput) : Except String String := do
  pure (prettyPrintModule (← translateSoundnessModule format))

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

end Triptych.Verus
