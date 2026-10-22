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

import Triptych.Architecture.Constraint
import Triptych.Backend.Verus.RuntimeModel

/-!
# Verus executable semantic plans

The readable Verus specification remains `Int`-valued, exactly like Triptych's shared
`ValExpr`. An executable Rust parser needs one additional decision: how the declared Lean
`ofSpec` conversion is represented at runtime.

This module makes that boundary explicit and fail-closed. It recognizes the conversions for
the Cedar extension examples and records enough structure for executable code generation:

* Decimal, Duration, and Datetime return an `i64`;
* IPv4 returns a family/address/prefix value with a `u32` address;
* IPv6 returns a family/address/prefix value with a `u128` address.

Packed IP denotations are decomposed before runtime generation. In particular, IPv6 never
materializes the artificial 135-bit integer `address * 129 + prefix`; the generated parser
computes the address and prefix separately while its proof relates them to that specification
integer.
-/

namespace Triptych.Backend.Verus

/-- Executable Rust result selected for a Triptych `ofSpec` conversion. -/
inductive SemanticResult where
  /-- Signed 64-bit domain value, used by Decimal, Duration, and Datetime. -/
  | int64
  /-- Cedar-compatible IP family/address/prefix result. -/
  | ip (family : Nat) (addressBits : Nat) (packingRadix : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- One generated lookup into the scanner's capture vector. -/
inductive CaptureSelector where
  | production (production : Nat)
  | qualified (parent production : Nat)
  | repetition (symbol : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- A named semantic field and the scanner key that supplies its source span. -/
structure SemanticField where
  name : String
  selector : CaptureSelector
  deriving Repr, Inhabited, DecidableEq

/-- A conservative closed interval for one executable semantic value. These bounds guide
    primitive lowering only; emitted Verus proofs remain the authority for correctness. -/
structure ValueRange where
  lower : Int
  upper : Int
  deriving Repr, Inhabited, DecidableEq

/-- Primitive interpretation of one captured source span. -/
inductive CaptureReader where
  | natural
  | integer
  | length
  | count
  | hexadecimal
  | hexadecimalSequence
  | segments
  | sign
  | prefixSign
  deriving Repr, Inhabited, DecidableEq

/-- Backend-neutral executable expression with every field name resolved to a scanner key. -/
inductive ExecutableExpr where
  | literal (integer : Int)
  | capture (source : String) (selector : CaptureSelector) (reader : CaptureReader)
      (range : Option ValueRange)
  | add (left right : ExecutableExpr)
  | sub (left right : ExecutableExpr)
  | mul (left right : ExecutableExpr)
  | tdiv (left right : ExecutableExpr)
  | mod (left right : ExecutableExpr)
  | pow (base exponent : ExecutableExpr)
  | neg (expression : ExecutableExpr)
  | iteEq (left right thenBranch elseBranch : ExecutableExpr)
  | iteLt (left right thenBranch elseBranch : ExecutableExpr)
  | iteLe (left right thenBranch elseBranch : ExecutableExpr)
  | iteEmpty (selector : CaptureSelector)
      (thenBranch elseBranch : ExecutableExpr)
  deriving Repr, Inhabited, DecidableEq

/-- Backend-neutral executable constraint over resolved capture keys. -/
inductive ExecutableConstraint where
  | noLeadingZero (selector : CaptureSelector)
  | stringEq (selector : CaptureSelector) (literal : String)
  | card (operation : CardOp) (minimum : Nat) (selectors : List CaptureSelector)
  | le (left right : ExecutableExpr)
  | lt (left right : ExecutableExpr)
  | eq (left right : ExecutableExpr)
  | and (left right : ExecutableConstraint)
  deriving Repr, Inhabited, DecidableEq

/-- Fully resolved semantic program consumed by executable backends. -/
inductive ExecutableSemanticPlan where
  | int64
      (expression : ExecutableExpr)
      (wfConstraints valueConstraints : List ExecutableConstraint)
  | ip
      (family addressBits packingRadix : Nat)
      (addressExpr prefixExpr : ExecutableExpr)
      (wfConstraints valueConstraints : List ExecutableConstraint)
  deriving Repr, Inhabited, DecidableEq

/-- Proof-facing environment for the executable semantic plan. Runtime backends construct this
    environment from source spans; keeping it abstract here makes the expression semantics
    independent of any concrete Rust representation. -/
abbrev ExecutableEnv := CaptureSelector → Option String

def CaptureReader.eval (source : Option String) : CaptureReader → Int
  | .natural | .count =>
      match source with
      | some text => readNat text
      | none => 0
  | .integer =>
      match source with
      | some text => readInt text
      | none => 0
  | .length =>
      match source with
      | some text => text.length
      | none => 0
  | .hexadecimal =>
      match source with
      | some text => hexOf text
      | none => 0
  | .hexadecimalSequence =>
      match source with
      | some text => hexSeqOf text
      | none => 0
  | .segments =>
      match source with
      | some text => segmentsOf text
      | none => 0
  | .sign | .prefixSign =>
      match source with
      | some text => signOf text
      | none => 1

private def ValueRange.hull (left right : ValueRange) : ValueRange :=
  { lower := min left.lower right.lower
    upper := max left.upper right.upper }

private def ValueRange.add (left right : ValueRange) : ValueRange :=
  { lower := left.lower + right.lower
    upper := left.upper + right.upper }

private def ValueRange.sub (left right : ValueRange) : ValueRange :=
  { lower := left.lower - right.upper
    upper := left.upper - right.lower }

private def ValueRange.mul (left right : ValueRange) : ValueRange :=
  let products :=
    [left.lower * right.lower, left.lower * right.upper,
      left.upper * right.lower, left.upper * right.upper]
  { lower := products.foldl min products.head!
    upper := products.foldl max products.head! }

private def ValueRange.neg (range : ValueRange) : ValueRange :=
  { lower := -range.upper, upper := -range.lower }

/-- Conservatively inferred interval for an executable expression. -/
def ExecutableExpr.range? : ExecutableExpr → Option ValueRange
  | .literal integer => some { lower := integer, upper := integer }
  | .capture _ _ _ range => range
  | .add left right => return (← left.range?).add (← right.range?)
  | .sub left right => return (← left.range?).sub (← right.range?)
  | .mul left right => return (← left.range?).mul (← right.range?)
  | .neg expression => return (← expression.range?).neg
  | .pow base exponent => do
      let baseRange ← base.range?
      let exponentRange ← exponent.range?
      guard (0 ≤ baseRange.lower)
      guard (0 ≤ exponentRange.lower)
      guard (exponentRange.lower = exponentRange.upper)
      let power := exponentRange.lower.toNat
      pure
        { lower := baseRange.lower ^ power
          upper := baseRange.upper ^ power }
  | .iteEq _ _ thenBranch elseBranch
  | .iteLt _ _ thenBranch elseBranch
  | .iteLe _ _ thenBranch elseBranch
  | .iteEmpty _ thenBranch elseBranch =>
      return (← thenBranch.range?).hull (← elseBranch.range?)
  | .tdiv .. | .mod .. => none

def ExecutableExpr.eval (env : ExecutableEnv) : ExecutableExpr → Int
  | .literal integer => integer
  | .capture _ selector reader _ => reader.eval (env selector)
  | .add left right => left.eval env + right.eval env
  | .sub left right => left.eval env - right.eval env
  | .mul left right => left.eval env * right.eval env
  | .tdiv left right => (left.eval env).tdiv (right.eval env)
  | .mod left right => (left.eval env).tmod (right.eval env)
  | .pow base exponent => (base.eval env) ^ (exponent.eval env).toNat
  | .neg expression => -(expression.eval env)
  | .iteEq left right thenBranch elseBranch =>
      if left.eval env = right.eval env then thenBranch.eval env else elseBranch.eval env
  | .iteLt left right thenBranch elseBranch =>
      if left.eval env < right.eval env then thenBranch.eval env else elseBranch.eval env
  | .iteLe left right thenBranch elseBranch =>
      if left.eval env ≤ right.eval env then thenBranch.eval env else elseBranch.eval env
  | .iteEmpty selector thenBranch elseBranch =>
      if (env selector).getD "" = "" then thenBranch.eval env else elseBranch.eval env

def ExecutableConstraint.eval (env : ExecutableEnv) : ExecutableConstraint → Prop
  | .noLeadingZero selector =>
      let text := (env selector).getD ""
      text.startsWith "0" = true → text = "0"
  | .stringEq selector literal =>
      match env selector with
      | some text => text = literal
      | none => True
  | .card operation minimum selectors =>
      let present := presentCount (selectors.map fun selector => (env selector).getD "")
      match operation with
      | .atLeast => minimum ≤ present
      | .atMost => present ≤ minimum
      | .exactlyK => present = minimum
  | .le left right => left.eval env ≤ right.eval env
  | .lt left right => left.eval env < right.eval env
  | .eq left right => left.eval env = right.eval env
  | .and left right => left.eval env ∧ right.eval env

/-- The executable semantic work that follows grammar recognition. -/
inductive SemanticPlan where
  /-- Evaluate the complete value expression and convert it to `i64`. -/
  | int64
      (expression : ValExpr)
      (wfConstraints valueConstraints : List Constraint)
  /-- Evaluate address and prefix separately, then prove their packed specification value. -/
  | ip
      (family addressBits packingRadix : Nat)
      (addressExpr prefixExpr : ValExpr)
      (wfConstraints valueConstraints : List Constraint)
  deriving Repr, Inhabited, DecidableEq

private def finalNameComponent (name : String) : String :=
  (name.splitOn ".").getLastD name

private def int64Conversion (ofSpec : String) : Bool :=
  let component := finalNameComponent ofSpec
  component == "ofInt" ||
    component == "millisToDuration" ||
    component == "millisToDatetime"

private def ipConversion? (ofSpec : String) : Option (Nat × Nat × Nat) :=
  match finalNameComponent ofSpec with
  | "ipv4CodeToNet" => some (4, 32, 33)
  | "ipv6CodeToNet" => some (6, 128, 129)
  | _ => none

private def packedValue? (radix : Nat) : ValExpr → Option (ValExpr × ValExpr)
  | .add (.mul addressExpr (.lit encodedRadix)) prefixExpr =>
      if encodedRadix == Int.ofNat radix then some (addressExpr, prefixExpr) else none
  | _ => none

/-- Compile the executable semantic stage selected by `ofSpec`.

Unknown conversions are rejected rather than emitted with an assumed Rust meaning. IP
conversions additionally require the injective `address * radix + prefix` shape used by the
readable specification. -/
def compileSemanticPlan (expression : ValExpr) (wfConstraints valueConstraints : List Constraint)
    (ofSpec : String) : Except String SemanticPlan := do
  if int64Conversion ofSpec then
    pure (.int64 expression wfConstraints valueConstraints)
  else
    match ipConversion? ofSpec with
    | some (family, addressBits, radix) =>
        let (addressExpr, prefixExpr) ←
          match packedValue? radix expression with
          | some parts => pure parts
          | none =>
              throw s!"Verus backend: `{ofSpec}` requires a value of the form \
                `address * {radix} + prefix`"
        pure (.ip family addressBits radix addressExpr prefixExpr
          wfConstraints valueConstraints)
    | none =>
        throw s!"Verus backend: no executable Rust result mapping is registered for \
          `ofSpec {ofSpec}`"

def SemanticPlan.result : SemanticPlan → SemanticResult
  | .int64 _ _ _ => .int64
  | .ip family addressBits radix _ _ _ _ => .ip family addressBits radix

private def indexOf? [BEq α] (needle : α) : List α → Option Nat
  | [] => none
  | candidate :: rest =>
      if candidate == needle then some 0 else (indexOf? needle rest).map (· + 1)

private def semanticCaptureNames (plan : SemanticPlan) : List String :=
  match plan with
  | .int64 expression wfConstraints valueConstraints =>
      (expression.captures ++
        (wfConstraints ++ valueConstraints).flatMap Constraint.captures).eraseDups
  | .ip _ _ _ addressExpr prefixExpr wfConstraints valueConstraints =>
      (addressExpr.captures ++ prefixExpr.captures ++
        (wfConstraints ++ valueConstraints).flatMap Constraint.captures).eraseDups

private def repetitionSelector? (grammar : FlatGrammar) (capture : String) :
    Option CaptureSelector := do
  guard (capture.endsWith "#count")
  let base := (capture.dropEnd 6).toString
  let production ← indexOf? base (grammar.productions.map (·.name))
  let (_, symbolIndex) ← grammar.symbols.zipIdx.find? fun (symbol, _) =>
    match symbol with
    | .repetition _ item _ _ =>
        grammar.symbols[item]? == some (.reference production)
    | _ => false
  pure (.repetition symbolIndex)

/-- Resolve one Triptych capture name to the key used by the executable scanner. -/
def captureSelector? (grammar : FlatGrammar) (capture : String) :
    Option CaptureSelector :=
  match repetitionSelector? grammar capture with
  | some selector => some selector
  | none =>
      match capture.splitOn "." with
      | [productionName] =>
          CaptureSelector.production <$>
            indexOf? productionName (grammar.productions.map (·.name))
      | [parentName, productionName] => do
          let parent ← indexOf? parentName (grammar.productions.map (·.name))
          let production ← indexOf? productionName (grammar.productions.map (·.name))
          pure (.qualified parent production)
      | _ => none

/-- Resolve every semantic capture to the concrete key emitted by the source-grammar scanner. -/
def compileSemanticFields (grammar : FlatGrammar) (plan : SemanticPlan) :
    Except String (List SemanticField) :=
  (semanticCaptureNames plan).mapM fun name => do
    let selector ← match captureSelector? grammar name with
      | some selector => pure selector
      | none => throw s!"Verus backend: cannot resolve semantic capture `{name}`"
    pure { name, selector }

private def selectorFor (fields : List SemanticField) (name : String) :
    Except String CaptureSelector :=
  match fields.find? (·.name == name) with
  | some field => pure field.selector
  | none => throw s!"Verus backend: semantic capture `{name}` was not resolved"

private def lenSpecUpper? : LenSpec → Option Nat
  | .exactly length => some length
  | .between _ upper => some upper
  | .atLeastOne => none

mutual
  private partial def symbolLengthUpper? (grammar : FlatGrammar) (fuel : Nat) :
      Nat → Option Nat
    | symbolIndex => do
        guard (0 < fuel)
        let symbol ← grammar.symbols[symbolIndex]?
        match symbol with
        | .literal text => pure text.length
        | .stringLiteral => none
        | .reference production =>
            productionLengthUpper? grammar (fuel - 1) production
        | .terminal _ length => lenSpecUpper? length
        | .repetition separator item _ upper => do
            let itemCountBound ← upper
            let itemLength ← symbolLengthUpper? grammar (fuel - 1) item
            pure <| itemCountBound * itemLength +
              (itemCountBound - 1) * separator.length

  private partial def alternativeLengthUpper? (grammar : FlatGrammar) (fuel : Nat)
      (alternative : FlatAlternative) : Option Nat := do
    guard (0 < fuel)
    let items ← (List.range alternative.itemCount).mapM fun offset =>
      grammar.items[alternative.firstItem + offset]?
    items.foldlM (init := 0) fun total item => do
      let length ← symbolLengthUpper? grammar (fuel - 1) item.symbol
      pure (total + length)

  private partial def productionLengthUpper? (grammar : FlatGrammar) (fuel : Nat) :
      Nat → Option Nat
    | productionIndex => do
        guard (0 < fuel)
        let production ← grammar.productions[productionIndex]?
        let alternatives ← (List.range production.alternativeCount).mapM fun offset =>
          grammar.alternatives[production.firstAlternative + offset]?
        let lengths ← alternatives.mapM (alternativeLengthUpper? grammar (fuel - 1))
        let first ← lengths.head?
        pure (lengths.foldl max first)
end

private def CaptureSelector.sourceLengthUpper? (grammar : FlatGrammar) :
    CaptureSelector → Option Nat
  | .production productionIndex =>
      productionLengthUpper? grammar
        (grammar.productions.length + grammar.symbols.length + 1) productionIndex
  | .qualified _ productionIndex =>
      productionLengthUpper? grammar
        (grammar.productions.length + grammar.symbols.length + 1) productionIndex
  | .repetition _ => none

private def CaptureSelector.repetitionUpper? (grammar : FlatGrammar) :
    CaptureSelector → Option Nat
  | .repetition symbol => do
      let .repetition _ _ _ upper ← grammar.symbols[symbol]?
        | none
      upper
  | _ => none

private def decimalUpper? (digits : Nat) : Option Int := do
  guard (digits ≤ 38)
  pure ((10 : Int) ^ digits - 1)

private def hexadecimalUpper? (digits : Nat) : Option Int := do
  guard (digits ≤ 32)
  pure ((16 : Int) ^ digits - 1)

/-- Range implied by the source grammar for one primitive capture interpretation. -/
def captureReaderRange? (grammar : FlatGrammar) (selector : CaptureSelector) :
    CaptureReader → Option ValueRange
  | .natural => do
      let length ← selector.sourceLengthUpper? grammar
      pure { lower := 0, upper := ← decimalUpper? length }
  | .length => do
      let length ← selector.sourceLengthUpper? grammar
      pure { lower := 0, upper := length }
  | .count => do
      let itemCountBound ← selector.repetitionUpper? grammar
      pure { lower := 0, upper := itemCountBound }
  | .hexadecimal => do
      let length ← selector.sourceLengthUpper? grammar
      pure { lower := 0, upper := ← hexadecimalUpper? length }
  | .sign | .prefixSign => some { lower := -1, upper := 1 }
  | .integer | .hexadecimalSequence | .segments => none

private partial def compileExecutableExpr (grammar : FlatGrammar)
    (fields : List SemanticField) :
    ValExpr → Except String ExecutableExpr
  | .lit integer => pure (.literal integer)
  | .nat field => do
      let selector ← selectorFor fields field
      pure (.capture field selector .natural (captureReaderRange? grammar selector .natural))
  | .int field => do
      let selector ← selectorFor fields field
      pure (.capture field selector .integer (captureReaderRange? grammar selector .integer))
  | .len field => do
      let selector ← selectorFor fields field
      pure (.capture field selector .length (captureReaderRange? grammar selector .length))
  | .count field => do
      let source := field ++ "#count"
      let selector ← selectorFor fields source
      pure (.capture source selector .count (captureReaderRange? grammar selector .count))
  | .hex field => do
      let selector ← selectorFor fields field
      pure (.capture field selector .hexadecimal
        (captureReaderRange? grammar selector .hexadecimal))
  | .hexSeq field => do
      let selector ← selectorFor fields field
      pure (.capture field selector .hexadecimalSequence
        (captureReaderRange? grammar selector .hexadecimalSequence))
  | .segments field => do
      let selector ← selectorFor fields field
      pure (.capture field selector .segments (captureReaderRange? grammar selector .segments))
  | .signOf field => do
      let selector ← selectorFor fields field
      pure (.capture field selector .sign (captureReaderRange? grammar selector .sign))
  | .prefixSign field => do
      let selector ← selectorFor fields field
      pure (.capture field selector .prefixSign
        (captureReaderRange? grammar selector .prefixSign))
  | .add left right => do
      pure (.add (← compileExecutableExpr grammar fields left)
        (← compileExecutableExpr grammar fields right))
  | .sub left right => do
      pure (.sub (← compileExecutableExpr grammar fields left)
        (← compileExecutableExpr grammar fields right))
  | .mul left right => do
      pure (.mul (← compileExecutableExpr grammar fields left)
        (← compileExecutableExpr grammar fields right))
  | .tdiv left right => do
      pure (.tdiv (← compileExecutableExpr grammar fields left)
        (← compileExecutableExpr grammar fields right))
  | .mod left right => do
      pure (.mod (← compileExecutableExpr grammar fields left)
        (← compileExecutableExpr grammar fields right))
  | .pow base exponent => do
      pure (.pow (← compileExecutableExpr grammar fields base)
        (← compileExecutableExpr grammar fields exponent))
  | .neg expression => do
      pure (.neg (← compileExecutableExpr grammar fields expression))
  | .iteEq left right thenBranch elseBranch => do
      pure (.iteEq
        (← compileExecutableExpr grammar fields left)
        (← compileExecutableExpr grammar fields right)
        (← compileExecutableExpr grammar fields thenBranch)
        (← compileExecutableExpr grammar fields elseBranch))
  | .iteLt left right thenBranch elseBranch => do
      pure (.iteLt
        (← compileExecutableExpr grammar fields left)
        (← compileExecutableExpr grammar fields right)
        (← compileExecutableExpr grammar fields thenBranch)
        (← compileExecutableExpr grammar fields elseBranch))
  | .iteLe left right thenBranch elseBranch => do
      pure (.iteLe
        (← compileExecutableExpr grammar fields left)
        (← compileExecutableExpr grammar fields right)
        (← compileExecutableExpr grammar fields thenBranch)
        (← compileExecutableExpr grammar fields elseBranch))
  | .iteEmpty field thenBranch elseBranch => do
      pure (.iteEmpty
        (← selectorFor fields field)
        (← compileExecutableExpr grammar fields thenBranch)
        (← compileExecutableExpr grammar fields elseBranch))

private partial def compileExecutableConstraint (grammar : FlatGrammar)
    (fields : List SemanticField) :
    Constraint → Except String ExecutableConstraint
  | .noLeadingZero field => do
      pure (.noLeadingZero (← selectorFor fields field))
  | .strEq field literal => do
      pure (.stringEq (← selectorFor fields field) literal)
  | .card operation minimum fieldNames => do
      pure (.card operation minimum (← fieldNames.mapM (selectorFor fields)))
  | .le left right => do
      pure (.le (← compileExecutableExpr grammar fields left)
        (← compileExecutableExpr grammar fields right))
  | .lt left right => do
      pure (.lt (← compileExecutableExpr grammar fields left)
        (← compileExecutableExpr grammar fields right))
  | .eq left right => do
      pure (.eq (← compileExecutableExpr grammar fields left)
        (← compileExecutableExpr grammar fields right))
  | .and left right => do
      pure (.and
        (← compileExecutableConstraint grammar fields left)
        (← compileExecutableConstraint grammar fields right))

/-- Resolve a semantic plan completely. Rust and future executable backends consume this form,
not raw capture names. -/
def compileExecutableSemanticPlan (grammar : FlatGrammar) (plan : SemanticPlan) :
    Except String ExecutableSemanticPlan := do
  let fields ← compileSemanticFields grammar plan
  match plan with
  | .int64 expression wfConstraints valueConstraints =>
      pure (.int64
        (← compileExecutableExpr grammar fields expression)
        (← wfConstraints.mapM (compileExecutableConstraint grammar fields))
        (← valueConstraints.mapM (compileExecutableConstraint grammar fields)))
  | .ip family addressBits radix addressExpr prefixExpr wfConstraints valueConstraints =>
      pure (.ip family addressBits radix
        (← compileExecutableExpr grammar fields addressExpr)
        (← compileExecutableExpr grammar fields prefixExpr)
        (← wfConstraints.mapM (compileExecutableConstraint grammar fields))
        (← valueConstraints.mapM (compileExecutableConstraint grammar fields)))

end Triptych.Backend.Verus
