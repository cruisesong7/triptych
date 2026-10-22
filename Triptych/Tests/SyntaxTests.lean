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

import Triptych.Elab.Syntax
import Triptych.Automation.ExternalParser

namespace Triptych.Tests

private def acyclicGrammar : Grammar :=
  { start := "A"
    prods :=
      [ ({ name := "A", alts := [[{ sym := .ref "B" }]] } : Production),
        ({ name := "B", alts := [[{ sym := .lit "b" }]] } : Production) ] }

private def indirectRecursiveGrammar : Grammar :=
  { start := "A"
    prods :=
      [ ({ name := "A", alts := [[{ sym := .ref "B" }]] } : Production),
        ({ name := "B", alts := [[{ sym := .ref "C" }]] } : Production),
        ({ name := "C", alts := [[{ sym := .ref "A" }]] } : Production) ] }

private def unreachableRecursiveGrammar : Grammar :=
  { start := "A"
    prods :=
      [ ({ name := "A", alts := [[{ sym := .lit "a" }]] } : Production),
        ({ name := "B", alts := [[{ sym := .ref "C" }]] } : Production),
        ({ name := "C", alts := [[{ sym := .ref "B" }]] } : Production) ] }

private def repeatedRecursiveGrammar : Grammar :=
  { start := "A"
    prods :=
      [ ({ name := "A"
           alts := [[{ sym := .rep "," (.ref "A") 1 (some 3) }]] } : Production) ] }

#guard acyclicGrammar.cycle? = none
#guard acyclicGrammar.isAcyclic
#guard indirectRecursiveGrammar.cycle? = some ["A", "B", "C", "A"]
#guard !indirectRecursiveGrammar.isAcyclic
#guard unreachableRecursiveGrammar.cycle? = some ["B", "C", "B"]
#guard !unreachableRecursiveGrammar.isAcyclic
#guard !unreachableRecursiveGrammar.ok
#guard repeatedRecursiveGrammar.cycle? = some ["A", "A"]
#guard !repeatedRecursiveGrammar.isAcyclic

/--
error: recursive grammar productions are unsupported; cycle: A -> B -> A
-/
#guard_msgs in
triptych RecursiveGrammar where
  grammar
    A ::= B
    B ::= A

/--
error: capture name segment `bit` is a reserved Lean/Triptych keyword; escape it as `«bit»` everywhere it is used. Triptych preserves the semantic capture name and quotes generated Lean identifiers automatically.
-/
#guard_msgs in
triptych ReservedCapture where
  grammar
    bit ::= digit{1}

triptych EscapedCapture where
  grammar
    Root  ::= «bit»
    «bit» ::= digit{1}
  value
    nat «bit»

#guard EscapedCapture.parse "1" = some 1

/--
error: captures `MM` and `mm` both normalize to the public Lean binder `mm` in the `value` function; rename or qualify one capture. Triptych does not silently rename public binders.
-/
#guard_msgs in
triptych BinderCollision where
  grammar
    Root ::= MM mm
    MM   ::= digit{1}
    mm   ::= digit{1}
  value
    nat MM + nat mm


namespace OfSpecParserExample

private def asDomainInt (i : Int) : Int := i
private def fromDomainInt (i : Int) : Int := i

triptych BoundedInteger where
  grammar
    Root   ::= Digits
    Digits ::= digit+
  value
    nat Digits
    ofSpec asDomainInt
  constraints
    nonempty Digits
    value ∈ [0, 100]

#guard BoundedInteger.parse "42" = some 42
#guard BoundedInteger.parse "101" = none

triptych AutoInverseInteger where
  grammar
    Root   ::= Digits
    Digits ::= digit+
  value
    nat Digits
    ofSpec asDomainInt
    toSpec fromDomainInt
  constraints
    value ∈ [0, 100]

example (i : Int) : asDomainInt (fromDomainInt i) = i :=
  AutoInverseInteger.ofSpec_toSpec i

private def shiftedToDomain (i : Int) : Int := i + 1
private def shiftedFromDomain (i : Int) : Int := i - 1

private theorem shiftedToDomain_shiftedFromDomain (i : Int) :
    shiftedToDomain (shiftedFromDomain i) = i := by
  simp [shiftedToDomain, shiftedFromDomain]

triptych ExplicitInverseInteger where
  grammar
    Root   ::= Digits
    Digits ::= digit+
  value
    nat Digits
    ofSpec shiftedToDomain
    toSpec shiftedFromDomain
    ofSpec_toSpec shiftedToDomain_shiftedFromDomain
  constraints
    value ∈ [0, 100]

example (i : Int) : shiftedToDomain (shiftedFromDomain i) = i :=
  ExplicitInverseInteger.ofSpec_toSpec i

private def nonInverseToDomain (i : Int) : Int := i + 1

/--
error: Triptych could not synthesize `ofSpec_toSpec`. Add `ofSpec_toSpec <proof>` after `toSpec`; the proof must establish `∀ d, ofSpec (toSpec d) = d`.
-/
#guard_msgs in
triptych MissingInverseInteger where
  grammar
    Root   ::= Digits
    Digits ::= digit+
  value
    nat Digits
    ofSpec nonInverseToDomain
    toSpec fromDomainInt

end OfSpecParserExample

namespace ValueResultBinderExample

structure Value where
  digits : String
  deriving Repr, DecidableEq

private def toValue (digits : String) : Value := { digits }

triptych ValueResult where
  grammar
    Root   ::= Digits
    Digits ::= digit+
  value'
    toValue Digits

#guard ValueResult.parse "42" = some { digits := "42" }

#guard decide (ValueResult.IsValid "42" ∧
  { digits := "42" } = ValueResult.value (component ValueResult.grammar "42" "Digits"))

end ValueResultBinderExample

namespace EscapedOfSpecExample

structure WrappedNat where
  val : Nat
  deriving Repr, DecidableEq

private def readValue (digits : String) : Nat := readNat digits

private def wrapValue (n : Nat) : WrappedNat := { val := n }

triptych EscapedOfSpec where
  grammar
    Root   ::= Digits
    Digits ::= digit+
  value'
    readValue Digits
    ofSpec wrapValue

#guard EscapedOfSpec.parse "42" = some { val := 42 }

end EscapedOfSpecExample

namespace StringLiteralExample

private def decodeLiteral (literal : String) : String :=
  (decodeStringLiteral literal).getD ""

/-
Corresponding Strata declaration and existing parser test:

  op sc_str (@[unwrap] s:Str) : SpecConstant => s;
  parse_spec_constant "test";
-/
triptych StringValue where
  grammar
    SpecConstant ::= StringLiteral
    StringLiteral ::= str
  value'
    decodeLiteral StringLiteral

#guard StringValue.parse "\"test\"" = some "test"

end StringLiteralExample

namespace AsciiRangeExample

triptych Graph6Character where
  grammar
    Root       ::= Character
    Character  ::= ascii[63,126]{1}

#guard decide (Graph6Character.IsWf "?")
#guard decide (Graph6Character.IsWf "~")
#guard !decide (Graph6Character.IsWf " ")

/--
error: ASCII range upper bound 64 is below lower bound 65
-/
#guard_msgs in
triptych ReversedAsciiRange where
  grammar
    Root ::= ascii[65,64]{1}

/--
error: ASCII range upper bound 128 exceeds 127
-/
#guard_msgs in
triptych NonAsciiRange where
  grammar
    Root ::= ascii[0,128]{1}

end AsciiRangeExample

namespace SizedTerminalExample

private def upperTriangleSize (order : String) : Nat :=
  let vertices := readNat order
  vertices * (vertices - 1) / 2

private def sizedGraphValue (order cells : String) : Nat × String :=
  (readNat order, cells)

triptych SizedGraph where
  grammar
    Graph ::= Order ":" Cells
    Order ::= digit+
    Cells ::= bit{upperTriangleSize Order}
  value'
    sizedGraphValue Order Cells

#guard SizedGraph.parse "3:101" = some (3, "101")
#guard SizedGraph.parse "4:101001" = some (4, "101001")
#guard SizedGraph.parse "1:" = some (1, "")
#guard SizedGraph.parse "3:10" = none
#guard SizedGraph.parse "3:1010" = none
#guard SizedGraph.parse "3:10a" = none
#guard decide (SizedGraph.IsWf "3:101")
#guard !decide (SizedGraph.IsWf "3:10")
#guard (SizedGraph.decodeView "3:101").map (fun view => (view.order, view.cells)) =
  some ("3", "101")

example (cells order : String) :
    SizedGraph.WfConstraints cells order ↔ cells.length = upperTriangleSize order :=
  Iff.rfl

example (s : String) :
    SizedGraph.parse s = none ↔ ¬SizedGraph.IsValid s :=
  SizedGraph.parse_reject s

/--
error: dependent width requires a nonempty literal delimiter before its field
-/
#guard_msgs in
triptych UndelimitedSized where
  grammar
    Root ::= Order Cells
    Order ::= digit+
    Cells ::= bit{upperTriangleSize Order}

private def rowWidth (width : String) : Nat :=
  readNat width

private def sizedRowsValue (width first second : String) : Nat × String × String :=
  (readNat width, first, second)

triptych SizedRows where
  grammar
    Rows   ::= Width ":" First "/" Second
    Width  ::= digit{1,2}
    First  ::= bit{rowWidth Width}
    Second ::= hexDigit{rowWidth Width}
  value'
    sizedRowsValue Width First Second

#guard SizedRows.parse "3:101/a0F" = some (3, "101", "a0F")
#guard SizedRows.parse "0:/" = some (0, "", "")
#guard SizedRows.parse "3:10/a0F" = none
#guard SizedRows.parse "3:101/a0" = none

/--
error: internal dependent-width field `Cells` requires an immediate nonempty literal delimiter after it
-/
#guard_msgs in
triptych UnseparatedInternalSized where
  grammar
    Root ::= Order ":" Cells Tail
    Order ::= digit+
    Cells ::= bit{upperTriangleSize Order}
    Tail ::= digit+

end SizedTerminalExample

namespace CollectionConstraintExample

private def taggedSumIsSix (tag : String) (items : List String) : Bool :=
  tag == "n=" && items.foldl (fun total item => total + readNat item) 0 == 6

triptych RepeatedSum where
  grammar
    Root ::= Tag rep Item sepBy ","+
    Tag  ::= "n="
    Item ::= digit+
  value
    count Item
  constraints'
    taggedSumIsSix Tag [Item]

#guard RepeatedSum.parse "n=1,2,3" = some 3
#guard RepeatedSum.parse "n=1,2,4" = none
#guard (RepeatedSum.decodeView "n=1,2,3").map (·.itemAll) = some ["1", "2", "3"]

/--
error: list argument `[Tag]` does not name a repeated item. Declare `rep Tag sepBy "..." <len>` before reading all of its spans.
-/
#guard_msgs in
triptych InvalidListConstraint where
  grammar
    Root ::= Tag
    Tag  ::= "tag"
  constraints'
    taggedSumIsSix Tag [Tag]

end CollectionConstraintExample

namespace ScannerBudgetExample

private def budgetGrammar : Grammar where
  start := "Root"
  prods := [{ name := "Root", alts := [[{ sym := .term .digit .atLeastOne }]] }]

#guard decide (decodeBudget budgetGrammar "1234" =
  { referenceDepth := 1, repetitionDepth := 4, terminalPrefixCandidates := 5 })

example (s : String) :
    (decodeBudget budgetGrammar s).terminalPrefixCandidates = s.length + 1 := by
  simp

example (s : String) :
    scannerCandidateChecks budgetGrammar s ≤ scannerCandidateBudget budgetGrammar s :=
  scannerCandidateChecks_le budgetGrammar s

#guard scannerCandidateChecks budgetGrammar "1234" = 0

end ScannerBudgetExample

namespace DefaultPrinterExample

private def payloadValue (digits : String) : Bool :=
  digits == "1"

triptych BitFormat where
  grammar
    EncodedBool ::= Payload
    Payload     ::= digit{1}
  value' payloadValue Payload

def BitFormat.toDerivation : Bool → BitFormat.Derivation.EncodedBool
  | false => .alt0 (.alt0 "0")
  | true => .alt0 (.alt0 "1")

def BitFormat.printer :
    DerivationPrinter BitFormat.Derivation.EncodedBool.render
      BitFormat.Derivation.EncodedBool.Valid BitFormat.Derivation.EncodedBool.toView
      BitFormat.View.Valid BitFormat.View.denotation where
  toDerivation := BitFormat.toDerivation
  structural b := by cases b <;> decide
  valid b := by cases b <;> trivial
  rightInverse b := by cases b <;> rfl

def BitFormat.toString : Bool → String := BitFormat.printer.toString

#guard BitFormat.toString false = "0"
#guard BitFormat.toString true = "1"

theorem BitFormat.encodeDerivation :
    EncodeDerivationStmt BitFormat.Derivation.EncodedBool.render
      BitFormat.Derivation.EncodedBool.Valid BitFormat.Derivation.EncodedBool.toView
      BitFormat.View.Valid BitFormat.View.denotation BitFormat.toString :=
  BitFormat.printer.encodeDerivation

theorem BitFormat.encodeView :
    EncodeViewStmt BitFormat.decodeView BitFormat.View.Valid BitFormat.View.denotation
      BitFormat.toString :=
  BitFormat.printer.encodeView BitFormat.Derivation.EncodedBool.decodeView_render

theorem BitFormat.parse_toString_roundtrip (b : Bool) :
    BitFormat.parse (BitFormat.toString b) = some b :=
  parse_toString_roundtrip_of_encodeView
    BitFormat.parse_eq_some_iff_view BitFormat.encodeView b

#guard BitFormat.parse (BitFormat.toString false) = some false
#guard BitFormat.parse (BitFormat.toString true) = some true

end DefaultPrinterExample


namespace NestedSearchScalingExample

/-! Regression for search-path emission at realistic size. This is the LRAT text grammar used by
    `Std.Tactic.BVDecide.LRAT.Parser`: nested captures, repetitions, and several optionals in one
    production. Inlining continuations as syntax once produced a 209 MB `directDecode`, and the
    readable-spec equivalence proof failed on a literal following an optional item. -/

private def lineCount (ids : List String) : Nat := ids.length

triptych LratText where
  grammar
    Proof    ::= rep Line sepBy "\n" + "\n"
    Line     ::= Id " " Body Cr
    Cr       ::= ["\r"]
    Body     ::= Delete | Add
    Delete   ::= "d " [DelIds] "0"
    DelIds   ::= rep DelId sepBy " " + " "
    DelId    ::= Pos
    Add      ::= [Lits] "0 " [Hints] [Rats] "0"
    Lits     ::= rep Lit sepBy " " + " "
    Lit      ::= Neg | Pos
    Hints    ::= rep Hint sepBy " " + " "
    Hint     ::= Pos
    Rats     ::= rep Rat sepBy " " + " "
    Rat      ::= Neg " " [Hints]
    Neg      ::= "-" Pos
    Pos      ::= digit+
    Id       ::= Pos
  value'
    lineCount [Id]

#guard LratText.parse "5 1 -2 0 3 4 0\n6 d 1 2 0\n" = some 2
#guard LratText.parse "7 0 5 6 0\n" = some 1
#guard LratText.parse "7 0 5 6 0" = none

end NestedSearchScalingExample


namespace GroupedValueExample

/-! Grouped `value'` arguments: one tuple per occurrence of a repeated production, with nested
    groups read inside each occurrence. -/

private def rowShape (rows : List (String × List String)) : List (String × Nat) :=
  rows.map fun (label, cells) => (label, cells.length)

triptych Rows where
  grammar
    Table ::= rep Row sepBy ";" +
    Row   ::= Label ":" Cells
    Label ::= ascii[97,122]+
    Cells ::= rep Cell sepBy "," +
    Cell  ::= digit+
  value'
    rowShape [Row ⟨Label, [Cell]⟩]

#guard Rows.parse "a:1,2;bc:3" = some [("a", 2), ("bc", 1)]
#guard Rows.parse "a:1,2,3" = some [("a", 3)]
#guard Rows.parse "a:" = none

/--
error: group field `Table` is not a production inside `Row`; a group reads only captures recorded within each `Row` occurrence
-/
#guard_msgs in
triptych RowsBadField where
  grammar
    Table ::= rep Row sepBy ";" +
    Row   ::= Cell
    Cell  ::= digit+
  value'
    List.length [Row ⟨Table⟩]

end GroupedValueExample


end Triptych.Tests
