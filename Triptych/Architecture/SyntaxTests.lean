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

import Triptych.Architecture.Syntax
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

namespace AutoPrinterExample

triptych SignedInteger where
  grammar
    Root   ::= Sign Digits
    Sign   ::= sign
    Digits ::= digit+
  value
    Sign * nat Digits
  printer auto

#guard SignedInteger.toString 0 = "0"
#guard SignedInteger.toString 42 = "42"
#guard SignedInteger.toString (-42) = "-42"
#guard SignedInteger.parse (SignedInteger.toString (-42)) = some (-42)

example (s : String) :
    SignedInteger.parse s =
      Triptych.gatedParse SignedInteger.IsValid SignedInteger.computeValue s := by
  rfl

/--
error: Unknown identifier `SignedInteger.isValid`
-/
#guard_msgs in
#check SignedInteger.isValid

example (i : Int) :
    SignedInteger.parse (SignedInteger.toString i) = some i :=
  SignedInteger.parse_toString_roundtrip i

triptych CommutedSignedInteger where
  grammar
    Root   ::= Sign Digits
    Sign   ::= sign
    Digits ::= digit+
  value
    nat Digits * Sign
  printer auto

#guard CommutedSignedInteger.toString (-42) = "-42"
#guard CommutedSignedInteger.parse (CommutedSignedInteger.toString 42) = some 42

private def opaqueValue (digits : String) : Nat :=
  readNat digits

/--
error: `printer auto` requires an analyzable `value` section; an opaque `value'` function needs an explicit `printer` or `DerivationPrinter` certificate
-/
#guard_msgs in
triptych OpaqueAutoPrinter where
  grammar
    Root ::= Digits
    Digits ::= digit+
  value' opaqueValue Digits
  printer auto

/--
error: `printer auto` does not yet synthesize a total printer for constrained value domains; use an explicit `printer`
-/
#guard_msgs in
triptych ConstrainedAutoPrinter where
  grammar
    Root   ::= Sign Digits
    Sign   ::= sign
    Digits ::= digit+
  value
    Sign * nat Digits
  constraints
    value ∈ [0, 10]
  printer auto

end AutoPrinterExample

namespace OfSpecParserExample

private def asDomainInt (i : Int) : Int := i

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

end OfSpecParserExample

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

namespace DecodeBudgetExample

private def budgetGrammar : Grammar where
  start := "Root"
  prods := [{ name := "Root", alts := [[{ sym := .term .digit .atLeastOne }]] }]

#guard decide (decodeBudget budgetGrammar "1234" =
  { referenceDepth := 1, repetitionDepth := 4, terminalPrefixCandidates := 5 })

example (s : String) :
    (decodeBudget budgetGrammar s).terminalPrefixCandidates = s.length + 1 := by
  simp

end DecodeBudgetExample

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

end Triptych.Tests
