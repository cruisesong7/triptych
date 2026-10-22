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

/-!
# Documentation examples

Examples quoted by the documentation site. They live in a small module of their own because the
documentation build highlights the source of every module it quotes.
-/

namespace Triptych.Tests

namespace AutoPrinterExample

-- ANCHOR: printerAutoUse
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
#guard decide (SignedInteger.Production "-42")
-- ANCHOR_END: printerAutoUse

example (s : String) :
    SignedInteger.IsWf.Root s ↔ SignedInteger.Production s :=
  Iff.rfl

#guard decide (SignedInteger.IsValid "-42" ∧
  -42 = SignedInteger.value (component SignedInteger.grammar "-42" "Sign")
    (component SignedInteger.grammar "-42" "Digits"))
#guard !decide (SignedInteger.IsValid "--42" ∧
  -42 = SignedInteger.value (component SignedInteger.grammar "--42" "Sign")
    (component SignedInteger.grammar "--42" "Digits"))

example (s : String) :
    SignedInteger.parse s =
      Triptych.gatedParse SignedInteger.IsValid SignedInteger.computeValue s := by
  exact SignedInteger.parse_eq_gated s

example (s : String) :
    SignedInteger.parse s =
      Triptych.scannerParse SignedInteger.grammar SignedInteger.constraints
        SignedInteger.valueExpr id s := by
  exact SignedInteger.parse_eq_scanner s

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

end Triptych.Tests
