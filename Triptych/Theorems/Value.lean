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

import Triptych.Architecture.Denote
import Triptych.Architecture.Value

/-!
# Value-reader correctness

Reusable correctness facts for the readers denoted by Triptych's value DSL.
-/

namespace Triptych

/-- Triptych's decimal reader is a left inverse of the standard decimal rendering. -/
@[simp] theorem readNat_toString (n : Nat) : readNat (toString n) = n := by
  unfold readNat
  rw [String.foldl_eq_foldl_toList, Nat.toString_eq_repr, Nat.toList_repr]
  simpa [Nat.ofDigitChars_eq_foldl, Nat.mul_comm] using
    (Nat.ofDigitChars_ten_toDigits (n := n))

/-- `Nat.repr` spelling of `readNat_toString`, useful after generated definitions unfold. -/
@[simp] theorem readNat_repr (n : Nat) : readNat n.repr = n := by
  simpa [Nat.toString_eq_repr] using readNat_toString n

/-- The standard decimal rendering is a nonempty string accepted by a `digit+` terminal. -/
theorem matchesTerm_digit_toString (n : Nat) :
    matchesTerm .digit .atLeastOne (toString n) := by
  unfold matchesTerm TokClass.all LenSpec.sat
  constructor
  · intro c hc
    simp only [TokClass.mem, Char.le_def, UInt32.le_iff_toNat_le]
    have hd := Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (c := c)
      (by omega) (by omega)
      (by simpa [Nat.toString_eq_repr, Nat.toList_repr] using hc)
    rw [Char.isDigit_iff_toNat] at hd
    exact hd
  · rw [Nat.toString_eq_repr, Nat.repr_eq_ofList_toDigits, String.length_ofList]
    exact Nat.length_toDigits_pos

end Triptych
