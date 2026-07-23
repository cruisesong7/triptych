import Triptych.Architecture.Denote
import Triptych.Architecture.Value
import Triptych.Theorems.Cedar.StringInternals

/-! Shared bridges between Triptych's digit reader and Cedar's string metatheory. -/

namespace Triptych.Theorems.Cedar.String

open Cedar.Spec.Ext
open Triptych.Theorems.Cedar.StringInternals

theorem digits_iff (s : String) : Triptych.IsDigits s ↔ _root_.IsDigits s := by
  unfold Triptych.IsDigits Triptych.TokClass.all Triptych.TokClass.mem _root_.IsDigits
  constructor
  · rintro ⟨hdigits, hlen⟩
    refine ⟨by omega, ?_⟩
    intro c hc
    rw [Char.isDigit_iff_toNat]
    have h := hdigits c hc
    change 48 ≤ c.toNat ∧ c.toNat ≤ 57 at h
    exact h
  · rintro ⟨hlen, hdigits⟩
    refine ⟨?_, by omega⟩
    intro c hc
    have h := hdigits c hc
    rw [Char.isDigit_iff_toNat] at h
    change 48 ≤ c.toNat ∧ c.toNat ≤ 57
    exact h

theorem readNat_eq (s : String) (h : _root_.IsDigits s) :
    toNat?' s = some (Triptych.readNat s) := by
  unfold toNat?'
  rw [noUnderscoreOfIsDigits h]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [String.toNat?_eq_some_ofDigitChars (isNatOfIsDigits h)]
  have hf : List.filter (fun x => x != '_') s.toList = s.toList := by
    apply List.filter_eq_self.mpr
    intro c hc
    have hd := h.2 c hc
    have hne : c ≠ '_' := by
      intro heq
      subst c
      simp at hd
    simp [hne]
  rw [hf]
  apply congrArg some
  unfold Triptych.readNat
  rw [String.foldl_eq_foldl_toList]
  simpa only [show Char.toNat '0' = 48 from rfl] using
    (foldlEqOfDigitChars s.toList 0).symm

end Triptych.Theorems.Cedar.String
