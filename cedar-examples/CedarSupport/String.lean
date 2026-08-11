import Triptych.Architecture.Denote
import Triptych.Architecture.Value
import CedarSupport.StringInternals

/-! Shared bridges between Triptych's digit reader and Cedar's string metatheory. -/

namespace CedarSupport.String

open Cedar.Spec.Ext
open CedarSupport.StringInternals

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

theorem readNat_toString (n : Nat) : Triptych.readNat (toString n) = n := by
  unfold Triptych.readNat
  rw [String.foldl_eq_foldl_toList, Nat.toString_eq_repr,
    Nat.repr_eq_ofList_toDigits, String.toList_ofList]
  change List.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0
    (Nat.toDigits 10 n) = n
  rw [foldlEqOfDigitChars, Nat.ofDigitChars_ten_toDigits]

theorem digits_toString (n : Nat) : _root_.IsDigits (toString n) := by
  rw [Nat.toString_eq_repr, Nat.repr_eq_ofList_toDigits]
  constructor
  · simpa [String.length_ofList] using Nat.length_toDigits_pos (b := 10) (n := n)
  · intro c hc
    rw [String.toList_ofList] at hc
    exact Nat.isDigit_of_mem_toDigits (by omega) (by omega) hc

theorem canonical_toString (n : Nat) :
    (toString n).startsWith "0" → toString n = "0" := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hstarts
    rw [String.startsWith_string_iff] at hstarts
    by_cases hlt : n < 10
    · rw [Nat.toString_eq_repr, Nat.repr_of_lt hlt] at hstarts ⊢
      simp at hstarts
      subst n
      rfl
    · have hge : 10 ≤ n := by omega
      have hq : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
      have hqstarts : (toString (n / 10)).startsWith "0" := by
        have hrepr :
            (toString n).toList =
              (toString (n / 10)).toList ++
                (String.singleton (Nat.digitChar (n % 10))).toList := by
          rw [Nat.toString_eq_repr, Nat.repr_of_ge hge, String.toList_append]
          simp [Nat.toString_eq_repr]
        rw [hrepr] at hstarts
        cases hlist : (toString (n / 10)).toList with
        | nil =>
          have hne : toString (n / 10) ≠ "" := by
            simpa [Nat.toString_eq_repr] using Nat.repr_ne_empty (n := n / 10)
          exfalso
          apply hne
          exact String.toList_inj.mp (by simpa using hlist)
        | cons c cs =>
          rw [hlist] at hstarts
          simp only [List.cons_append, List.cons_prefix_cons] at hstarts
          rw [String.startsWith_string_iff, hlist]
          simpa using hstarts
      have hqzero : toString (n / 10) = "0" := ih (n / 10) hq hqstarts
      have : n / 10 = 0 := by
        have heq := congrArg Triptych.readNat hqzero
        rw [readNat_toString] at heq
        simpa [Triptych.readNat, String.foldl_eq_foldl_toList] using heq
      omega

end CedarSupport.String
