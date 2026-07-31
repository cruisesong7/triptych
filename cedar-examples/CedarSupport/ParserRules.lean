import CedarSupport.String
import Triptych.Automation.ExternalParser

/-!
# Cedar parser rules

Reusable successful-path summaries for Cedar parser primitives. These theorems are proved
from the executable definitions and Cedar's low-level string facts; they do not depend on any
format-specific parser correctness theorem.
-/

open Cedar.Spec.Ext
open CedarSupport.String
open CedarSupport.StringInternals
open Triptych

namespace CedarSupport.ParserRules

/-- Successful unsigned decimal conversion is exactly nonempty decimal syntax and its value. -/
@[triptych_parser]
theorem toNat?_eq_some_iff {s : String} {n : Nat} :
    toNat?' s = some n ↔ Triptych.IsDigits s ∧ n = readNat s := by
  constructor
  · intro h
    have hsome : (toNat?' s).isSome = true := by simp [h]
    have hcedar := isDigitsOfToNatIsSome hsome
    have hdigits := (digits_iff s).mpr hcedar
    have hvalue := readNat_eq s hcedar
    rw [h] at hvalue
    exact ⟨hdigits, Option.some.inj hvalue⟩
  · rintro ⟨hdigits, rfl⟩
    exact readNat_eq s ((digits_iff s).mp hdigits)

/-- Cedar's signed decimal conversion on an explicit optional sign and digit run. -/
theorem toInt?_of_parts (sign natural : String) (hsign : sign = "-" ∨ sign = "")
    (hnatural : Triptych.IsDigits natural) :
    toInt?' (sign ++ natural) = some (signOf sign * natOf natural) := by
  have hcedar := (digits_iff natural).mp hnatural
  have hnat := readNat_eq natural hcedar
  have hno := noUnderscoreOfIsDigits hcedar
  have hnatStd : natural.toNat? = some (readNat natural) := by
    unfold toNat?' at hnat
    rw [hno] at hnat
    exact hnat
  rcases hsign with rfl | rfl
  · unfold toInt?'
    have hnoSigned : ("-" ++ natural).contains '_' = false := by
      simpa [String.contains, String.toList_append] using hno
    rw [hnoSigned]
    apply String.toInt?_eq_some_iff.mpr
    right
    exact ⟨natural, rfl, readNat natural, hnatStd, by simp [signOf, natOf]⟩
  · simp only [String.empty_append]
    unfold toInt?'
    rw [hno, String.toInt?_eq_some_of_toNat?_eq_some hnatStd]
    simp [signOf, natOf]

/-- Successful signed conversion exposes an optional minus sign, decimal digits, and value. -/
@[triptych_parser]
theorem toInt?_eq_some_iff {s : String} {i : Int} :
    toInt?' s = some i ↔
      ∃ sign natural,
        (sign = "-" ∨ sign = "") ∧ Triptych.IsDigits natural ∧
        s = sign ++ natural ∧ i = signOf sign * natOf natural := by
  constructor
  · intro h
    unfold toInt?' at h
    split at h
    · simp at h
    · rename_i hno
      rw [Bool.not_eq_true] at hno
      rcases String.toInt?_eq_some_iff.mp h with
        ⟨n, hn, rfl⟩ | ⟨natural, rfl, n, hn, rfl⟩
      · have hwrapped : toNat?' s = some n := by
          unfold toNat?'
          rw [hno]
          exact hn
        obtain ⟨hdigits, hnvalue⟩ := toNat?_eq_some_iff.mp hwrapped
        refine ⟨"", s, Or.inr rfl, hdigits, by simp, ?_⟩
        rw [hnvalue]
        simp [signOf, natOf]
      · have hnaturalNoUnderscore : natural.contains '_' = false := by
          simpa [String.contains, String.toList_append] using hno
        have hwrapped : toNat?' natural = some n := by
          unfold toNat?'
          rw [hnaturalNoUnderscore]
          exact hn
        obtain ⟨hdigits, hnvalue⟩ := toNat?_eq_some_iff.mp hwrapped
        refine ⟨"-", natural, Or.inl rfl, hdigits, rfl, ?_⟩
        rw [hnvalue]
        simp [signOf, natOf]
  · rintro ⟨sign, natural, hsign, hdigits, rfl, rfl⟩
    exact toInt?_of_parts sign natural hsign hdigits

end CedarSupport.ParserRules
