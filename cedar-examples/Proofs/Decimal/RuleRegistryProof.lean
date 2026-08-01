import Generated.Decimal.parser
import CedarSupport.ParserRules
import Triptych.Automation.ExternalParser

/-!
# Decimal external-parser proof via the Triptych rule registry

This module starts from Cedar's executable Decimal parser and Triptych's generated grammar.
It intentionally does not import `Cedar.Thm.Ext.Decimal` or `Decimal.CedarBridge`.
-/

open Cedar.Spec.Ext
open CedarSupport.ParserRules
open Triptych

set_option linter.unusedSimpArgs false

namespace Decimal.RuleRegistryProof

private theorem noDotOfDigits {s : String} (h : Triptych.IsDigits s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = '.')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq
  subst c
  have := h.1 '.' hc
  simp [TokClass.mem] at this

private theorem noDotOfSignedDigits {sgn natural : String}
    (hsign : sgn = "-" ∨ sgn = "") (hnatural : Triptych.IsDigits natural) :
    ∀ c ∈ (sgn ++ natural).toList, (fun x : Char => decide (x = '.')) c = false := by
  intro c hc
  rw [String.toList_append] at hc
  rcases List.mem_append.mp hc with hsignChar | hnaturalChar
  · rcases hsign with rfl | rfl <;> simp at hsignChar
    subst c
    decide
  · exact noDotOfDigits hnatural c hnaturalChar

private theorem naturalDoesNotStartWithMinus {natural : String} (h : Triptych.IsDigits natural) :
    natural.startsWith "-" = false := by
  apply String.startsWith_string_eq_false_iff.mpr
  intro hp
  have hm : '-' ∈ natural.toList := List.IsPrefix.subset hp (by simp)
  have := h.1 '-' hm
  simp [TokClass.mem] at this

/-- Cedar's arithmetic after splitting agrees with the generated Decimal denotation. -/
private theorem parserValue_eq_denotation (sgn natural fraction : String)
    (hsign : sgn = "-" ∨ sgn = "") (hnatural : Triptych.IsDigits natural)
    (hfraction : Triptych.IsDigitsBetween 1 4 fraction) :
    (if !(sgn ++ natural).startsWith "-" then
        (signOf sgn * natOf natural) * Int.pow 10 4 +
          (readNat fraction : Int) * Int.pow 10 (4 - fraction.length)
      else
        (signOf sgn * natOf natural) * Int.pow 10 4 -
          (readNat fraction : Int) * Int.pow 10 (4 - fraction.length)) =
      Decimal.value sgn natural fraction := by
  have hlen : fraction.length ≤ 4 := hfraction.2.2
  have hexp : ((4 : Int) - (fraction.length : Int)).toNat = 4 - fraction.length := by
    omega
  unfold Decimal.value natOf lenOf
  rw [hexp]
  rw [show Int.pow 10 4 = (10000 : Int) from by rfl]
  rcases hsign with rfl | rfl
  · rw [show (10 : Int) ^ (4 - fraction.length) =
      Int.pow 10 (4 - fraction.length) from rfl]
    simp [signOf, Int.sub_eq_add_neg, Int.neg_add, Int.neg_mul]
  · simp only [String.empty_append, signOf]
    rw [naturalDoesNotStartWithMinus hnatural]
    simp
    rw [show (10 : Int) ^ (4 - fraction.length) =
      Int.pow 10 (4 - fraction.length) from rfl]

/-- On grammar-shaped components, Cedar's executable parser computes the generated value. -/
theorem parse_of_parts (s sgn natural fraction : String)
    (hs : s = sgn ++ natural ++ "." ++ fraction)
    (hsign : sgn = "-" ∨ sgn = "")
    (hnatural : Triptych.IsDigits natural)
    (hfraction : Triptych.IsDigitsBetween 1 4 fraction) :
    Cedar.Spec.Ext.Decimal.parse s =
      Int64.ofInt? (Decimal.value sgn natural fraction) := by
  have hfractionDigits : Triptych.IsDigits fraction :=
    ⟨hfraction.1, hfraction.2.1⟩
  have hsplit :
      s.splitToList (· = '.') = [sgn ++ natural, fraction] := by
    rw [hs]
    simpa [String.append_assoc] using
      (Triptych.splitToList_two (sgn ++ natural) fraction
        (fun x : Char => decide (x = '.')) '.' (by simp)
        (noDotOfSignedDigits hsign hnatural) (noDotOfDigits hfractionDigits))
  unfold Cedar.Spec.Ext.Decimal.parse
  rw [hsplit]
  have hlen : 0 < fraction.length ∧ fraction.length ≤ DECIMAL_DIGITS := by
    simpa using ⟨hfraction.2.1, hfraction.2.2⟩
  have hnotBare : sgn ++ natural ≠ "-" := by
    rcases hsign with rfl | rfl
    · intro heq
      have hempty : natural = "" := by simpa using heq
      subst natural
      simpa using hnatural.2
    · intro heq
      have hdash : natural = "-" := by simpa using heq
      subst natural
      have := hnatural.1 '-' (by simp)
      simp [TokClass.mem] at this
  simp only [hnotBare, ↓reduceIte]
  rw [if_pos hlen]
  rw [toInt?_of_parts sgn natural hsign hnatural]
  rw [(toNat?_eq_some_iff).mpr ⟨hfractionDigits, rfl⟩]
  simp only
  rw [parserValue_eq_denotation sgn natural fraction hsign hnatural hfraction]
  rfl

/-- A successful Cedar parse exposes grammar-shaped Decimal components. -/
@[triptych_parser, triptych_parser_search =]
theorem parse_eq_some_iff_parts {s : String} {d : Cedar.Spec.Ext.Decimal} :
    Cedar.Spec.Ext.Decimal.parse s = some d ↔
      ∃ sgn natural fraction,
        (sgn = "-" ∨ sgn = "") ∧
        s = sgn ++ natural ++ "." ++ fraction ∧
        Triptych.IsDigits natural ∧ Triptych.IsDigitsBetween 1 4 fraction ∧
        Int64.ofInt? (Decimal.value sgn natural fraction) = some d := by
  constructor
  · intro hparse
    unfold Cedar.Spec.Ext.Decimal.parse at hparse
    generalize hsplits : s.splitToList (· = '.') = parts at hparse
    rcases parts with _ | ⟨left, rest⟩
    · simp at hparse
    rcases rest with _ | ⟨right, rest⟩
    · simp at hparse
    rcases rest with _ | ⟨extra, rest⟩
    · by_cases hbare : left = "-"
      · subst left
        simp at hparse
      · by_cases hlen :
          0 < right.length ∧ right.length ≤ DECIMAL_DIGITS
        · simp only [hbare, hlen, ↓reduceIte] at hparse
          cases hleft : toInt?' left with
          | none => simp [hleft] at hparse
          | some l =>
            cases hr : toNat?' right with
            | none => simp [hleft, hr] at hparse
            | some r =>
              simp only [hleft, hr] at hparse
              triptych_sound [Cedar.Spec.Ext.Decimal.decimal?] at hparse
              obtain ⟨sgn, natural, hsign, hnatural, hleftParts, hl⟩ :=
                toInt?_eq_some_iff.mp hleft
              have hrightDigits : Triptych.IsDigits right :=
                (toNat?_eq_some_iff.mp hr).1
              have hrightValue : r = readNat right :=
                (toNat?_eq_some_iff.mp hr).2
              have hfraction : Triptych.IsDigitsBetween 1 4 right := by
                refine ⟨hrightDigits.1, ?_, ?_⟩
                · exact hrightDigits.2
                · simpa [DECIMAL_DIGITS] using hlen.2
              have hs := Triptych.eq_intercalate_of_splitToList_eq '.' hsplits
              rw [String.intercalate_cons_cons, String.intercalate_singleton] at hs
              have hsrender : s = sgn ++ natural ++ "." ++ right := by
                simpa [hleftParts, String.append_assoc] using hs
              refine ⟨sgn, natural, right, hsign, hsrender, hnatural, hfraction, ?_⟩
              rw [← hparse]
              congr 1
              rw [hleftParts, hl, hrightValue]
              simpa using
                (parserValue_eq_denotation sgn natural right hsign hnatural hfraction).symm
        · simp [hbare, hlen] at hparse
    · simp at hparse
  · rintro ⟨sgn, natural, fraction, hsign, hs, hnatural, hfraction, hresult⟩
    rw [parse_of_parts s sgn natural fraction hs hsign hnatural hfraction]
    exact hresult

theorem sign_mem (fuel : Nat) (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym Decimal.grammar "" (fuel + 1) (Sym.ref "Sign") cs ↔
      (m = [("Sign", "-")] ∧ cs = '-' :: r) ∨
      (m = [("Sign", "")] ∧ cs = r) := by
  simp [matchSym, Decimal.grammar, Grammar.prod?, matchProd, matchSeq]
  constructor
  · rintro (⟨a, ⟨hp, rfl, rfl⟩, rfl⟩ | ⟨rfl, rfl⟩)
    · left
      cases cs with
      | nil => simp at hp
      | cons c cs =>
        simp at hp
        subst c
        simp
    · exact Or.inr ⟨rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl (by simp)
    · exact Or.inr ⟨rfl, rfl⟩

theorem sign_parts_mem (fuel : Nat) (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym Decimal.grammar "" (fuel + 1) (Sym.ref "Sign") cs ↔
      ∃ sgn, (sgn = "-" ∨ sgn = "") ∧
        m = [("Sign", sgn)] ∧ cs = sgn.toList ++ r := by
  constructor
  · intro h
    rcases (sign_mem fuel cs r m).mp h with hminus | hempty
    · exact ⟨"-", Or.inl rfl, hminus.1, by simpa using hminus.2⟩
    · exact ⟨"", Or.inr rfl, hempty.1, by simpa using hempty.2⟩
  · rintro ⟨sgn, hsign, hm, hcs⟩
    rcases hsign with rfl | rfl
    · exact (sign_mem fuel cs r m).mpr (Or.inl ⟨hm, by simpa using hcs⟩)
    · exact (sign_mem fuel cs r m).mpr (Or.inr ⟨hm, by simpa using hcs⟩)

theorem natural_mem (fuel : Nat) (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym Decimal.grammar "" (fuel + 1) (Sym.ref "Natural") cs ↔
      ∃ p, m = [("Natural", String.ofList p)] ∧ cs = p ++ r ∧
        matchesTerm TokClass.digit LenSpec.atLeastOne (String.ofList p) := by
  exact mem_matchSym_ref_single_term_iff Decimal.grammar fuel "Natural" "Natural"
    TokClass.digit LenSpec.atLeastOne rfl cs r m

theorem fraction_mem (fuel : Nat) (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym Decimal.grammar "" (fuel + 1) (Sym.ref "Fraction") cs ↔
      ∃ p, m = [("Fraction", String.ofList p)] ∧ cs = p ++ r ∧
        matchesTerm TokClass.digit (LenSpec.between 1 4) (String.ofList p) := by
  exact mem_matchSym_ref_single_term_iff Decimal.grammar fuel "Fraction" "Fraction"
    TokClass.digit (LenSpec.between 1 4) rfl cs r m

theorem decimal_match_mem (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈
        matchProd Decimal.grammar "" 4
          (Production.mk "Decimal"
            [[SymItem.mk (Sym.ref "Sign") false,
              SymItem.mk (Sym.ref "Natural") false,
              SymItem.mk (Sym.lit ".") false,
              SymItem.mk (Sym.ref "Fraction") false]]) cs ↔
      ∃ sgn natural fraction,
        (sgn = "-" ∨ sgn = "") ∧
        m = [("Sign", sgn), ("Natural", natural), ("Fraction", fraction)] ∧
        cs = sgn.toList ++ natural.toList ++ '.' :: fraction.toList ++ r ∧
        Triptych.IsDigits natural ∧ Triptych.IsDigitsBetween 1 4 fraction := by
  rw [matchProd]
  simp only [List.mem_flatMap, List.mem_singleton, exists_eq_left]
  constructor
  · intro hmem
    obtain ⟨mS, restS, mRest, hS, hRest, rfl⟩ :=
      (mem_matchSeq_cons_required_iff Decimal.grammar "" 4 _ _ rfl cs r m).mp hmem
    obtain ⟨mI, restI, mRestI, hI, hRestI, rfl⟩ :=
      (mem_matchSeq_cons_required_iff Decimal.grammar "" 4 _ _ rfl restS r mRest).mp hRest
    obtain ⟨mDot, restDot, mRestDot, hDot, hRestDot, rfl⟩ :=
      (mem_matchSeq_cons_required_iff Decimal.grammar "" 4 _ _ rfl restI r mRestI).mp
        hRestI
    obtain ⟨mF, restF, mNil, hF, hNil, rfl⟩ :=
      (mem_matchSeq_cons_required_iff Decimal.grammar "" 4 _ _ rfl restDot r mRestDot).mp
        hRestDot
    simp only [matchSeq, List.mem_singleton, Prod.mk.injEq] at hNil
    obtain ⟨rfl, rfl⟩ := hNil
    obtain ⟨sgn, hsign, rfl, hsigncs⟩ := (sign_parts_mem 3 cs restS mS).mp hS
    obtain ⟨natural, rfl, hnatural, hnaturalDigits⟩ := (natural_mem 3 _ _ _).mp hI
    obtain ⟨rfl, rfl⟩ := (mem_matchSym_lit_iff Decimal.grammar "" 4 "." _ _ _).mp hDot
    obtain ⟨fraction, rfl, hfraction, hfractionDigits⟩ := (fraction_mem 3 _ _ _).mp hF
    refine ⟨sgn, String.ofList natural, String.ofList fraction, hsign, ?_, ?_, ?_, ?_⟩
    · simp
    · simp [hsigncs, hnatural, hfraction, List.append_assoc]
    · simpa [IsDigits_matchesTerm] using hnaturalDigits
    · simpa [IsDigitsBetween_matchesTerm] using hfractionDigits
  · rintro ⟨sgn, natural, fraction, hsign, rfl, hcs, hnatural, hfraction⟩
    rw [mem_matchSeq_cons_required_iff Decimal.grammar "" 4 _ _ rfl]
    refine ⟨[("Sign", sgn)], natural.toList ++ '.' :: fraction.toList ++ r,
      [("Natural", natural), ("Fraction", fraction)], ?_, ?_, by simp⟩
    · exact (sign_parts_mem 3 _ _ _).mpr
        ⟨sgn, hsign, rfl, by simpa [List.append_assoc] using hcs⟩
    · rw [mem_matchSeq_cons_required_iff Decimal.grammar "" 4 _ _ rfl]
      refine ⟨[("Natural", natural)], '.' :: fraction.toList ++ r,
        [("Fraction", fraction)], ?_, ?_, by simp⟩
      · exact (natural_mem 3 _ _ _).mpr
          ⟨natural.toList, by simp, by simp [List.append_assoc],
            by rw [IsDigits_matchesTerm, String.ofList_toList]; exact hnatural⟩
      · rw [mem_matchSeq_cons_required_iff Decimal.grammar "" 4 _ _ rfl]
        refine ⟨[], fraction.toList ++ r, [("Fraction", fraction)], ?_, ?_, by simp⟩
        · exact (mem_matchSym_lit_iff Decimal.grammar "" 4 "." _ _ _).mpr ⟨rfl, rfl⟩
        · rw [mem_matchSeq_cons_required_iff Decimal.grammar "" 4 _ _ rfl]
          refine ⟨[("Fraction", fraction)], r, [], ?_, ?_, by simp⟩
          · exact (fraction_mem 3 _ _ _).mpr
              ⟨fraction.toList, by simp, rfl,
                by rw [IsDigitsBetween_matchesTerm, String.ofList_toList]; exact hfraction⟩
          · simp [matchSeq]

/-- Every successful generated decode exposes the exact Decimal component captures. -/
theorem decode_sound {s : String} {m : CaptureMap}
    (h : decode Decimal.grammar s = some m) :
    ∃ sgn natural fraction,
      (sgn = "-" ∨ sgn = "") ∧
      m = [("Sign", sgn), ("Natural", natural), ("Fraction", fraction)] ∧
      s = sgn ++ natural ++ "." ++ fraction ∧
      Triptych.IsDigits natural ∧ Triptych.IsDigitsBetween 1 4 fraction := by
  obtain ⟨p, hstart, hmem⟩ := mem_matchProd_of_decode_eq_some h
  have hp :
      p =
        Production.mk "Decimal"
          [[SymItem.mk (Sym.ref "Sign") false,
            SymItem.mk (Sym.ref "Natural") false,
            SymItem.mk (Sym.lit ".") false,
            SymItem.mk (Sym.ref "Fraction") false]] := by
    have hknown :
        Decimal.grammar.startProd? =
          some
            (Production.mk "Decimal"
              [[SymItem.mk (Sym.ref "Sign") false,
                SymItem.mk (Sym.ref "Natural") false,
                SymItem.mk (Sym.lit ".") false,
                SymItem.mk (Sym.ref "Fraction") false]]) := rfl
    rw [hknown] at hstart
    exact (Option.some.inj hstart).symm
  subst p
  have hxmem :
      (m, ([] : List Char)) ∈
        matchProd Decimal.grammar "" 4
          (Production.mk "Decimal"
            [[SymItem.mk (Sym.ref "Sign") false,
              SymItem.mk (Sym.ref "Natural") false,
              SymItem.mk (Sym.lit ".") false,
              SymItem.mk (Sym.ref "Fraction") false]])
          s.toList := by
    simpa [Decimal.grammar] using hmem
  obtain ⟨sgn, natural, fraction, hsign, hm, hs, hnatural, hfraction⟩ :=
    (decimal_match_mem s.toList [] m).mp hxmem
  refine ⟨sgn, natural, fraction, hsign, hm, ?_, hnatural, hfraction⟩
  rw [← String.toList_inj]
  simpa [String.toList_append, List.append_assoc] using hs

/-- Surface grammar well-formedness determines the generated decoder's component view. -/
theorem decode_parts_of_isWf {s : String} (h : Decimal.IsWf.Decimal s) :
    ∃ sgn natural fraction,
      decode Decimal.grammar s =
        some [("Sign", sgn), ("Natural", natural), ("Fraction", fraction)] ∧
      (sgn = "-" ∨ sgn = "") ∧
      s = sgn ++ natural ++ "." ++ fraction ∧
      Triptych.IsDigits natural ∧ Triptych.IsDigitsBetween 1 4 fraction := by
  have hwf : Triptych.IsWf Decimal.grammar s := (Decimal.IsWfGrammar_equiv s).mpr h
  have hsome : (decode Decimal.grammar s).isSome = true :=
    (decodeSome_iff_IsWf Decimal.grammar (by decide) s).mpr hwf
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨sgn, natural, fraction, hsign, rfl, hs, hnatural, hfraction⟩ :=
    decode_sound hm
  exact ⟨sgn, natural, fraction, hm, hsign, hs, hnatural, hfraction⟩

end Decimal.RuleRegistryProof
