import Triptych.Examples.Decimal.parser
import Triptych.Theorems.Cedar.String
import Triptych.Theorems.Decimal.CedarInternals
import Triptych.Theorems.DecodeLemmas
import Cedar.Thm.Ext.Decimal
import Init.Data.List.SplitOn.Lemmas

/-! Bridges the generated Decimal specification to Cedar's Decimal metatheory. -/

open Cedar.Spec.Ext hiding Decimal
open Triptych.Theorems.Cedar.String
open Triptych.Theorems.Decimal.CedarInternals

namespace Decimal.CedarBridge

theorem join_split {s left right : String}
    (h : s.splitToList (· = '.') = [left, right]) :
    s = left ++ "." ++ right := by
  rw [String.splitToList_of_valid] at h
  have hp : (fun x : Char => decide (x = '.')) = (fun x => x == '.') := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, beq_iff_eq]
  have hsplits : List.splitOn '.' s.toList = [left.toList, right.toList] := by
    rw [List.splitOn_eq_splitOnP]
    have h' := congrArg (List.map String.toList) h
    simpa [Function.comp_def, hp] using h'
  have hi := congrArg (List.intercalate ['.']) hsplits
  rw [List.intercalate_splitOn] at hi
  rw [← String.toList_inj]
  simpa [List.intercalate] using hi

theorem toInt_parts_eq (sgn integer : String) (hsgn : sgn = "-" ∨ sgn = "")
    (hi : _root_.IsDigits integer) :
    toInt?' (sgn ++ integer) =
      some (Triptych.signOf sgn * Triptych.natOf integer) := by
  have hnat' := readNat_eq integer hi
  have hno := noUnderscore_of_isDigits hi
  unfold toNat?' at hnat'
  rw [hno] at hnat'
  rcases hsgn with rfl | rfl
  · unfold toInt?'
    have hnoSigned : ("-" ++ integer).contains '_' = false := by
      have hnot : ¬('_' ∈ ("-" ++ integer).toList) := by
        rw [String.toList_append]
        intro hm
        cases List.mem_append.mp hm with
        | inl hm => simp at hm
        | inr hm =>
            have := hi.2 '_' hm
            simp at this
      simpa [String.contains] using hnot
    rw [hnoSigned]
    apply String.toInt?_eq_some_iff.mpr
    right
    exact ⟨integer, rfl, Triptych.readNat integer, hnat', by
      simp [Triptych.signOf, Triptych.natOf]⟩
  · simp only [String.empty_append]
    unfold toInt?'
    rw [hno]
    rw [String.toInt?_eq_some_of_toNat?_eq_some hnat']
    simp [Triptych.signOf, Triptych.natOf]

open Triptych

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
  · rintro ⟨sgn, hsgn, hm, hcs⟩
    rcases hsgn with rfl | rfl
    · exact (sign_mem fuel cs r m).mpr (Or.inl ⟨hm, by simpa using hcs⟩)
    · exact (sign_mem fuel cs r m).mpr (Or.inr ⟨hm, by simpa using hcs⟩)

theorem integer_mem (fuel : Nat) (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym Decimal.grammar "" (fuel + 1) (Sym.ref "Integer") cs ↔
      ∃ p, m = [("Integer", String.ofList p)] ∧ cs = p ++ r ∧
        matchesTerm TokClass.digit LenSpec.atLeastOne (String.ofList p) := by
  exact mem_matchSym_ref_single_term_iff Decimal.grammar fuel "Integer" "Integer"
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
              SymItem.mk (Sym.ref "Integer") false,
              SymItem.mk (Sym.lit ".") false,
              SymItem.mk (Sym.ref "Fraction") false]]) cs ↔
      ∃ sgn integer fraction,
        (sgn = "-" ∨ sgn = "") ∧
        m = [("Sign", sgn), ("Integer", integer), ("Fraction", fraction)] ∧
        cs = sgn.toList ++ integer.toList ++ '.' :: fraction.toList ++ r ∧
        Triptych.IsDigits integer ∧ Triptych.IsDigitsBetween 1 4 fraction := by
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
    obtain ⟨sgn, hsgn, rfl, hsgncs⟩ := (sign_parts_mem 3 cs restS mS).mp hS
    obtain ⟨i, rfl, hi, hdi⟩ := (integer_mem 3 _ _ _).mp hI
    obtain ⟨rfl, rfl⟩ := (mem_matchSym_lit_iff Decimal.grammar "" 4 "." _ _ _).mp hDot
    obtain ⟨f, rfl, hf, hdf⟩ := (fraction_mem 3 _ _ _).mp hF
    refine ⟨sgn, String.ofList i, String.ofList f, hsgn, ?_, ?_, ?_, ?_⟩
    · simp
    · simp [hsgncs, hi, hf, List.append_assoc]
    · simpa [Triptych.IsDigits_matchesTerm] using hdi
    · simpa [Triptych.IsDigitsBetween_matchesTerm] using hdf
  · rintro ⟨sgn, integer, fraction, hsgn, rfl, hcs, hi, hf⟩
    rw [mem_matchSeq_cons_required_iff Decimal.grammar "" 4 _ _ rfl]
    refine ⟨[("Sign", sgn)], integer.toList ++ '.' :: fraction.toList ++ r,
      [("Integer", integer), ("Fraction", fraction)], ?_, ?_, by simp⟩
    · exact (sign_parts_mem 3 _ _ _).mpr
        ⟨sgn, hsgn, rfl, by simpa [List.append_assoc] using hcs⟩
    · rw [mem_matchSeq_cons_required_iff Decimal.grammar "" 4 _ _ rfl]
      refine ⟨[("Integer", integer)], '.' :: fraction.toList ++ r,
        [("Fraction", fraction)], ?_, ?_, by simp⟩
      · exact (integer_mem 3 _ _ _).mpr
          ⟨integer.toList, by simp, by simp [List.append_assoc],
            by rw [Triptych.IsDigits_matchesTerm, String.ofList_toList]; exact hi⟩
      · rw [mem_matchSeq_cons_required_iff Decimal.grammar "" 4 _ _ rfl]
        refine ⟨[], fraction.toList ++ r, [("Fraction", fraction)], ?_, ?_, by simp⟩
        · exact (mem_matchSym_lit_iff Decimal.grammar "" 4 "." _ _ _).mpr ⟨rfl, rfl⟩
        · rw [mem_matchSeq_cons_required_iff Decimal.grammar "" 4 _ _ rfl]
          refine ⟨[("Fraction", fraction)], r, [], ?_, ?_, by simp⟩
          · exact (fraction_mem 3 _ _ _).mpr
              ⟨fraction.toList, by simp, rfl,
                by rw [Triptych.IsDigitsBetween_matchesTerm, String.ofList_toList]; exact hf⟩
          · simp [matchSeq]

theorem decode_decimal_sound {s : String} {m : CaptureMap}
    (h : decode Decimal.grammar s = some m) :
    ∃ sgn integer fraction,
      (sgn = "-" ∨ sgn = "") ∧
      m = [("Sign", sgn), ("Integer", integer), ("Fraction", fraction)] ∧
      s = sgn ++ integer ++ "." ++ fraction ∧
      Triptych.IsDigits integer ∧ Triptych.IsDigitsBetween 1 4 fraction := by
  obtain ⟨p, hstart, hmem⟩ := mem_matchProd_of_decode_eq_some h
  have hp :
      p =
        Production.mk "Decimal"
          [[SymItem.mk (Sym.ref "Sign") false,
            SymItem.mk (Sym.ref "Integer") false,
            SymItem.mk (Sym.lit ".") false,
            SymItem.mk (Sym.ref "Fraction") false]] := by
    have hknown :
        Decimal.grammar.startProd? =
          some
            (Production.mk "Decimal"
              [[SymItem.mk (Sym.ref "Sign") false,
                SymItem.mk (Sym.ref "Integer") false,
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
              SymItem.mk (Sym.ref "Integer") false,
              SymItem.mk (Sym.lit ".") false,
              SymItem.mk (Sym.ref "Fraction") false]])
          s.toList := by
    simpa [Decimal.grammar] using hmem
  obtain ⟨sgn, integer, fraction, hsgn, hm, hs, hi, hf⟩ :=
    (decimal_match_mem s.toList [] m).mp hxmem
  refine ⟨sgn, integer, fraction, hsgn, hm, ?_, hi, hf⟩
  rw [← String.toList_inj]
  simpa [String.toList_append, List.append_assoc] using hs

theorem no_dot_of_digits {s : String} (h : Triptych.IsDigits s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = '.')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq
  subst c
  have := h.1 '.' hc
  simp [Triptych.TokClass.mem] at this

theorem split_decimal (left right : String)
    (hleft : ∀ c ∈ left.toList, (fun x : Char => decide (x = '.')) c = false)
    (hright : ∀ c ∈ right.toList, (fun x : Char => decide (x = '.')) c = false) :
    (left ++ "." ++ right).splitToList (· = '.') = [left, right] := by
  simpa using
    splitToList_eq left right (fun x : Char => decide (x = '.')) '.' (by simp) hleft hright

theorem cedar_wf_to_surface {s : String} (h : Cedar.Thm.Decimal.IsWfStr s) :
    Decimal.IsWf.Decimal s := by
  rw [Triptych.Theorems.Decimal.CedarInternals.isWfStr_iff] at h
  obtain ⟨left, fraction, hsplit, _, hfracPos, hfracLen, hleft, hfrac⟩ := h
  have hs := join_split hsplit
  have hfDigits : Triptych.IsDigits fraction :=
    (digits_iff fraction).mpr (toNatIsSome_iff_isDigits.mp hfrac)
  have hf : Triptych.IsDigitsBetween 1 4 fraction :=
    ⟨hfDigits.1, by omega, hfracLen⟩
  obtain ⟨leftValue, hleftValue⟩ := Option.isSome_iff_exists.mp hleft
  unfold toInt?' at hleftValue
  split at hleftValue
  · simp at hleftValue
  · rename_i hno
    rw [Bool.not_eq_true] at hno
    rcases String.toInt?_eq_some_iff.mp hleftValue with
      ⟨leftNat, hleftNat, _⟩ | ⟨integer, hleftEq, integerNat, hintegerNat, _⟩
    · have hleftNat' : toNat?' left = some leftNat := by
        unfold toNat?'
        rw [hno]
        exact hleftNat
      have hi : Triptych.IsDigits left :=
        (digits_iff left).mpr (toNatIsSome_iff_isDigits.mp (by simp [hleftNat']))
      exact ⟨"", left, fraction,
        ⟨⟨by simpa [String.append_assoc] using hs, Or.inr rfl⟩, hi⟩, hf⟩
    · have hintegerNoUnderscore : integer.contains '_' = false := by
        have hnot : ¬ ('_' ∈ integer.toList) := by
          intro hm
          have hmleft : '_' ∈ left.toList := by
            rw [hleftEq, String.toList_append]
            exact List.mem_append_right _ hm
          have hcontains : left.contains '_' = true := by
            simpa [String.contains] using hmleft
          rw [hcontains] at hno
          contradiction
        simpa [String.contains] using hnot
      have hintegerNat' : toNat?' integer = some integerNat := by
        unfold toNat?'
        rw [hintegerNoUnderscore]
        exact hintegerNat
      have hi : Triptych.IsDigits integer :=
        (digits_iff integer).mpr
          (toNatIsSome_iff_isDigits.mp (by simp [hintegerNat']))
      exact ⟨"-", integer, fraction,
        ⟨⟨by simpa [hleftEq, String.append_assoc] using hs, Or.inl rfl⟩, hi⟩, hf⟩

theorem surface_wf_to_cedar {s : String} (h : Decimal.IsWf.Decimal s) :
    Cedar.Thm.Decimal.IsWfStr s := by
  rw [Triptych.Theorems.Decimal.CedarInternals.isWfStr_iff]
  obtain ⟨sgn, integer, fraction, ⟨⟨hs, hsgn⟩, hi⟩, hf⟩ := h
  have hi' : _root_.IsDigits integer := (digits_iff integer).mp hi
  have hfDigits : Triptych.IsDigits fraction := ⟨hf.1, hf.2.1⟩
  have hf' : _root_.IsDigits fraction := (digits_iff fraction).mp hfDigits
  refine ⟨sgn ++ integer, fraction, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs]
    apply split_decimal
    · intro c hc
      rw [String.toList_append] at hc
      cases List.mem_append.mp hc with
      | inl hc =>
          rcases hsgn with rfl | rfl
          · simp at hc
            subst c
            decide
          · simp at hc
      | inr hc => exact no_dot_of_digits hi c hc
    · exact no_dot_of_digits hfDigits
  · rcases hsgn with rfl | rfl
    · intro heq
      have hempty : integer = "" := by simpa using heq
      subst integer
      simpa using hi.2
    · intro heq
      have hdash : integer = "-" := by simpa using heq
      subst integer
      have := hi.1 '-' (by simp)
      simp [Triptych.TokClass.mem] at this
  · have hmin := hf.2.1
    omega
  · exact hf.2.2
  · rw [toInt_parts_eq sgn integer hsgn hi']
    simp
  · rw [readNat_eq fraction hf']
    simp

theorem format_compute_of_decode (s sgn integer fraction : String)
    (h : decode Decimal.grammar s =
      some [("Sign", sgn), ("Integer", integer), ("Fraction", fraction)]) :
    Decimal.computeValue s = some (Decimal.value sgn integer fraction) := by
  unfold Decimal.computeValue Triptych.computeValue
  rw [h]
  simp [Decimal.valueExpr, Decimal.value, ValExpr.eval, CaptureMap.toEnv,
    Triptych.Env.signVal, Triptych.Env.natVal, Triptych.Env.lenVal,
    Triptych.signOf, Triptych.natOf, Triptych.lenOf]

theorem cedar_compute_of_parts (s sgn integer fraction : String)
    (hs : s = sgn ++ integer ++ "." ++ fraction)
    (hsgn : sgn = "-" ∨ sgn = "")
    (hi : Triptych.IsDigits integer)
    (hf : Triptych.IsDigitsBetween 1 4 fraction) :
    Cedar.Thm.Decimal.computeValue s = Decimal.value sgn integer fraction := by
  have hi' : _root_.IsDigits integer := (digits_iff integer).mp hi
  have hfDigits : Triptych.IsDigits fraction := ⟨hf.1, hf.2.1⟩
  have hf' : _root_.IsDigits fraction := (digits_iff fraction).mp hfDigits
  have hleftNoDot :
      ∀ c ∈ (sgn ++ integer).toList, (fun x : Char => decide (x = '.')) c = false := by
    intro c hc
    rw [String.toList_append] at hc
    cases List.mem_append.mp hc with
    | inl hc =>
        rcases hsgn with rfl | rfl
        · simp at hc
          subst c
          decide
        · simp at hc
    | inr hc => exact no_dot_of_digits hi c hc
  rw [hs]
  rw [Triptych.Theorems.Decimal.CedarInternals.computeValue_eq]
  rw [split_decimal (sgn ++ integer) fraction hleftNoDot (no_dot_of_digits hfDigits)]
  simp only
  rw [toInt_parts_eq sgn integer hsgn hi', readNat_eq fraction hf']
  have hlen : fraction.length ≤ 4 := hf.2.2
  have hexp : ((4 : Int) - (fraction.length : Int)).toNat = 4 - fraction.length := by
    omega
  unfold Decimal.value Triptych.natOf Triptych.lenOf
  rw [hexp]
  rw [show Int.pow 10 4 = (10000 : Int) from by rfl]
  rcases hsgn with rfl | rfl
  · simp [Triptych.signOf]
    rw [show (10 : Int) ^ (4 - fraction.length) =
      Int.pow 10 (4 - fraction.length) from rfl]
    omega
  · simp only [String.empty_append, Triptych.signOf]
    have hnot : ¬ ['-'] <+: integer.toList := by
      intro hp
      have hm : '-' ∈ integer.toList := List.IsPrefix.subset hp (by simp)
      have := hi'.2 '-' hm
      simp at this
    have hstarts : integer.startsWith "-" = false :=
      String.startsWith_string_eq_false_iff.mpr hnot
    rw [hstarts]
    simp
    rw [show (10 : Int) ^ (4 - fraction.length) =
      Int.pow 10 (4 - fraction.length) from rfl]

theorem decode_parts_of_surface_wf {s : String} (h : Decimal.IsWf.Decimal s) :
    ∃ sgn integer fraction,
      decode Decimal.grammar s =
        some [("Sign", sgn), ("Integer", integer), ("Fraction", fraction)] ∧
      (sgn = "-" ∨ sgn = "") ∧
      s = sgn ++ integer ++ "." ++ fraction ∧
      Triptych.IsDigits integer ∧ Triptych.IsDigitsBetween 1 4 fraction := by
  have hwf : IsWf Decimal.grammar s := (Decimal.IsWf_equiv s).mpr h
  have hsome : (decode Decimal.grammar s).isSome = true :=
    (decodeSome_iff_IsWf Decimal.grammar (by decide) s).mpr hwf
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨sgn, integer, fraction, hsgn, rfl, hs, hi, hf⟩ :=
    decode_decimal_sound hm
  exact ⟨sgn, integer, fraction, hm, hsgn, hs, hi, hf⟩

theorem bridge_value (s : String) (h : Cedar.Thm.Decimal.IsWfStr s) :
    Decimal.computeValue s = some (Cedar.Thm.Decimal.computeValue s) := by
  have hsurface := cedar_wf_to_surface h
  obtain ⟨sgn, integer, fraction, hdecode, hsgn, hs, hi, hf⟩ :=
    decode_parts_of_surface_wf hsurface
  rw [format_compute_of_decode s sgn integer fraction hdecode,
    cedar_compute_of_parts s sgn integer fraction hs hsgn hi hf]

theorem constraints_of_decode (s sgn integer fraction : String)
    (h : decode Decimal.grammar s =
      some [("Sign", sgn), ("Integer", integer), ("Fraction", fraction)]) :
    Decimal.SatisfiesConstraints s ↔
      (-9223372036854775808 : Int) ≤ Decimal.value sgn integer fraction ∧
        Decimal.value sgn integer fraction ≤ (9223372036854775807 : Int) := by
  unfold Decimal.SatisfiesConstraints Decimal.Constraints Triptych.component Triptych.envOf
  rw [h]
  simp [CaptureMap.toEnv]

theorem bridge_isValid (s : String) :
    Decimal.IsValid s ↔
      Cedar.Thm.Decimal.IsWfStr s ∧
        (-9223372036854775808 : Int) ≤ Cedar.Thm.Decimal.computeValue s ∧
        Cedar.Thm.Decimal.computeValue s ≤ (9223372036854775807 : Int) := by
  constructor
  · rintro ⟨hwf, hconstraints⟩
    have hcedar := surface_wf_to_cedar hwf
    obtain ⟨sgn, integer, fraction, hdecode, _, _, _, _⟩ :=
      decode_parts_of_surface_wf hwf
    have hformat := format_compute_of_decode s sgn integer fraction hdecode
    have hvalue : Decimal.value sgn integer fraction = Cedar.Thm.Decimal.computeValue s := by
      rw [bridge_value s hcedar] at hformat
      exact Option.some.inj hformat.symm
    refine ⟨hcedar, ?_⟩
    simpa [hvalue] using
      (constraints_of_decode s sgn integer fraction hdecode).mp hconstraints
  · rintro ⟨hcedar, hrange⟩
    have hwf := cedar_wf_to_surface hcedar
    obtain ⟨sgn, integer, fraction, hdecode, _, _, _, _⟩ :=
      decode_parts_of_surface_wf hwf
    have hformat := format_compute_of_decode s sgn integer fraction hdecode
    have hv : Decimal.value sgn integer fraction = Cedar.Thm.Decimal.computeValue s := by
      rw [bridge_value s hcedar] at hformat
      exact Option.some.inj hformat.symm
    refine ⟨hwf, (constraints_of_decode s sgn integer fraction hdecode).mpr ?_⟩
    simpa [hv] using hrange

end Decimal.CedarBridge
