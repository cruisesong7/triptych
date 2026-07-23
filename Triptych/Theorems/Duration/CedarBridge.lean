import Triptych.Examples.Duration.parser
import Triptych.Theorems.Cedar.String
import Triptych.Theorems.DecodeLemmas
import Triptych.Theorems.Duration.CedarInternals
import Cedar.Thm.Ext.Duration

/-! Bridges the generated Duration specification to Cedar's Duration metatheory. -/

open Cedar.Spec.Ext
open Cedar.Spec.Ext.Datetime
open Triptych
open Triptych.Theorems.Cedar.String
open Triptych.Theorems.Duration.CedarInternals

namespace Duration.CedarBridge

def OptionalDigitsWf : Option String → Prop
  | none => True
  | some digits => Triptych.IsDigits digits

def unitCaptures (unit digitsName suffix : String) : Option String → CaptureMap
  | none => []
  | some digits =>
      [(unit, digits ++ suffix), ("Components." ++ unit, digits ++ suffix),
        (digitsName, digits), (unit ++ "." ++ digitsName, digits)]

def componentsCaptures (components : Cedar.Thm.Duration.Components) : CaptureMap :=
  unitCaptures "Days" "DDays" "d" components.days ++
    unitCaptures "Hours" "DHours" "h" components.hours ++
    unitCaptures "Minutes" "DMinutes" "m" components.minutes ++
    unitCaptures "Seconds" "DSeconds" "s" components.seconds ++
    unitCaptures "Millis" "DMillis" "ms" components.milliseconds

def ComponentsWf (components : Cedar.Thm.Duration.Components) : Prop :=
  OptionalDigitsWf components.days ∧
    OptionalDigitsWf components.hours ∧
    OptionalDigitsWf components.minutes ∧
    OptionalDigitsWf components.seconds ∧
    OptionalDigitsWf components.milliseconds

theorem sign_cases_mem (fuel : Nat) (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym Duration.grammar "" (fuel + 1) (Sym.ref "Sign") cs ↔
      (m = [("Sign", "-")] ∧ cs = '-' :: r) ∨
      (m = [("Sign", "")] ∧ cs = r) := by
  simp [matchSym, Duration.grammar, Grammar.prod?, matchProd, matchSeq]
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

theorem sign_mem (fuel : Nat) (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym Duration.grammar "" (fuel + 1) (Sym.ref "Sign") cs ↔
      ∃ sgn, (sgn = "-" ∨ sgn = "") ∧
        m = [("Sign", sgn)] ∧ cs = sgn.toList ++ r := by
  constructor
  · intro h
    rcases (sign_cases_mem fuel cs r m).mp h with hminus | hempty
    · exact ⟨"-", Or.inl rfl, hminus.1, by simpa using hminus.2⟩
    · exact ⟨"", Or.inr rfl, hempty.1, by simpa using hempty.2⟩
  · rintro ⟨sgn, hsign, hm, hcs⟩
    rcases hsign with rfl | rfl
    · exact (sign_cases_mem fuel cs r m).mpr (Or.inl ⟨hm, by simpa using hcs⟩)
    · exact (sign_cases_mem fuel cs r m).mpr (Or.inr ⟨hm, by simpa using hcs⟩)

theorem unit_mem (fuel : Nat) (unit digitsName suffix : String) (hunitNe : unit ≠ "")
    (hunit :
      Duration.grammar.prod? unit =
        some
          (Production.mk unit
            [[SymItem.mk (Sym.ref digitsName) false,
              SymItem.mk (Sym.lit suffix) false]]))
    (hdigits :
      Duration.grammar.prod? digitsName =
        some
          (Production.mk digitsName
            [[SymItem.mk (Sym.term TokClass.digit LenSpec.atLeastOne) false]]))
    (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈
        matchSym Duration.grammar "Components" (fuel + 2) (Sym.ref unit) cs ↔
      ∃ digits,
        m =
          [(unit, digits ++ suffix), ("Components." ++ unit, digits ++ suffix),
            (digitsName, digits), (unit ++ "." ++ digitsName, digits)] ∧
        cs = (digits ++ suffix).toList ++ r ∧
        Triptych.IsDigits digits := by
  rw [mem_matchSym_ref_iff Duration.grammar "Components" (fuel + 1) unit _ hunit]
  constructor
  · rintro ⟨inner, hinner, rfl⟩
    rw [matchProd] at hinner
    simp only [List.mem_flatMap, List.mem_singleton, exists_eq_left] at hinner
    obtain ⟨mDigits, restDigits, mRest, hDigits, hRest, rfl⟩ :=
      (mem_matchSeq_cons_required_iff Duration.grammar unit (fuel + 1) _ _ rfl
        cs r inner).mp hinner
    obtain ⟨mSuffix, restSuffix, mNil, hSuffix, hNil, rfl⟩ :=
      (mem_matchSeq_cons_required_iff Duration.grammar unit (fuel + 1) _ _ rfl
        restDigits r mRest).mp hRest
    simp only [matchSeq, List.mem_singleton, Prod.mk.injEq] at hNil
    obtain ⟨rfl, rfl⟩ := hNil
    obtain ⟨p, rfl, hcs, hp⟩ :=
      (mem_matchSym_ref_single_term_qualified_iff Duration.grammar unit fuel
        digitsName digitsName TokClass.digit LenSpec.atLeastOne hdigits _ _ _).mp hDigits
    obtain ⟨rfl, hsuffix⟩ :=
      (mem_matchSym_lit_iff Duration.grammar unit (fuel + 1) suffix _ _ _).mp hSuffix
    have htake : cs.take (cs.length - r.length) = p ++ suffix.toList := by
      rw [hcs, hsuffix]
      simp only [List.length_append]
      rw [show p.length + (suffix.toList.length + r.length) - r.length =
        (p ++ suffix.toList).length by simp; omega]
      rw [show p ++ (suffix.toList ++ r) = (p ++ suffix.toList) ++ r by
        simp [List.append_assoc]]
      exact List.take_left
    refine ⟨String.ofList p, ?_, ?_, ?_⟩
    · simp [htake, hunitNe]
    · simp [hcs, hsuffix, String.toList_append, List.append_assoc]
    · rw [Triptych.IsDigits_matchesTerm] at hp
      exact hp
  · rintro ⟨digits, rfl, hcs, hdigitsWf⟩
    refine ⟨
      [(digitsName, digits), (unit ++ "." ++ digitsName, digits)], ?_, ?_⟩
    · rw [matchProd]
      simp only [List.mem_flatMap, List.mem_singleton, exists_eq_left]
      rw [mem_matchSeq_cons_required_iff Duration.grammar unit (fuel + 1) _ _ rfl]
      refine ⟨[(digitsName, digits), (unit ++ "." ++ digitsName, digits)],
        suffix.toList ++ r, [], ?_, ?_, by simp⟩
      · exact
          (mem_matchSym_ref_single_term_qualified_iff Duration.grammar unit fuel
            digitsName digitsName TokClass.digit LenSpec.atLeastOne hdigits _ _ _).mpr
            ⟨digits.toList, by simp [hunitNe],
              by simpa [String.toList_append, List.append_assoc] using hcs,
              by simpa [Triptych.IsDigits_matchesTerm] using hdigitsWf⟩
      · rw [mem_matchSeq_cons_required_iff Duration.grammar unit (fuel + 1) _ _ rfl]
        refine ⟨[], r, [], ?_, by simp [matchSeq], by simp⟩
        exact (mem_matchSym_lit_iff Duration.grammar unit (fuel + 1) suffix _ _ _).mpr
          ⟨rfl, rfl⟩
    · have htake :
          cs.take (cs.length - r.length) = digits.toList ++ suffix.toList := by
        rw [hcs]
        simp only [String.toList_append, List.length_append]
        rw [show digits.toList.length + suffix.toList.length + r.length - r.length =
          (digits.toList ++ suffix.toList).length by simp]
        rw [show digits.toList ++ suffix.toList ++ r =
          (digits.toList ++ suffix.toList) ++ r from rfl]
        exact List.take_left
      simp [htake]

theorem optional_unit_cons_mem (fuel : Nat) (unit digitsName suffix : String)
    (hunitNe : unit ≠ "")
    (hunit :
      Duration.grammar.prod? unit =
        some
          (Production.mk unit
            [[SymItem.mk (Sym.ref digitsName) false,
              SymItem.mk (Sym.lit suffix) false]]))
    (hdigits :
      Duration.grammar.prod? digitsName =
        some
          (Production.mk digitsName
            [[SymItem.mk (Sym.term TokClass.digit LenSpec.atLeastOne) false]]))
    (rest : Seq) (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈
        matchSeq Duration.grammar "Components" (fuel + 2)
          (SymItem.mk (Sym.ref unit) true :: rest) cs ↔
      ∃ digits mid mRest,
        m = unitCaptures unit digitsName suffix digits ++ mRest ∧
        cs = (Cedar.Thm.Duration.durationChunk digits suffix).toList ++ mid ∧
        OptionalDigitsWf digits ∧
        (mRest, r) ∈ matchSeq Duration.grammar "Components" (fuel + 2) rest mid := by
  rw [mem_matchSeq_cons_optional_iff Duration.grammar "Components" (fuel + 2) _ _ rfl]
  constructor
  · rintro (⟨mUnit, mid, mRest, hUnit, hRest, rfl⟩ | hRest)
    · obtain ⟨digits, rfl, hcs, hwf⟩ :=
        (unit_mem fuel unit digitsName suffix hunitNe hunit hdigits _ _ _).mp hUnit
      exact ⟨some digits, mid, mRest, by simp [unitCaptures],
        by simpa [Cedar.Thm.Duration.durationChunk] using hcs, hwf, hRest⟩
    · exact ⟨none, cs, m, by simp [unitCaptures],
        by simp [Cedar.Thm.Duration.durationChunk], trivial, hRest⟩
  · rintro ⟨digits, mid, mRest, hm, hcs, hwf, hRest⟩
    cases digits with
    | none =>
        simp only [unitCaptures, List.nil_append] at hm
        simp only [Cedar.Thm.Duration.durationChunk, String.toList_empty,
          List.nil_append] at hcs
        subst mRest
        subst mid
        exact Or.inr hRest
    | some digits =>
        apply Or.inl
        refine ⟨unitCaptures unit digitsName suffix (some digits), mid, mRest, ?_,
          hRest, hm⟩
        simpa [unitCaptures, Cedar.Thm.Duration.durationChunk] using
          (unit_mem fuel unit digitsName suffix hunitNe hunit hdigits cs mid
            (unitCaptures unit digitsName suffix (some digits))).mpr
            ⟨digits, by simp [unitCaptures], by
              simpa [Cedar.Thm.Duration.durationChunk] using hcs, hwf⟩

theorem components_mem (fuel : Nat) (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈
        matchSym Duration.grammar "" (fuel + 3) (Sym.ref "Components") cs ↔
      ∃ components : Cedar.Thm.Duration.Components,
        m = [("Components", components.asString)] ++ componentsCaptures components ∧
        cs = components.asString.toList ++ r ∧
        ComponentsWf components := by
  rw [mem_matchSym_ref_iff Duration.grammar "" (fuel + 2) "Components" _
    (show
      Duration.grammar.prod? "Components" =
        some
          (Production.mk "Components"
            [[SymItem.mk (Sym.ref "Days") true,
              SymItem.mk (Sym.ref "Hours") true,
              SymItem.mk (Sym.ref "Minutes") true,
              SymItem.mk (Sym.ref "Seconds") true,
              SymItem.mk (Sym.ref "Millis") true]])
      from rfl)]
  constructor
  · rintro ⟨inner, hinner, rfl⟩
    rw [matchProd] at hinner
    simp only [List.mem_flatMap, List.mem_singleton, exists_eq_left] at hinner
    obtain ⟨days, restDays, mDays, rfl, hDays, hwfDays, hrest⟩ :=
      (optional_unit_cons_mem fuel "Days" "DDays" "d" (by decide) rfl rfl _
        cs r inner).mp hinner
    obtain ⟨hours, restHours, mHours, rfl, hHours, hwfHours, hrest⟩ :=
      (optional_unit_cons_mem fuel "Hours" "DHours" "h" (by decide) rfl rfl _
        restDays r mDays).mp hrest
    obtain ⟨minutes, restMinutes, mMinutes, rfl, hMinutes, hwfMinutes, hrest⟩ :=
      (optional_unit_cons_mem fuel "Minutes" "DMinutes" "m" (by decide) rfl rfl _
        restHours r mHours).mp hrest
    obtain ⟨seconds, restSeconds, mSeconds, rfl, hSeconds, hwfSeconds, hrest⟩ :=
      (optional_unit_cons_mem fuel "Seconds" "DSeconds" "s" (by decide) rfl rfl _
        restMinutes r mMinutes).mp hrest
    obtain ⟨milliseconds, restMillis, mMillis, rfl, hMillis, hwfMillis, hrest⟩ :=
      (optional_unit_cons_mem fuel "Millis" "DMillis" "ms" (by decide) rfl rfl _
        restSeconds r mSeconds).mp hrest
    simp only [matchSeq, List.mem_singleton, Prod.mk.injEq] at hrest
    obtain ⟨rfl, rfl⟩ := hrest
    let components : Cedar.Thm.Duration.Components :=
      ⟨days, hours, minutes, seconds, milliseconds⟩
    have hcs : cs = components.asString.toList ++ r := by
      rw [hDays, hHours, hMinutes, hSeconds, hMillis]
      simp [components, Cedar.Thm.Duration.Components.asString, String.toList_append,
        List.append_assoc]
    have htake : cs.take (cs.length - r.length) = components.asString.toList := by
      rw [hcs]
      simp
    refine ⟨components, ?_, hcs, ?_⟩
    · simp [componentsCaptures, components, htake]
    · exact ⟨hwfDays, hwfHours, hwfMinutes, hwfSeconds, hwfMillis⟩
  · rintro ⟨⟨days, hours, minutes, seconds, milliseconds⟩, rfl, hcs,
      hwfDays, hwfHours, hwfMinutes, hwfSeconds, hwfMillis⟩
    refine ⟨componentsCaptures ⟨days, hours, minutes, seconds, milliseconds⟩, ?_, ?_⟩
    · rw [matchProd]
      simp only [List.mem_flatMap, List.mem_singleton, exists_eq_left]
      rw [optional_unit_cons_mem fuel "Days" "DDays" "d" (by decide) rfl rfl]
      refine ⟨days,
        (Cedar.Thm.Duration.durationChunk hours "h" ++
          Cedar.Thm.Duration.durationChunk minutes "m" ++
          Cedar.Thm.Duration.durationChunk seconds "s" ++
          Cedar.Thm.Duration.durationChunk milliseconds "ms").toList ++ r,
        unitCaptures "Hours" "DHours" "h" hours ++
          unitCaptures "Minutes" "DMinutes" "m" minutes ++
          unitCaptures "Seconds" "DSeconds" "s" seconds ++
          unitCaptures "Millis" "DMillis" "ms" milliseconds,
        by simp [componentsCaptures], ?_, hwfDays, ?_⟩
      · simpa [Cedar.Thm.Duration.Components.asString, String.toList_append,
          List.append_assoc] using hcs
      · rw [optional_unit_cons_mem fuel "Hours" "DHours" "h" (by decide) rfl rfl]
        refine ⟨hours,
          (Cedar.Thm.Duration.durationChunk minutes "m" ++
            Cedar.Thm.Duration.durationChunk seconds "s" ++
            Cedar.Thm.Duration.durationChunk milliseconds "ms").toList ++ r,
          unitCaptures "Minutes" "DMinutes" "m" minutes ++
            unitCaptures "Seconds" "DSeconds" "s" seconds ++
            unitCaptures "Millis" "DMillis" "ms" milliseconds,
          by simp [List.append_assoc],
          by simp [String.toList_append, List.append_assoc], hwfHours, ?_⟩
        rw [optional_unit_cons_mem fuel "Minutes" "DMinutes" "m" (by decide) rfl rfl]
        refine ⟨minutes,
          (Cedar.Thm.Duration.durationChunk seconds "s" ++
            Cedar.Thm.Duration.durationChunk milliseconds "ms").toList ++ r,
          unitCaptures "Seconds" "DSeconds" "s" seconds ++
            unitCaptures "Millis" "DMillis" "ms" milliseconds,
          by simp [List.append_assoc],
          by simp [String.toList_append, List.append_assoc], hwfMinutes, ?_⟩
        rw [optional_unit_cons_mem fuel "Seconds" "DSeconds" "s" (by decide) rfl rfl]
        refine ⟨seconds,
          (Cedar.Thm.Duration.durationChunk milliseconds "ms").toList ++ r,
          unitCaptures "Millis" "DMillis" "ms" milliseconds,
          rfl, by simp [String.toList_append, List.append_assoc], hwfSeconds, ?_⟩
        rw [optional_unit_cons_mem fuel "Millis" "DMillis" "ms" (by decide) rfl rfl]
        exact ⟨milliseconds, r, [], by simp, by simp, hwfMillis, by simp [matchSeq]⟩
    · have htake :
          cs.take (cs.length - r.length) =
            (Cedar.Thm.Duration.Components.asString
              ⟨days, hours, minutes, seconds, milliseconds⟩).toList := by
        rw [hcs]
        simp
      simp [htake]

theorem optional_digits_wf_iff (digits : Option String) :
    OptionalDigitsWf digits ↔ Cedar.Thm.Duration.IsWfOptionalQuantity digits := by
  cases digits <;>
    simp [OptionalDigitsWf, Cedar.Thm.Duration.IsWfOptionalQuantity, digits_iff]

theorem components_wf_iff (components : Cedar.Thm.Duration.Components) :
    ComponentsWf components ↔ components.quantitiesWf := by
  rcases components with ⟨days, hours, minutes, seconds, milliseconds⟩
  simp [ComponentsWf, Cedar.Thm.Duration.Components.quantitiesWf,
    optional_digits_wf_iff]

theorem components_nonempty_iff (components : Cedar.Thm.Duration.Components) :
    components.asString ≠ "" ↔ components.nonempty := by
  rcases components with ⟨days, hours, minutes, seconds, milliseconds⟩
  cases days <;> cases hours <;> cases minutes <;> cases seconds <;>
    cases milliseconds <;>
    simp [Cedar.Thm.Duration.Components.asString,
      Cedar.Thm.Duration.Components.nonempty, Cedar.Thm.Duration.durationChunk]

theorem duration_match_mem (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈
        matchProd Duration.grammar "" 13
          (Production.mk "Duration"
            [[SymItem.mk (Sym.ref "Sign") false,
              SymItem.mk (Sym.ref "Components") false]]) cs ↔
      ∃ sgn components,
        (sgn = "-" ∨ sgn = "") ∧
        m =
          [("Sign", sgn), ("Components", components.asString)] ++
            componentsCaptures components ∧
        cs = sgn.toList ++ components.asString.toList ++ r ∧
        ComponentsWf components := by
  rw [matchProd]
  simp only [List.mem_flatMap, List.mem_singleton, exists_eq_left]
  constructor
  · intro hmem
    obtain ⟨mSign, restSign, mRest, hSign, hRest, rfl⟩ :=
      (mem_matchSeq_cons_required_iff Duration.grammar "" 13 _ _ rfl
        cs r m).mp hmem
    obtain ⟨mComponents, restComponents, mNil, hComponents, hNil, rfl⟩ :=
      (mem_matchSeq_cons_required_iff Duration.grammar "" 13 _ _ rfl
        restSign r mRest).mp hRest
    simp only [matchSeq, List.mem_singleton, Prod.mk.injEq] at hNil
    obtain ⟨rfl, rfl⟩ := hNil
    obtain ⟨sgn, hsgn, rfl, hcsSign⟩ := (sign_mem 12 cs restSign mSign).mp hSign
    obtain ⟨components, rfl, hcsComponents, hwf⟩ :=
      (components_mem 10 restSign r mComponents).mp hComponents
    exact ⟨sgn, components, hsgn, by simp, by
      simp [hcsSign, hcsComponents, List.append_assoc], hwf⟩
  · rintro ⟨sgn, components, hsgn, rfl, hcs, hwf⟩
    rw [mem_matchSeq_cons_required_iff Duration.grammar "" 13 _ _ rfl]
    refine ⟨[("Sign", sgn)], components.asString.toList ++ r,
      [("Components", components.asString)] ++ componentsCaptures components,
      ?_, ?_, by simp⟩
    · exact (sign_mem 12 _ _ _).mpr
        ⟨sgn, hsgn, rfl, by simpa [List.append_assoc] using hcs⟩
    · rw [mem_matchSeq_cons_required_iff Duration.grammar "" 13 _ _ rfl]
      refine ⟨[("Components", components.asString)] ++ componentsCaptures components,
        r, [], ?_, by simp [matchSeq], by simp⟩
      exact (components_mem 10 _ _ _).mpr ⟨components, rfl, rfl, hwf⟩

theorem decode_duration_sound {s : String} {m : CaptureMap}
    (h : decode Duration.grammar s = some m) :
    ∃ sgn components,
      (sgn = "-" ∨ sgn = "") ∧
      m =
        [("Sign", sgn), ("Components", components.asString)] ++
          componentsCaptures components ∧
      s = sgn ++ components.asString ∧
      ComponentsWf components := by
  obtain ⟨p, hstart, hmem⟩ := mem_matchProd_of_decode_eq_some h
  have hp :
      p =
        Production.mk "Duration"
          [[SymItem.mk (Sym.ref "Sign") false,
            SymItem.mk (Sym.ref "Components") false]] := by
    have hknown :
        Duration.grammar.startProd? =
          some
            (Production.mk "Duration"
              [[SymItem.mk (Sym.ref "Sign") false,
                SymItem.mk (Sym.ref "Components") false]]) := rfl
    rw [hknown] at hstart
    exact (Option.some.inj hstart).symm
  subst p
  have hxmem :
      (m, ([] : List Char)) ∈
        matchProd Duration.grammar "" 13
          (Production.mk "Duration"
            [[SymItem.mk (Sym.ref "Sign") false,
              SymItem.mk (Sym.ref "Components") false]]) s.toList := by
    simpa [Duration.grammar] using hmem
  obtain ⟨sgn, components, hsgn, hm, hs, hwf⟩ :=
    (duration_match_mem s.toList [] m).mp hxmem
  refine ⟨sgn, components, hsgn, hm, ?_, hwf⟩
  rw [← String.toList_inj]
  simpa [String.toList_append, List.append_assoc] using hs

theorem optional_chunk_surface (digits : Option String) (suffix : String)
    (hwf : OptionalDigitsWf digits) :
    Cedar.Thm.Duration.durationChunk digits suffix = "" ∨
      ∃ digitsValue,
        Cedar.Thm.Duration.durationChunk digits suffix = digitsValue ++ suffix ∧
          Triptych.IsDigits digitsValue := by
  cases digits with
  | none => exact Or.inl rfl
  | some digitsString => exact Or.inr ⟨digitsString, rfl, hwf⟩

theorem components_to_surface (components : Cedar.Thm.Duration.Components)
    (hwf : ComponentsWf components) :
    Duration.IsWf.Components components.asString := by
  rcases components with ⟨days, hours, minutes, seconds, milliseconds⟩
  rcases hwf with ⟨hwfDays, hwfHours, hwfMinutes, hwfSeconds, hwfMillis⟩
  let daysChunk := Cedar.Thm.Duration.durationChunk days "d"
  let hoursChunk := Cedar.Thm.Duration.durationChunk hours "h"
  let minutesChunk := Cedar.Thm.Duration.durationChunk minutes "m"
  let secondsChunk := Cedar.Thm.Duration.durationChunk seconds "s"
  let millisChunk := Cedar.Thm.Duration.durationChunk milliseconds "ms"
  have hdays : daysChunk = "" ∨ Duration.IsWf.Days daysChunk := by
    simpa [daysChunk, Duration.IsWf.Days, Duration.IsWf.DDays] using
      optional_chunk_surface days "d" hwfDays
  have hhours : hoursChunk = "" ∨ Duration.IsWf.Hours hoursChunk := by
    simpa [hoursChunk, Duration.IsWf.Hours, Duration.IsWf.DHours] using
      optional_chunk_surface hours "h" hwfHours
  have hminutes : minutesChunk = "" ∨ Duration.IsWf.Minutes minutesChunk := by
    simpa [minutesChunk, Duration.IsWf.Minutes, Duration.IsWf.DMinutes] using
      optional_chunk_surface minutes "m" hwfMinutes
  have hseconds : secondsChunk = "" ∨ Duration.IsWf.Seconds secondsChunk := by
    simpa [secondsChunk, Duration.IsWf.Seconds, Duration.IsWf.DSeconds] using
      optional_chunk_surface seconds "s" hwfSeconds
  have hmillis : millisChunk = "" ∨ Duration.IsWf.Millis millisChunk := by
    simpa [millisChunk, Duration.IsWf.Millis, Duration.IsWf.DMillis] using
      optional_chunk_surface milliseconds "ms" hwfMillis
  exact ⟨daysChunk, hoursChunk, minutesChunk, secondsChunk, millisChunk,
    ⟨⟨⟨⟨⟨by
      simp [daysChunk, hoursChunk, minutesChunk, secondsChunk, millisChunk,
        Cedar.Thm.Duration.Components.asString], hdays⟩, hhours⟩, hminutes⟩,
      hseconds⟩, hmillis⟩⟩

theorem cedar_wf_to_surface {s : String} (h : Cedar.Thm.Duration.IsWfDuration s) :
    Duration.IsWf.Duration s := by
  rcases h with hbody | ⟨body, hs, hbody⟩
  · obtain ⟨components, _, hwf, rfl⟩ := hbody
    refine ⟨"", components.asString, ⟨⟨by simp, Or.inr rfl⟩, ?_⟩⟩
    exact components_to_surface components ((components_wf_iff components).mpr hwf)
  · obtain ⟨components, _, hwf, hbody⟩ := hbody
    refine ⟨"-", body, ⟨⟨hs, Or.inl rfl⟩, ?_⟩⟩
    rw [hbody]
    exact components_to_surface components ((components_wf_iff components).mpr hwf)

theorem decode_parts_of_surface_wf {s : String} (h : Duration.IsWf.Duration s) :
    ∃ sgn components,
      decode Duration.grammar s =
        some
          ([("Sign", sgn), ("Components", components.asString)] ++
            componentsCaptures components) ∧
      (sgn = "-" ∨ sgn = "") ∧
      s = sgn ++ components.asString ∧
      ComponentsWf components := by
  have hwf : IsWf Duration.grammar s := (Duration.IsWf_equiv s).mpr h
  have hsome : (decode Duration.grammar s).isSome = true :=
    (decodeSome_iff_IsWf Duration.grammar (by decide) s).mpr hwf
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨sgn, components, hsgn, rfl, hs, hwf⟩ := decode_duration_sound hm
  exact ⟨sgn, components, hm, hsgn, hs, hwf⟩

theorem wf_body_ne_empty {body : String} (h : Cedar.Thm.Duration.IsWfBody body) :
    body ≠ "" := by
  rintro rfl
  obtain ⟨components, hnonempty, _, hcomponents⟩ := h
  exact (components_nonempty_iff components).mpr hnonempty hcomponents.symm

theorem not_wf_duration_empty : ¬ Cedar.Thm.Duration.IsWfDuration "" := by
  rintro (hbody | ⟨body, hs, _⟩)
  · exact wf_body_ne_empty hbody rfl
  · simp at hs

theorem not_wf_duration_dash : ¬ Cedar.Thm.Duration.IsWfDuration "-" := by
  rintro (hbody | ⟨body, hs, hbody⟩)
  · exact isWfBody_front_ne_dash "-" hbody (by decide)
  · have hlist := congrArg String.toList hs
    have : body = "" := by
      apply String.toList_inj.mp
      simpa [String.toList_append] using hlist
    subst body
    exact wf_body_ne_empty hbody rfl

theorem components_nonempty_of_cedar {s sgn : String}
    (components : Cedar.Thm.Duration.Components)
    (hcedar : Cedar.Thm.Duration.IsWfDuration s)
    (hs : s = sgn ++ components.asString)
    (hsgn : sgn = "-" ∨ sgn = "") :
    components.nonempty := by
  by_contra hnonempty
  have hempty : components.asString = "" := by
    by_contra hne
    exact hnonempty ((components_nonempty_iff components).mp hne)
  rcases hsgn with rfl | rfl
  · have hs' : s = "-" := by simpa [hempty] using hs
    rw [hs'] at hcedar
    exact not_wf_duration_dash hcedar
  · have hs' : s = "" := by simpa [hempty] using hs
    rw [hs'] at hcedar
    exact not_wf_duration_empty hcedar

theorem parts_to_cedar {s sgn : String}
    (components : Cedar.Thm.Duration.Components)
    (hs : s = sgn ++ components.asString)
    (hsgn : sgn = "-" ∨ sgn = "")
    (hwf : ComponentsWf components)
    (hnonempty : components.nonempty) :
    Cedar.Thm.Duration.IsWfDuration s := by
  have hbody : Cedar.Thm.Duration.IsWfBody components.asString :=
    ⟨components, hnonempty, (components_wf_iff components).mp hwf, rfl⟩
  rcases hsgn with rfl | rfl
  · exact Or.inr ⟨components.asString, hs, hbody⟩
  · have hs' : s = components.asString := by simpa using hs
    rw [hs']
    exact Or.inl hbody

def formatQuantity : Option String → Int
  | none => 0
  | some digits => Triptych.natOf digits

def formatValue (sgn : String) (components : Cedar.Thm.Duration.Components) : Int :=
  Triptych.signOf sgn *
    (formatQuantity components.days * 86400000 +
      formatQuantity components.hours * 3600000 +
      formatQuantity components.minutes * 60000 +
      formatQuantity components.seconds * 1000 +
      formatQuantity components.milliseconds)

theorem format_compute_of_decode (s sgn : String)
    (components : Cedar.Thm.Duration.Components)
    (h :
      decode Duration.grammar s =
        some
          ([("Sign", sgn), ("Components", components.asString)] ++
            componentsCaptures components)) :
    Duration.computeValue s = some (formatValue sgn components) := by
  rcases components with ⟨days, hours, minutes, seconds, milliseconds⟩
  rcases days with _ | days <;> rcases hours with _ | hours <;>
    rcases minutes with _ | minutes <;> rcases seconds with _ | seconds <;>
    rcases milliseconds with _ | milliseconds <;>
    simp [Duration.computeValue, Triptych.computeValue, h, Duration.valueExpr,
      formatValue, formatQuantity, componentsCaptures, unitCaptures, ValExpr.eval,
      CaptureMap.toEnv, Triptych.Env.signVal, Triptych.Env.natVal,
      Triptych.signOf, Triptych.natOf]

theorem quantityNat_eq_formatQuantity (digits : Option String)
    (hwf : OptionalDigitsWf digits) :
    (quantityNat digits : Int) = formatQuantity digits := by
  cases digits with
  | none => simp [quantityNat, formatQuantity]
  | some digits =>
      have hcedar : _root_.IsDigits digits := (digits_iff digits).mp hwf
      rw [quantityNat, readNat_eq digits hcedar]
      simp [formatQuantity, Triptych.natOf]

theorem cedar_body_value (components : Cedar.Thm.Duration.Components)
    (hwf : ComponentsWf components) :
    Cedar.Thm.Duration.computeBodyValue components.asString =
      some (formatValue "" components) := by
  have hcedarWf : components.quantitiesWf := (components_wf_iff components).mp hwf
  rw [computeBodyValue_components components hcedarWf]
  rcases components with ⟨days, hours, minutes, seconds, milliseconds⟩
  simp only [ComponentsWf] at hwf
  rcases hwf with ⟨hdays, hhours, hminutes, hseconds, hmilliseconds⟩
  rw [quantityNat_eq_formatQuantity days hdays,
    quantityNat_eq_formatQuantity hours hhours,
    quantityNat_eq_formatQuantity minutes hminutes,
    quantityNat_eq_formatQuantity seconds hseconds,
    quantityNat_eq_formatQuantity milliseconds hmilliseconds]
  simp [formatValue, Triptych.signOf, Cedar.Spec.Ext.Datetime.MILLISECONDS_PER_DAY,
    Cedar.Spec.Ext.Datetime.MILLISECONDS_PER_HOUR,
    Cedar.Spec.Ext.Datetime.MILLISECONDS_PER_MINUTE,
    Cedar.Spec.Ext.Datetime.MILLISECONDS_PER_SECOND]

theorem cedar_compute_of_parts (s sgn : String)
    (components : Cedar.Thm.Duration.Components)
    (hs : s = sgn ++ components.asString)
    (hsgn : sgn = "-" ∨ sgn = "")
    (hwf : ComponentsWf components)
    (hnonempty : components.nonempty) :
    Cedar.Thm.Duration.computeValue s = some (formatValue sgn components) := by
  have hbody : Cedar.Thm.Duration.IsWfBody components.asString :=
    ⟨components, hnonempty, (components_wf_iff components).mp hwf, rfl⟩
  rcases hsgn with rfl | rfl
  · rw [hs, computeValue_neg_body, Cedar.Thm.Duration.computeSignedBodyValue,
      cedar_body_value components hwf]
    simp [formatValue, Triptych.signOf]
  · have hs' : s = components.asString := by simpa using hs
    rw [hs', computeValue_pos_body components.asString
      (isWfBody_front_ne_dash components.asString hbody),
      Cedar.Thm.Duration.computeSignedBodyValue, cedar_body_value components hwf]
    simp

theorem constraints_of_decode (s sgn : String)
    (components : Cedar.Thm.Duration.Components)
    (h :
      decode Duration.grammar s =
        some
          ([("Sign", sgn), ("Components", components.asString)] ++
            componentsCaptures components)) :
    Duration.SatisfiesConstraints s ↔
      components.asString ≠ "" ∧
        (-9223372036854775808 : Int) ≤ formatValue sgn components ∧
        formatValue sgn components ≤ (9223372036854775807 : Int) := by
  unfold Duration.SatisfiesConstraints Duration.Constraints
  unfold Triptych.component Triptych.envOf
  rw [h]
  rcases components with ⟨days, hours, minutes, seconds, milliseconds⟩
  rcases days with _ | days <;> rcases hours with _ | hours <;>
    rcases minutes with _ | minutes <;> rcases seconds with _ | seconds <;>
    rcases milliseconds with _ | milliseconds <;>
    simp [formatValue, formatQuantity, componentsCaptures, unitCaptures,
      CaptureMap.toEnv, Duration.value, Triptych.signOf, Triptych.natOf,
      Triptych.readNat, Cedar.Thm.Duration.Components.asString,
      Cedar.Thm.Duration.durationChunk]

theorem bridge_value (s : String) (hcedar : Cedar.Thm.Duration.IsWfDuration s) :
    Duration.computeValue s = Cedar.Thm.Duration.computeValue s := by
  have hsurface := cedar_wf_to_surface hcedar
  obtain ⟨sgn, components, hdecode, hsgn, hs, hwf⟩ :=
    decode_parts_of_surface_wf hsurface
  have hnonempty := components_nonempty_of_cedar components hcedar hs hsgn
  rw [format_compute_of_decode s sgn components hdecode,
    cedar_compute_of_parts s sgn components hs hsgn hwf hnonempty]

theorem bridge_isValid (s : String) :
    Duration.IsValid s ↔
      Cedar.Thm.Duration.IsWfDuration s ∧
        ∃ v,
          Cedar.Thm.Duration.computeValue s = some v ∧
            (-9223372036854775808 : Int) ≤ v ∧
            v ≤ (9223372036854775807 : Int) := by
  constructor
  · rintro ⟨hsurface, hconstraints⟩
    obtain ⟨sgn, components, hdecode, hsgn, hs, hwf⟩ :=
      decode_parts_of_surface_wf hsurface
    obtain ⟨hne, hlo, hhi⟩ :=
      (constraints_of_decode s sgn components hdecode).mp hconstraints
    have hnonempty : components.nonempty :=
      (components_nonempty_iff components).mp hne
    have hcedar := parts_to_cedar components hs hsgn hwf hnonempty
    exact ⟨hcedar, formatValue sgn components,
      cedar_compute_of_parts s sgn components hs hsgn hwf hnonempty, hlo, hhi⟩
  · rintro ⟨hcedar, v, hvalue, hlo, hhi⟩
    have hsurface := cedar_wf_to_surface hcedar
    obtain ⟨sgn, components, hdecode, hsgn, hs, hwf⟩ :=
      decode_parts_of_surface_wf hsurface
    have hnonempty := components_nonempty_of_cedar components hcedar hs hsgn
    have hparts :=
      cedar_compute_of_parts s sgn components hs hsgn hwf hnonempty
    have heq : formatValue sgn components = v := by
      rw [hparts] at hvalue
      exact Option.some.inj hvalue
    refine ⟨hsurface, (constraints_of_decode s sgn components hdecode).mpr ?_⟩
    exact ⟨(components_nonempty_iff components).mpr hnonempty, by
      simpa [heq] using And.intro hlo hhi⟩

end Duration.CedarBridge
