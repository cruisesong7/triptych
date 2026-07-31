import Datetime.CedarBridge
import Triptych.Theorems.DecodeLemmas

/-! Exact structural reconstruction for Datetime's generated decoded view. -/

open Triptych
open CedarExamples.Datetime

namespace Datetime.CedarBridge

def dateCaptures (date : Cedar.Thm.Datetime.DateComponents) : CaptureMap :=
  [("Date", date.asString),
    ("YYYY", date.year), ("Date.YYYY", date.year),
    ("MM", date.month), ("Date.MM", date.month),
    ("DD", date.day), ("Date.DD", date.day)]

def timeCaptures (time : Cedar.Thm.Datetime.TimeComponents) : CaptureMap :=
  [("Time", time.asString),
    ("hh", time.hours), ("Time.hh", time.hours),
    ("mm", time.minutes), ("Time.mm", time.minutes),
    ("ss", time.seconds), ("Time.ss", time.seconds)]

def offsetCaptures (offset : Cedar.Thm.Datetime.OffsetComponents) : CaptureMap :=
  [("Offset", offset.asString),
    ("hh", offset.hours), ("Offset.hh", offset.hours),
    ("mm", offset.minutes), ("Offset.mm", offset.minutes)]

def componentsCaptures (components : Cedar.Thm.Datetime.DatetimeComponents) : CaptureMap :=
  dateCaptures components.date ++
    match components.time with
    | none => []
    | some timePart =>
        timeCaptures timePart.time ++
          (match timePart.millis with
          | none => []
          | some millis => [("SSS", millis)]) ++
          match timePart.zone with
          | .utc => []
          | .offset offset => offsetCaptures offset

theorem fixedField_mem (fuel : Nat) (qual name : String) (width : Nat)
    (hprod :
      Datetime.grammar.prod? name =
        some
          (Production.mk name
            [[SymItem.mk (Sym.term TokClass.digit (LenSpec.exactly width)) false]]))
    (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym Datetime.grammar qual (fuel + 1) (Sym.ref name) cs ↔
      ∃ field,
        m =
          (if qual.isEmpty then
            [(name, field)]
          else
            [(name, field), (qual ++ "." ++ name, field)]) ∧
        cs = field.toList ++ r ∧ Triptych.IsFixedDigits width field := by
  rw [mem_matchSym_ref_single_term_qualified_iff Datetime.grammar qual fuel
    name name TokClass.digit (LenSpec.exactly width) hprod]
  constructor
  · rintro ⟨p, rfl, hcs, hwf⟩
    exact ⟨String.ofList p, rfl, by simpa using hcs,
      by simpa [IsFixedDigits_matchesTerm] using hwf⟩
  · rintro ⟨field, rfl, hcs, hwf⟩
    exact ⟨field.toList, by simp, by simpa using hcs,
      by simpa [IsFixedDigits_matchesTerm] using hwf⟩

theorem date_mem (fuel : Nat) (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym Datetime.grammar "" (fuel + 2) (Sym.ref "Date") cs ↔
      ∃ date : Cedar.Thm.Datetime.DateComponents,
        m = dateCaptures date ∧
        cs = date.asString.toList ++ r ∧
        date.syntaxWf := by
  rw [mem_matchSym_ref_iff Datetime.grammar "" (fuel + 1) "Date" _ rfl]
  constructor
  · rintro ⟨inner, hinner, rfl⟩
    rw [matchProd] at hinner
    simp only [List.mem_flatMap, List.mem_singleton, exists_eq_left] at hinner
    obtain ⟨my, ry, mt₁, hy, ht₁, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Date" (fuel + 1)
        (Sym.ref "YYYY") _ cs r inner).mp hinner
    obtain ⟨mdash₁, rdash₁, mt₂, hdash₁, ht₂, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Date" (fuel + 1)
        (Sym.lit "-") _ ry r mt₁).mp ht₁
    obtain ⟨mm, rm, mt₃, hm, ht₃, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Date" (fuel + 1)
        (Sym.ref "MM") _ rdash₁ r mt₂).mp ht₂
    obtain ⟨mdash₂, rdash₂, mt₄, hdash₂, ht₄, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Date" (fuel + 1)
        (Sym.lit "-") _ rm r mt₃).mp ht₃
    obtain ⟨md, rd, mnil, hd, hnil, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Date" (fuel + 1)
        (Sym.ref "DD") _ rdash₂ r mt₄).mp ht₄
    simp only [matchSeq, List.mem_singleton, Prod.mk.injEq] at hnil
    obtain ⟨rfl, rfl⟩ := hnil
    obtain ⟨year, rfl, hycs, hywf⟩ :=
      (fixedField_mem fuel "Date" "YYYY" 4 rfl _ _ _).mp hy
    obtain ⟨rfl, hdash₁cs⟩ :=
      (mem_matchSym_lit_iff Datetime.grammar "Date" (fuel + 1) "-" _ _ _).mp hdash₁
    obtain ⟨month, rfl, hmcs, hmwf⟩ :=
      (fixedField_mem fuel "Date" "MM" 2 rfl _ _ _).mp hm
    obtain ⟨rfl, hdash₂cs⟩ :=
      (mem_matchSym_lit_iff Datetime.grammar "Date" (fuel + 1) "-" _ _ _).mp hdash₂
    obtain ⟨day, rfl, hdcs, hdwf⟩ :=
      (fixedField_mem fuel "Date" "DD" 2 rfl _ _ _).mp hd
    let date : Cedar.Thm.Datetime.DateComponents := ⟨year, month, day⟩
    have hparts : cs = date.asString.toList ++ r := by
      simp [date, Cedar.Thm.Datetime.DateComponents.asString, hycs, hdash₁cs,
        hmcs, hdash₂cs, hdcs, String.toList_append, List.append_assoc]
    have hconsumed :
        String.ofList (cs.take (cs.length - r.length)) = date.asString := by
      simpa only [String.ofList_toList] using consumed_eq_of_append hparts
    exact ⟨date, by simp [dateCaptures, hconsumed, date], hparts,
      by exact ⟨(fixedDigits_iff 4 (by omega) year).mp hywf,
        (fixedDigits_iff 2 (by omega) month).mp hmwf,
        (fixedDigits_iff 2 (by omega) day).mp hdwf⟩⟩
  · rintro ⟨⟨year, month, day⟩, rfl, hcs, hywf, hmwf, hdwf⟩
    let date : Cedar.Thm.Datetime.DateComponents := ⟨year, month, day⟩
    have hparts : cs = date.asString.toList ++ r := by simpa [date] using hcs
    have hycs :
        cs = year.toList ++
          ("-" ++ month ++ "-" ++ day).toList ++ r := by
      simpa [date, Cedar.Thm.Datetime.DateComponents.asString, String.toList_append,
        List.append_assoc] using hparts
    have hconsumed :
        String.ofList (cs.take (cs.length - r.length)) =
          (Cedar.Thm.Datetime.DateComponents.mk year month day).asString := by
      simpa only [String.ofList_toList] using consumed_eq_of_append hparts
    refine ⟨[("YYYY", year), ("Date.YYYY", year),
      ("MM", month), ("Date.MM", month),
      ("DD", day), ("Date.DD", day)], ?_, ?_⟩
    · rw [matchProd]
      simp only [List.mem_flatMap, List.mem_singleton, exists_eq_left]
      refine (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Date" (fuel + 1)
        (Sym.ref "YYYY") _ cs r _).mpr ?_
      refine ⟨[("YYYY", year), ("Date.YYYY", year)],
        ("-" ++ month ++ "-" ++ day).toList ++ r, _, ?_, ?_, rfl⟩
      · exact (fixedField_mem fuel "Date" "YYYY" 4 rfl _ _ _).mpr
          ⟨year, rfl, by simpa [List.append_assoc] using hycs,
            (fixedDigits_iff 4 (by omega) year).mpr hywf⟩
      · refine (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Date" (fuel + 1)
          (Sym.lit "-") _ _ r _).mpr ?_
        refine ⟨[], (month ++ "-" ++ day).toList ++ r, _, ?_, ?_, rfl⟩
        · exact (mem_matchSym_lit_iff Datetime.grammar "Date" (fuel + 1) "-" _ _ _).mpr
            ⟨rfl, by simp [String.toList_append, List.append_assoc]⟩
        · refine (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Date" (fuel + 1)
            (Sym.ref "MM") _ _ r _).mpr ?_
          refine ⟨[("MM", month), ("Date.MM", month)],
            ("-" ++ day).toList ++ r, _, ?_, ?_, rfl⟩
          · exact (fixedField_mem fuel "Date" "MM" 2 rfl _ _ _).mpr
              ⟨month, rfl, by simp [String.toList_append, List.append_assoc],
                (fixedDigits_iff 2 (by omega) month).mpr hmwf⟩
          · refine (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Date" (fuel + 1)
              (Sym.lit "-") _ _ r _).mpr ?_
            refine ⟨[], day.toList ++ r, _, ?_, ?_, rfl⟩
            · exact (mem_matchSym_lit_iff Datetime.grammar "Date" (fuel + 1) "-" _ _ _).mpr
                ⟨rfl, by simp [String.toList_append]⟩
            · refine (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Date" (fuel + 1)
                (Sym.ref "DD") _ _ r _).mpr ?_
              refine ⟨[("DD", day), ("Date.DD", day)], r, [], ?_, ?_, by simp⟩
              · exact (fixedField_mem fuel "Date" "DD" 2 rfl _ _ _).mpr
                  ⟨day, rfl, rfl, (fixedDigits_iff 2 (by omega) day).mpr hdwf⟩
              · simp [matchSeq]
    · simp [dateCaptures, hconsumed]

theorem time_of_mem (fuel : Nat) (cs r : List Char) (m : CaptureMap)
    (h : (m, r) ∈
      matchSym Datetime.grammar "" (fuel + 2) (Sym.ref "Time") cs) :
    ∃ time : Cedar.Thm.Datetime.TimeComponents,
      m = timeCaptures time ∧
      cs = time.asString.toList ++ r ∧
      time.syntaxWf := by
  rw [mem_matchSym_ref_iff Datetime.grammar "" (fuel + 1) "Time" _ rfl] at h
  obtain ⟨inner, hinner, rfl⟩ := h
  rw [matchProd] at hinner
  simp only [List.mem_flatMap, List.mem_singleton, exists_eq_left] at hinner
  obtain ⟨mh, rh, mt₁, hh, ht₁, rfl⟩ :=
    (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Time" (fuel + 1)
      (Sym.ref "hh") _ cs r inner).mp hinner
  obtain ⟨mcolon₁, rcolon₁, mt₂, hcolon₁, ht₂, rfl⟩ :=
    (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Time" (fuel + 1)
      (Sym.lit ":") _ rh r mt₁).mp ht₁
  obtain ⟨mm, rm, mt₃, hm, ht₃, rfl⟩ :=
    (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Time" (fuel + 1)
      (Sym.ref "mm") _ rcolon₁ r mt₂).mp ht₂
  obtain ⟨mcolon₂, rcolon₂, mt₄, hcolon₂, ht₄, rfl⟩ :=
    (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Time" (fuel + 1)
      (Sym.lit ":") _ rm r mt₃).mp ht₃
  obtain ⟨ms, rs, mnil, hs, hnil, rfl⟩ :=
    (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Time" (fuel + 1)
      (Sym.ref "ss") _ rcolon₂ r mt₄).mp ht₄
  simp only [matchSeq, List.mem_singleton, Prod.mk.injEq] at hnil
  obtain ⟨rfl, rfl⟩ := hnil
  obtain ⟨hours, rfl, hhcs, hhwf⟩ :=
    (fixedField_mem fuel "Time" "hh" 2 rfl _ _ _).mp hh
  obtain ⟨rfl, hcolon₁cs⟩ :=
    (mem_matchSym_lit_iff Datetime.grammar "Time" (fuel + 1) ":" _ _ _).mp hcolon₁
  obtain ⟨minutes, rfl, hmcs, hmwf⟩ :=
    (fixedField_mem fuel "Time" "mm" 2 rfl _ _ _).mp hm
  obtain ⟨rfl, hcolon₂cs⟩ :=
    (mem_matchSym_lit_iff Datetime.grammar "Time" (fuel + 1) ":" _ _ _).mp hcolon₂
  obtain ⟨seconds, rfl, hscs, hswf⟩ :=
    (fixedField_mem fuel "Time" "ss" 2 rfl _ _ _).mp hs
  let time : Cedar.Thm.Datetime.TimeComponents := ⟨hours, minutes, seconds⟩
  have hparts : cs = time.asString.toList ++ r := by
    simp [time, Cedar.Thm.Datetime.TimeComponents.asString, hhcs, hcolon₁cs,
      hmcs, hcolon₂cs, hscs, String.toList_append, List.append_assoc]
  have hconsumed :
      String.ofList (cs.take (cs.length - r.length)) = time.asString := by
    simpa only [String.ofList_toList] using consumed_eq_of_append hparts
  exact ⟨time, by simp [timeCaptures, hconsumed, time], hparts,
    ⟨(fixedDigits_iff 2 (by omega) hours).mp hhwf,
      (fixedDigits_iff 2 (by omega) minutes).mp hmwf,
      (fixedDigits_iff 2 (by omega) seconds).mp hswf⟩⟩

theorem offset_of_mem (fuel : Nat) (cs r : List Char) (m : CaptureMap)
    (h : (m, r) ∈
      matchSym Datetime.grammar "" (fuel + 2) (Sym.ref "Offset") cs) :
    ∃ offset : Cedar.Thm.Datetime.OffsetComponents,
      m = offsetCaptures offset ∧
      cs = offset.asString.toList ++ r ∧
      offset.syntaxWf := by
  rw [mem_matchSym_ref_iff Datetime.grammar "" (fuel + 1) "Offset" _ rfl] at h
  obtain ⟨inner, hinner, rfl⟩ := h
  rw [matchProd] at hinner
  simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left] at hinner
  rcases hinner with hplus | hminus
  ·
    obtain ⟨msign, rsign, mt₁, hsign, ht₁, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Offset" (fuel + 1)
        _ _ cs r inner).mp hplus
    obtain ⟨mh, rh, mt₂, hh, ht₂, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Offset" (fuel + 1)
        (Sym.ref "hh") _ rsign r mt₁).mp ht₁
    obtain ⟨mm, rm, mnil, hm, hnil, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Offset" (fuel + 1)
        (Sym.ref "mm") _ rh r mt₂).mp ht₂
    simp only [matchSeq, List.mem_singleton, Prod.mk.injEq] at hnil
    obtain ⟨rfl, rfl⟩ := hnil
    obtain ⟨hours, rfl, hhcs, hhwf⟩ :=
      (fixedField_mem fuel "Offset" "hh" 2 rfl _ _ _).mp hh
    obtain ⟨minutes, rfl, hmcs, hmwf⟩ :=
      (fixedField_mem fuel "Offset" "mm" 2 rfl _ _ _).mp hm
    obtain ⟨rfl, hsigncs⟩ :=
      (mem_matchSym_lit_iff Datetime.grammar "Offset" (fuel + 1) "+" _ _ _).mp hsign
    let offset : Cedar.Thm.Datetime.OffsetComponents := ⟨false, hours, minutes⟩
    have hparts : cs = offset.asString.toList ++ r := by
      simp [offset, Cedar.Thm.Datetime.OffsetComponents.asString, hsigncs,
        hhcs, hmcs, String.toList_append, List.append_assoc]
    have hconsumed :
        String.ofList (cs.take (cs.length - r.length)) = offset.asString := by
      simpa only [String.ofList_toList] using consumed_eq_of_append hparts
    exact ⟨offset, by simp [offsetCaptures, hconsumed, offset], hparts,
      ⟨(fixedDigits_iff 2 (by omega) hours).mp hhwf,
        (fixedDigits_iff 2 (by omega) minutes).mp hmwf⟩⟩
  ·
    obtain ⟨msign, rsign, mt₁, hsign, ht₁, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Offset" (fuel + 1)
        _ _ cs r inner).mp hminus
    obtain ⟨mh, rh, mt₂, hh, ht₂, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Offset" (fuel + 1)
        (Sym.ref "hh") _ rsign r mt₁).mp ht₁
    obtain ⟨mm, rm, mnil, hm, hnil, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar "Offset" (fuel + 1)
        (Sym.ref "mm") _ rh r mt₂).mp ht₂
    simp only [matchSeq, List.mem_singleton, Prod.mk.injEq] at hnil
    obtain ⟨rfl, rfl⟩ := hnil
    obtain ⟨hours, rfl, hhcs, hhwf⟩ :=
      (fixedField_mem fuel "Offset" "hh" 2 rfl _ _ _).mp hh
    obtain ⟨minutes, rfl, hmcs, hmwf⟩ :=
      (fixedField_mem fuel "Offset" "mm" 2 rfl _ _ _).mp hm
    obtain ⟨rfl, hsigncs⟩ :=
      (mem_matchSym_lit_iff Datetime.grammar "Offset" (fuel + 1) "-" _ _ _).mp hsign
    let offset : Cedar.Thm.Datetime.OffsetComponents := ⟨true, hours, minutes⟩
    have hparts : cs = offset.asString.toList ++ r := by
      simp [offset, Cedar.Thm.Datetime.OffsetComponents.asString, hsigncs,
        hhcs, hmcs, String.toList_append, List.append_assoc]
    have hconsumed :
        String.ofList (cs.take (cs.length - r.length)) = offset.asString := by
      simpa only [String.ofList_toList] using consumed_eq_of_append hparts
    exact ⟨offset, by simp [offsetCaptures, hconsumed, offset], hparts,
      ⟨(fixedDigits_iff 2 (by omega) hours).mp hhwf,
        (fixedDigits_iff 2 (by omega) minutes).mp hmwf⟩⟩

end Datetime.CedarBridge
