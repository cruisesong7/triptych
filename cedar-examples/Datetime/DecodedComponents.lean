import Datetime.StructuralView

open Triptych
open CedarExamples.Datetime

namespace Datetime.GrammarView

theorem components_of_decode {s : String} {m : CaptureMap}
    (h : decode Datetime.grammar s = some m) :
    ∃ components : Cedar.Thm.Datetime.DatetimeComponents,
      m = componentsCaptures components ∧
      s = components.asString ∧
      components.syntaxWf := by
  obtain ⟨p, hp, hmem⟩ := mem_matchProd_of_decode_eq_some h
  have hp' :
      p =
        Production.mk "Datetime"
          [[SymItem.mk (Sym.ref "Date") false],
            [SymItem.mk (Sym.ref "Date") false, SymItem.mk (Sym.lit "T") false,
              SymItem.mk (Sym.ref "Time") false, SymItem.mk (Sym.lit "Z") false],
            [SymItem.mk (Sym.ref "Date") false, SymItem.mk (Sym.lit "T") false,
              SymItem.mk (Sym.ref "Time") false, SymItem.mk (Sym.lit ".") false,
              SymItem.mk (Sym.ref "SSS") false, SymItem.mk (Sym.lit "Z") false],
            [SymItem.mk (Sym.ref "Date") false, SymItem.mk (Sym.lit "T") false,
              SymItem.mk (Sym.ref "Time") false, SymItem.mk (Sym.ref "Offset") false],
            [SymItem.mk (Sym.ref "Date") false, SymItem.mk (Sym.lit "T") false,
              SymItem.mk (Sym.ref "Time") false, SymItem.mk (Sym.lit ".") false,
              SymItem.mk (Sym.ref "SSS") false, SymItem.mk (Sym.ref "Offset") false]] := by
    rw [show Datetime.grammar.startProd? =
      some
        (Production.mk "Datetime"
          [[SymItem.mk (Sym.ref "Date") false],
            [SymItem.mk (Sym.ref "Date") false, SymItem.mk (Sym.lit "T") false,
              SymItem.mk (Sym.ref "Time") false, SymItem.mk (Sym.lit "Z") false],
            [SymItem.mk (Sym.ref "Date") false, SymItem.mk (Sym.lit "T") false,
              SymItem.mk (Sym.ref "Time") false, SymItem.mk (Sym.lit ".") false,
              SymItem.mk (Sym.ref "SSS") false, SymItem.mk (Sym.lit "Z") false],
            [SymItem.mk (Sym.ref "Date") false, SymItem.mk (Sym.lit "T") false,
              SymItem.mk (Sym.ref "Time") false, SymItem.mk (Sym.ref "Offset") false],
            [SymItem.mk (Sym.ref "Date") false, SymItem.mk (Sym.lit "T") false,
              SymItem.mk (Sym.ref "Time") false, SymItem.mk (Sym.lit ".") false,
              SymItem.mk (Sym.ref "SSS") false,
              SymItem.mk (Sym.ref "Offset") false]]) from rfl] at hp
    exact Option.some.inj hp.symm
  subst p
  rw [matchProd] at hmem
  simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    exists_eq_or_imp, exists_eq_left, or_false] at hmem
  rcases hmem with hdate | hutc | hmillisUtc | hOffsetAlt | hMillisOffsetAlt
  · obtain ⟨md, rd, mnil, hd, hnil, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.ref "Date") [] s.toList [] m).mp hdate
    simp only [mem_matchSeq_nil_iff] at hnil
    obtain ⟨rfl, rfl⟩ := hnil
    rw [show Datetime.grammar.prods.length = 11 from rfl] at hd
    obtain ⟨date, rfl, hparts, hsyn⟩ :=
      (date_mem 9 s.toList [] md).mp hd
    let components : Cedar.Thm.Datetime.DatetimeComponents := ⟨date, none⟩
    have hs : s = components.asString := by
      simpa [components, Cedar.Thm.Datetime.DatetimeComponents.asString] using
        congrArg String.ofList hparts
    exact ⟨components, by simp [components, componentsCaptures], hs, ⟨hsyn, trivial⟩⟩
  · obtain ⟨md, rd, mtail₁, hd, htail₁, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.ref "Date") _ s.toList [] m).mp hutc
    obtain ⟨mT, rT, mtail₂, hT, htail₂, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.lit "T") _ rd [] mtail₁).mp htail₁
    obtain ⟨mtime, rtime, mtail₃, htime, htail₃, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.ref "Time") _ rT [] mtail₂).mp htail₂
    obtain ⟨mZ, rZ, mnil, hZ, hnil, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.lit "Z") _ rtime [] mtail₃).mp htail₃
    simp only [mem_matchSeq_nil_iff] at hnil
    obtain ⟨rfl, rfl⟩ := hnil
    rw [show Datetime.grammar.prods.length = 11 from rfl] at hd htime
    obtain ⟨date, rfl, hdateParts, hdateSyn⟩ :=
      (date_mem 9 s.toList rd md).mp hd
    obtain ⟨rfl, hTParts⟩ :=
      (mem_matchSym_lit_iff Datetime.grammar "" 11 "T" rd rT mT).mp hT
    obtain ⟨time, rfl, htimeParts, htimeSyn⟩ :=
      time_of_mem 9 rT rtime mtime htime
    obtain ⟨rfl, hZParts⟩ :=
      (mem_matchSym_lit_iff Datetime.grammar "" 11 "Z" rtime [] mZ).mp hZ
    let timePart : Cedar.Thm.Datetime.TimePart := ⟨time, none, .utc⟩
    let components : Cedar.Thm.Datetime.DatetimeComponents := ⟨date, some timePart⟩
    have hparts : s.toList = components.asString.toList := by
      simp [components, timePart, Cedar.Thm.Datetime.DatetimeComponents.asString,
        Cedar.Thm.Datetime.TimePart.asString, Cedar.Thm.Datetime.Zone.asString,
        hdateParts, hTParts, htimeParts, hZParts, String.toList_append]
    have hs : s = components.asString := by
      simpa using congrArg String.ofList hparts
    exact ⟨components, by simp [components, timePart, componentsCaptures], hs,
      ⟨hdateSyn, htimeSyn, trivial, trivial⟩⟩
  · obtain ⟨md, rd, mtail₁, hd, htail₁, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.ref "Date") _ s.toList [] m).mp hmillisUtc
    obtain ⟨mT, rT, mtail₂, hT, htail₂, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.lit "T") _ rd [] mtail₁).mp htail₁
    obtain ⟨mtime, rtime, mtail₃, htime, htail₃, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.ref "Time") _ rT [] mtail₂).mp htail₂
    obtain ⟨mdot, rdot, mtail₄, hdot, htail₄, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.lit ".") _ rtime [] mtail₃).mp htail₃
    obtain ⟨mmillis, rmillis, mtail₅, hmillis, htail₅, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.ref "SSS") _ rdot [] mtail₄).mp htail₄
    obtain ⟨mZ, rZ, mnil, hZ, hnil, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.lit "Z") _ rmillis [] mtail₅).mp htail₅
    simp only [mem_matchSeq_nil_iff] at hnil
    obtain ⟨rfl, rfl⟩ := hnil
    rw [show Datetime.grammar.prods.length = 11 from rfl] at hd htime hmillis
    obtain ⟨date, rfl, hdateParts, hdateSyn⟩ :=
      (date_mem 9 s.toList rd md).mp hd
    obtain ⟨rfl, hTParts⟩ :=
      (mem_matchSym_lit_iff Datetime.grammar "" 11 "T" rd rT mT).mp hT
    obtain ⟨time, rfl, htimeParts, htimeSyn⟩ :=
      time_of_mem 9 rT rtime mtime htime
    obtain ⟨rfl, hdotParts⟩ :=
      (mem_matchSym_lit_iff Datetime.grammar "" 11 "." rtime rdot mdot).mp hdot
    obtain ⟨millis, rfl, hmillisParts, hmillisSyn⟩ :=
      (fixedField_mem 10 "" "SSS" 3 rfl rdot rmillis mmillis).mp hmillis
    obtain ⟨rfl, hZParts⟩ :=
      (mem_matchSym_lit_iff Datetime.grammar "" 11 "Z" rmillis [] mZ).mp hZ
    let timePart : Cedar.Thm.Datetime.TimePart := ⟨time, some millis, .utc⟩
    let components : Cedar.Thm.Datetime.DatetimeComponents := ⟨date, some timePart⟩
    have hparts : s.toList = components.asString.toList := by
      simp [components, timePart, Cedar.Thm.Datetime.DatetimeComponents.asString,
        Cedar.Thm.Datetime.TimePart.asString, Cedar.Thm.Datetime.Zone.asString,
        hdateParts, hTParts, htimeParts, hdotParts, hmillisParts, hZParts,
        String.toList_append, List.append_assoc]
    have hs : s = components.asString := by simpa using congrArg String.ofList hparts
    exact ⟨components, by simp [components, timePart, componentsCaptures], hs,
      ⟨hdateSyn, htimeSyn, (fixedDigits_iff 3 (by omega) millis).mp hmillisSyn,
        trivial⟩⟩
  · obtain ⟨md, rd, mtail₁, hd, htail₁, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.ref "Date") _ s.toList [] m).mp hOffsetAlt
    obtain ⟨mT, rT, mtail₂, hT, htail₂, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.lit "T") _ rd [] mtail₁).mp htail₁
    obtain ⟨mtime, rtime, mtail₃, htime, htail₃, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.ref "Time") _ rT [] mtail₂).mp htail₂
    obtain ⟨moffset, roffset, mnil, hoffsetMatch, hnil, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.ref "Offset") _ rtime [] mtail₃).mp htail₃
    simp only [mem_matchSeq_nil_iff] at hnil
    obtain ⟨rfl, rfl⟩ := hnil
    rw [show Datetime.grammar.prods.length = 11 from rfl] at hd htime hoffsetMatch
    obtain ⟨date, rfl, hdateParts, hdateSyn⟩ :=
      (date_mem 9 s.toList rd md).mp hd
    obtain ⟨rfl, hTParts⟩ :=
      (mem_matchSym_lit_iff Datetime.grammar "" 11 "T" rd rT mT).mp hT
    obtain ⟨time, rfl, htimeParts, htimeSyn⟩ :=
      time_of_mem 9 rT rtime mtime htime
    obtain ⟨offset, rfl, hoffsetParts, hoffsetSyn⟩ :=
      offset_of_mem 9 rtime [] moffset hoffsetMatch
    let timePart : Cedar.Thm.Datetime.TimePart := ⟨time, none, .offset offset⟩
    let components : Cedar.Thm.Datetime.DatetimeComponents := ⟨date, some timePart⟩
    have hparts : s.toList = components.asString.toList := by
      simp [components, timePart, Cedar.Thm.Datetime.DatetimeComponents.asString,
        Cedar.Thm.Datetime.TimePart.asString, Cedar.Thm.Datetime.Zone.asString,
        hdateParts, hTParts, htimeParts, hoffsetParts, String.toList_append]
    have hs : s = components.asString := by simpa using congrArg String.ofList hparts
    exact ⟨components, by simp [components, timePart, componentsCaptures], hs,
      ⟨hdateSyn, htimeSyn, trivial, hoffsetSyn⟩⟩
  · obtain ⟨md, rd, mtail₁, hd, htail₁, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.ref "Date") _ s.toList [] m).mp hMillisOffsetAlt
    obtain ⟨mT, rT, mtail₂, hT, htail₂, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.lit "T") _ rd [] mtail₁).mp htail₁
    obtain ⟨mtime, rtime, mtail₃, htime, htail₃, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.ref "Time") _ rT [] mtail₂).mp htail₂
    obtain ⟨mdot, rdot, mtail₄, hdot, htail₄, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.lit ".") _ rtime [] mtail₃).mp htail₃
    obtain ⟨mmillis, rmillis, mtail₅, hmillis, htail₅, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.ref "SSS") _ rdot [] mtail₄).mp htail₄
    obtain ⟨moffset, roffset, mnil, hoffsetMatch, hnil, rfl⟩ :=
      (mem_matchSeq_cons_mk_required_iff Datetime.grammar ""
        Datetime.grammar.prods.length (Sym.ref "Offset") _ rmillis [] mtail₅).mp htail₅
    simp only [mem_matchSeq_nil_iff] at hnil
    obtain ⟨rfl, rfl⟩ := hnil
    rw [show Datetime.grammar.prods.length = 11 from rfl] at hd htime hmillis hoffsetMatch
    obtain ⟨date, rfl, hdateParts, hdateSyn⟩ :=
      (date_mem 9 s.toList rd md).mp hd
    obtain ⟨rfl, hTParts⟩ :=
      (mem_matchSym_lit_iff Datetime.grammar "" 11 "T" rd rT mT).mp hT
    obtain ⟨time, rfl, htimeParts, htimeSyn⟩ :=
      time_of_mem 9 rT rtime mtime htime
    obtain ⟨rfl, hdotParts⟩ :=
      (mem_matchSym_lit_iff Datetime.grammar "" 11 "." rtime rdot mdot).mp hdot
    obtain ⟨millis, rfl, hmillisParts, hmillisSyn⟩ :=
      (fixedField_mem 10 "" "SSS" 3 rfl rdot rmillis mmillis).mp hmillis
    obtain ⟨offset, rfl, hoffsetParts, hoffsetSyn⟩ :=
      offset_of_mem 9 rmillis [] moffset hoffsetMatch
    let timePart : Cedar.Thm.Datetime.TimePart := ⟨time, some millis, .offset offset⟩
    let components : Cedar.Thm.Datetime.DatetimeComponents := ⟨date, some timePart⟩
    have hparts : s.toList = components.asString.toList := by
      simp [components, timePart, Cedar.Thm.Datetime.DatetimeComponents.asString,
        Cedar.Thm.Datetime.TimePart.asString, Cedar.Thm.Datetime.Zone.asString,
        hdateParts, hTParts, htimeParts, hdotParts, hmillisParts, hoffsetParts,
        String.toList_append, List.append_assoc]
    have hs : s = components.asString := by simpa using congrArg String.ofList hparts
    exact ⟨components, by simp [components, timePart, componentsCaptures], hs,
      ⟨hdateSyn, htimeSyn, (fixedDigits_iff 3 (by omega) millis).mp hmillisSyn,
        hoffsetSyn⟩⟩

theorem cedarOffset_asString (offset : Cedar.Thm.Datetime.OffsetComponents) :
    cedarOffset offset.asString offset.hours offset.minutes = offset := by
  rcases offset with ⟨negative, hours, minutes⟩
  cases negative <;>
    simp [cedarOffset, Cedar.Thm.Datetime.OffsetComponents.asString]

theorem components_of_decodeView {s : String} {v : Datetime.View}
    (h : Datetime.decodeView s = some v) :
    ∃ components : Cedar.Thm.Datetime.DatetimeComponents,
      v.toCedarComponents? = some components ∧
      v.input = components.asString ∧
      components.syntaxWf := by
  unfold Datetime.decodeView at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨m, hm, rfl⟩ := h
  obtain ⟨components, rfl, hs, hsyn⟩ := components_of_decode hm
  refine ⟨components, ?_, hs, hsyn⟩
  rcases components with ⟨date, time⟩
  rcases date with ⟨year, month, day⟩
  cases time with
  | none =>
      simp [Datetime.View.ofMap, componentsCaptures, dateCaptures,
        Datetime.View.toCedarComponents?, cedarDate, CaptureMap.toEnv]
  | some timePart =>
      rcases timePart with ⟨time, millis, zone⟩
      rcases time with ⟨hours, minutes, seconds⟩
      cases millis <;> cases zone <;>
        simp [Datetime.View.ofMap, componentsCaptures, dateCaptures, timeCaptures,
          offsetCaptures, Datetime.View.toCedarComponents?, cedarDate, cedarTime,
          cedarOffset_asString, CaptureMap.toEnv]

end Datetime.GrammarView
