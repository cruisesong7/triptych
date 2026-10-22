import TriptychVermilionGenerated.Datetime
import Proofs.Datetime.ComponentView
import Triptych.Backend.Verus.AstSemantics

namespace Triptych.Vermilion.Proofs.Datetime

open Triptych
open Triptych.Vermilion.String
open Triptych.Vermilion.Generated.Datetime
open Datetime.GrammarView

theorem yyyy_equiv (source : String) :
    Datetime.IsWf.YYYY source ↔
      triptych_datetime_roundtrip.datetime_is_wf_YYYY
        (encodeString source) := by
  simpa [Datetime.IsWf.YYYY,
    triptych_datetime_roundtrip.datetime_is_wf_YYYY,
    triptych_datetime_roundtrip.triptych_is_digit, IsDigitCode] using
      fixedDigits_iff_encoded 4 source

theorem mm_equiv (source : String) :
    Datetime.IsWf.MM source ↔
      triptych_datetime_roundtrip.datetime_is_wf_MM
        (encodeString source) := by
  simpa [Datetime.IsWf.MM,
    triptych_datetime_roundtrip.datetime_is_wf_MM,
    triptych_datetime_roundtrip.triptych_is_digit, IsDigitCode] using
      fixedDigits_iff_encoded 2 source

theorem dd_equiv (source : String) :
    Datetime.IsWf.DD source ↔
      triptych_datetime_roundtrip.datetime_is_wf_DD
        (encodeString source) := by
  simpa [Datetime.IsWf.DD,
    triptych_datetime_roundtrip.datetime_is_wf_DD,
    triptych_datetime_roundtrip.triptych_is_digit, IsDigitCode] using
      fixedDigits_iff_encoded 2 source

theorem hh_equiv (source : String) :
    Datetime.IsWf.hh source ↔
      triptych_datetime_roundtrip.datetime_is_wf_hh
        (encodeString source) := by
  simpa [Datetime.IsWf.hh,
    triptych_datetime_roundtrip.datetime_is_wf_hh,
    triptych_datetime_roundtrip.triptych_is_digit, IsDigitCode] using
      fixedDigits_iff_encoded 2 source

theorem minute_equiv (source : String) :
    Datetime.IsWf.mm source ↔
      triptych_datetime_roundtrip.datetime_is_wf_mm
        (encodeString source) := by
  simpa [Datetime.IsWf.mm,
    triptych_datetime_roundtrip.datetime_is_wf_mm,
    triptych_datetime_roundtrip.triptych_is_digit, IsDigitCode] using
      fixedDigits_iff_encoded 2 source

theorem ss_equiv (source : String) :
    Datetime.IsWf.ss source ↔
      triptych_datetime_roundtrip.datetime_is_wf_ss
        (encodeString source) := by
  simpa [Datetime.IsWf.ss,
    triptych_datetime_roundtrip.datetime_is_wf_ss,
    triptych_datetime_roundtrip.triptych_is_digit, IsDigitCode] using
      fixedDigits_iff_encoded 2 source

theorem sss_equiv (source : String) :
    Datetime.IsWf.SSS source ↔
      triptych_datetime_roundtrip.datetime_is_wf_SSS
        (encodeString source) := by
  simpa [Datetime.IsWf.SSS,
    triptych_datetime_roundtrip.datetime_is_wf_SSS,
    triptych_datetime_roundtrip.triptych_is_digit, IsDigitCode] using
      fixedDigits_iff_encoded 3 source

theorem decode_datetime_fixed_digits
    (sequence : Vermilion.Seq Int) (width : Nat)
    (hwf :
      ∃ digits : Vermilion.Seq Int,
        sequence = digits ∧
          Vermilion.Seq.len digits = Int.ofNat width ∧
          ∀ index : Int,
            0 ≤ index ∧ index < Vermilion.Seq.len digits →
              triptych_datetime_roundtrip.triptych_is_digit
                (Vermilion.Seq.index digits index)) :
    ∃ text : String,
      sequence = encodeString text ∧ IsFixedDigits width text := by
  apply Triptych.Vermilion.String.decode_fixed_digits
  simpa [triptych_datetime_roundtrip.triptych_is_digit, IsDigitCode] using hwf

theorem decode_date_wf
    (sequence : Vermilion.Seq Int)
    (hwf : triptych_datetime_roundtrip.datetime_is_wf_Date sequence) :
    ∃ yyyy mm dd : String,
      sequence = encodeString (yyyy ++ "-" ++ mm ++ "-" ++ dd) ∧
        Datetime.IsWf.YYYY yyyy ∧ Datetime.IsWf.MM mm ∧
          Datetime.IsWf.DD dd := by
  rcases hwf with
    ⟨yyyySequence, mmSequence, ddSequence,
      ⟨⟨⟨hsequence, hyyyy⟩, hmm⟩, hdd⟩⟩
  obtain ⟨yyyy, hyyyyEncode, hyyyyWf⟩ :=
    decode_datetime_fixed_digits yyyySequence 4 (by
      simpa [triptych_datetime_roundtrip.datetime_is_wf_YYYY] using hyyyy)
  obtain ⟨mm, hmmEncode, hmmWf⟩ :=
    decode_datetime_fixed_digits mmSequence 2 (by
      simpa [triptych_datetime_roundtrip.datetime_is_wf_MM] using hmm)
  obtain ⟨dd, hddEncode, hddWf⟩ :=
    decode_datetime_fixed_digits ddSequence 2 (by
      simpa [triptych_datetime_roundtrip.datetime_is_wf_DD] using hdd)
  refine ⟨yyyy, mm, dd, ?_, hyyyyWf, hmmWf, hddWf⟩
  rw [encodeString_append, encodeString_append, encodeString_append,
    encodeString_append, ← hyyyyEncode, ← hmmEncode, ← hddEncode]
  simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
    Vermilion.Seq.empty] using hsequence

theorem date_equiv (source : String) :
    Datetime.IsWf.Date source ↔
      triptych_datetime_roundtrip.datetime_is_wf_Date
        (encodeString source) := by
  constructor
  · rintro ⟨yyyy, mm, dd, ⟨⟨⟨hsource, hyyyy⟩, hmm⟩, hdd⟩⟩
    refine ⟨encodeString yyyy, encodeString mm, encodeString dd, ?_⟩
    refine ⟨⟨⟨?_, (yyyy_equiv yyyy).1 hyyyy⟩,
      (mm_equiv mm).1 hmm⟩, (dd_equiv dd).1 hdd⟩
    simpa [encodeString_append, encodeString, Vermilion.Seq.add,
      Vermilion.Seq.push, Vermilion.Seq.empty] using
        congrArg encodeString hsource
  · intro hwf
    obtain ⟨yyyy, mm, dd, hsource, hyyyy, hmm, hdd⟩ :=
      decode_date_wf (encodeString source) hwf
    exact ⟨yyyy, mm, dd,
      ⟨⟨⟨encodeString_injective hsource, hyyyy⟩, hmm⟩, hdd⟩⟩

theorem decode_time_wf
    (sequence : Vermilion.Seq Int)
    (hwf : triptych_datetime_roundtrip.datetime_is_wf_Time sequence) :
    ∃ hh mm ss : String,
      sequence = encodeString (hh ++ ":" ++ mm ++ ":" ++ ss) ∧
        Datetime.IsWf.hh hh ∧ Datetime.IsWf.mm mm ∧
          Datetime.IsWf.ss ss := by
  rcases hwf with
    ⟨hhSequence, mmSequence, ssSequence,
      ⟨⟨⟨hsequence, hhh⟩, hmm⟩, hss⟩⟩
  obtain ⟨hh, hhhEncode, hhhWf⟩ :=
    decode_datetime_fixed_digits hhSequence 2 (by
      simpa [triptych_datetime_roundtrip.datetime_is_wf_hh] using hhh)
  obtain ⟨mm, hmmEncode, hmmWf⟩ :=
    decode_datetime_fixed_digits mmSequence 2 (by
      simpa [triptych_datetime_roundtrip.datetime_is_wf_mm] using hmm)
  obtain ⟨ss, hssEncode, hssWf⟩ :=
    decode_datetime_fixed_digits ssSequence 2 (by
      simpa [triptych_datetime_roundtrip.datetime_is_wf_ss] using hss)
  refine ⟨hh, mm, ss, ?_, hhhWf, hmmWf, hssWf⟩
  rw [encodeString_append, encodeString_append, encodeString_append,
    encodeString_append, ← hhhEncode, ← hmmEncode, ← hssEncode]
  simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
    Vermilion.Seq.empty] using hsequence

theorem time_equiv (source : String) :
    Datetime.IsWf.Time source ↔
      triptych_datetime_roundtrip.datetime_is_wf_Time
        (encodeString source) := by
  constructor
  · rintro ⟨hh, mm, ss, ⟨⟨⟨hsource, hhh⟩, hmm⟩, hss⟩⟩
    refine ⟨encodeString hh, encodeString mm, encodeString ss, ?_⟩
    refine ⟨⟨⟨?_, (hh_equiv hh).1 hhh⟩,
      (minute_equiv mm).1 hmm⟩, (ss_equiv ss).1 hss⟩
    simpa [encodeString_append, encodeString, Vermilion.Seq.add,
      Vermilion.Seq.push, Vermilion.Seq.empty] using
        congrArg encodeString hsource
  · intro hwf
    obtain ⟨hh, mm, ss, hsource, hhh, hmm, hss⟩ :=
      decode_time_wf (encodeString source) hwf
    exact ⟨hh, mm, ss,
      ⟨⟨⟨encodeString_injective hsource, hhh⟩, hmm⟩, hss⟩⟩

theorem decode_offset_wf
    (sequence : Vermilion.Seq Int)
    (hwf : triptych_datetime_roundtrip.datetime_is_wf_Offset sequence) :
    ∃ offset hh mm : String,
      sequence = encodeString (offset ++ hh ++ mm) ∧
        (offset = "+" ∨ offset = "-") ∧
        Datetime.IsWf.hh hh ∧ Datetime.IsWf.mm mm := by
  rcases hwf with hpositive | hnegative
  · rcases hpositive with
      ⟨hhSequence, mmSequence, ⟨⟨hsequence, hhh⟩, hmm⟩⟩
    obtain ⟨hh, hhhEncode, hhhWf⟩ :=
      decode_datetime_fixed_digits hhSequence 2 (by
        simpa [triptych_datetime_roundtrip.datetime_is_wf_hh] using hhh)
    obtain ⟨mm, hmmEncode, hmmWf⟩ :=
      decode_datetime_fixed_digits mmSequence 2 (by
        simpa [triptych_datetime_roundtrip.datetime_is_wf_mm] using hmm)
    refine ⟨"+", hh, mm, ?_, Or.inl rfl, hhhWf, hmmWf⟩
    rw [encodeString_append, encodeString_append, ← hhhEncode, ← hmmEncode]
    simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
      Vermilion.Seq.empty] using hsequence
  · rcases hnegative with
      ⟨hhSequence, mmSequence, ⟨⟨hsequence, hhh⟩, hmm⟩⟩
    obtain ⟨hh, hhhEncode, hhhWf⟩ :=
      decode_datetime_fixed_digits hhSequence 2 (by
        simpa [triptych_datetime_roundtrip.datetime_is_wf_hh] using hhh)
    obtain ⟨mm, hmmEncode, hmmWf⟩ :=
      decode_datetime_fixed_digits mmSequence 2 (by
        simpa [triptych_datetime_roundtrip.datetime_is_wf_mm] using hmm)
    refine ⟨"-", hh, mm, ?_, Or.inr rfl, hhhWf, hmmWf⟩
    rw [encodeString_append, encodeString_append, ← hhhEncode, ← hmmEncode]
    simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
      Vermilion.Seq.empty] using hsequence

theorem offset_equiv (source : String) :
    Datetime.IsWf.Offset source ↔
      triptych_datetime_roundtrip.datetime_is_wf_Offset
        (encodeString source) := by
  constructor
  · rintro (⟨hh, mm, ⟨hsource, hhh⟩, hmm⟩ |
      ⟨hh, mm, ⟨hsource, hhh⟩, hmm⟩)
    · left
      refine ⟨encodeString hh, encodeString mm,
        ⟨⟨?_, (hh_equiv hh).1 hhh⟩, (minute_equiv mm).1 hmm⟩⟩
      simpa [encodeString_append, encodeString, Vermilion.Seq.add,
        Vermilion.Seq.push, Vermilion.Seq.empty] using
          congrArg encodeString hsource
    · right
      refine ⟨encodeString hh, encodeString mm,
        ⟨⟨?_, (hh_equiv hh).1 hhh⟩, (minute_equiv mm).1 hmm⟩⟩
      simpa [encodeString_append, encodeString, Vermilion.Seq.add,
        Vermilion.Seq.push, Vermilion.Seq.empty] using
          congrArg encodeString hsource
  · intro hwf
    obtain ⟨offset, hh, mm, hsource, hoffset, hhh, hmm⟩ :=
      decode_offset_wf (encodeString source) hwf
    rcases hoffset with rfl | rfl
    · exact Or.inl ⟨hh, mm,
        ⟨encodeString_injective hsource, hhh⟩, hmm⟩
    · exact Or.inr ⟨hh, mm,
        ⟨encodeString_injective hsource, hhh⟩, hmm⟩

theorem decode_date_text
    (sequence : Vermilion.Seq Int)
    (hwf : triptych_datetime_roundtrip.datetime_is_wf_Date sequence) :
    ∃ date : String,
      sequence = encodeString date ∧ Datetime.IsWf.Date date := by
  obtain ⟨yyyy, mm, dd, hsequence, hyyyy, hmm, hdd⟩ :=
    decode_date_wf sequence hwf
  exact ⟨yyyy ++ "-" ++ mm ++ "-" ++ dd, hsequence,
    ⟨yyyy, mm, dd, ⟨⟨⟨rfl, hyyyy⟩, hmm⟩, hdd⟩⟩⟩

theorem decode_time_text
    (sequence : Vermilion.Seq Int)
    (hwf : triptych_datetime_roundtrip.datetime_is_wf_Time sequence) :
    ∃ time : String,
      sequence = encodeString time ∧ Datetime.IsWf.Time time := by
  obtain ⟨hh, mm, ss, hsequence, hhh, hmm, hss⟩ :=
    decode_time_wf sequence hwf
  exact ⟨hh ++ ":" ++ mm ++ ":" ++ ss, hsequence,
    ⟨hh, mm, ss, ⟨⟨⟨rfl, hhh⟩, hmm⟩, hss⟩⟩⟩

theorem decode_offset_text
    (sequence : Vermilion.Seq Int)
    (hwf : triptych_datetime_roundtrip.datetime_is_wf_Offset sequence) :
    ∃ offset : String,
      sequence = encodeString offset ∧ Datetime.IsWf.Offset offset := by
  obtain ⟨signText, hh, mm, hsequence, hsign, hhh, hmm⟩ :=
    decode_offset_wf sequence hwf
  rcases hsign with rfl | rfl
  · exact ⟨"+" ++ hh ++ mm, hsequence,
      Or.inl ⟨hh, mm, ⟨rfl, hhh⟩, hmm⟩⟩
  · exact ⟨"-" ++ hh ++ mm, hsequence,
      Or.inr ⟨hh, mm, ⟨rfl, hhh⟩, hmm⟩⟩

theorem decode_sss_text
    (sequence : Vermilion.Seq Int)
    (hwf : triptych_datetime_roundtrip.datetime_is_wf_SSS sequence) :
    ∃ sss : String,
      sequence = encodeString sss ∧ Datetime.IsWf.SSS sss := by
  exact decode_datetime_fixed_digits sequence 3 (by
    simpa [triptych_datetime_roundtrip.datetime_is_wf_SSS] using hwf)

theorem datetime_equiv (source : String) :
    Datetime.IsWf.Datetime source ↔
      triptych_datetime_roundtrip.datetime_is_wf_Datetime
        (encodeString source) := by
  unfold Datetime.IsWf.Datetime Datetime.Production
    triptych_datetime_roundtrip.datetime_is_wf_Datetime
  constructor
  · rintro ((((hdate |
      ⟨date, time, ⟨hsource, hdate⟩, htime⟩) |
      ⟨date, time, sss, ⟨⟨hsource, hdate⟩, htime⟩, hsss⟩) |
      ⟨date, time, offset, ⟨⟨hsource, hdate⟩, htime⟩, hoffset⟩) |
      ⟨date, time, sss, offset,
        ⟨⟨⟨hsource, hdate⟩, htime⟩, hsss⟩, hoffset⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl
        ⟨encodeString source, rfl, (date_equiv source).1 hdate⟩)))
    · refine Or.inl (Or.inl (Or.inl (Or.inr
        ⟨encodeString date, encodeString time,
          ⟨⟨?_, (date_equiv date).1 hdate⟩,
            (time_equiv time).1 htime⟩⟩)))
      simpa [encodeString_append, encodeString, Vermilion.Seq.add,
        Vermilion.Seq.push, Vermilion.Seq.empty] using
          congrArg encodeString hsource
    · refine Or.inl (Or.inl (Or.inr
        ⟨encodeString date, encodeString time, encodeString sss,
          ⟨⟨⟨?_, (date_equiv date).1 hdate⟩,
            (time_equiv time).1 htime⟩, (sss_equiv sss).1 hsss⟩⟩))
      simpa [encodeString_append, encodeString, Vermilion.Seq.add,
        Vermilion.Seq.push, Vermilion.Seq.empty] using
          congrArg encodeString hsource
    · refine Or.inl (Or.inr
        ⟨encodeString date, encodeString time, encodeString offset,
          ⟨⟨⟨?_, (date_equiv date).1 hdate⟩,
            (time_equiv time).1 htime⟩, (offset_equiv offset).1 hoffset⟩⟩)
      simpa [encodeString_append, encodeString, Vermilion.Seq.add,
        Vermilion.Seq.push, Vermilion.Seq.empty] using
          congrArg encodeString hsource
    · refine Or.inr
        ⟨encodeString date, encodeString time, encodeString sss,
          encodeString offset,
          ⟨⟨⟨⟨?_, (date_equiv date).1 hdate⟩,
            (time_equiv time).1 htime⟩, (sss_equiv sss).1 hsss⟩,
              (offset_equiv offset).1 hoffset⟩⟩
      simpa [encodeString_append, encodeString, Vermilion.Seq.add,
        Vermilion.Seq.push, Vermilion.Seq.empty] using
          congrArg encodeString hsource
  · rintro ((((⟨dateSequence, hsource, hdate⟩ |
      ⟨dateSequence, timeSequence,
        ⟨⟨hsource, hdate⟩, htime⟩⟩) |
      ⟨dateSequence, timeSequence, sssSequence,
        ⟨⟨⟨hsource, hdate⟩, htime⟩, hsss⟩⟩) |
      ⟨dateSequence, timeSequence, offsetSequence,
        ⟨⟨⟨hsource, hdate⟩, htime⟩, hoffset⟩⟩) |
      ⟨dateSequence, timeSequence, sssSequence, offsetSequence,
        ⟨⟨⟨⟨hsource, hdate⟩, htime⟩, hsss⟩, hoffset⟩⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl
        ((date_equiv source).2 (by simpa [← hsource] using hdate)))))
    · obtain ⟨date, hdateEncode, hdateWf⟩ :=
        decode_date_text dateSequence hdate
      obtain ⟨time, htimeEncode, htimeWf⟩ :=
        decode_time_text timeSequence htime
      refine Or.inl (Or.inl (Or.inl (Or.inr
        ⟨date, time, ⟨?_, hdateWf⟩, htimeWf⟩)))
      apply encodeString_injective
      rw [encodeString_append, encodeString_append, encodeString_append,
        ← hdateEncode, ← htimeEncode]
      simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
        Vermilion.Seq.empty] using hsource
    · obtain ⟨date, hdateEncode, hdateWf⟩ :=
        decode_date_text dateSequence hdate
      obtain ⟨time, htimeEncode, htimeWf⟩ :=
        decode_time_text timeSequence htime
      obtain ⟨sss, hsssEncode, hsssWf⟩ :=
        decode_sss_text sssSequence hsss
      refine Or.inl (Or.inl (Or.inr
        ⟨date, time, sss, ⟨⟨?_, hdateWf⟩, htimeWf⟩, hsssWf⟩))
      apply encodeString_injective
      rw [encodeString_append, encodeString_append, encodeString_append,
        encodeString_append, encodeString_append, ← hdateEncode,
        ← htimeEncode, ← hsssEncode]
      simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
        Vermilion.Seq.empty] using hsource
    · obtain ⟨date, hdateEncode, hdateWf⟩ :=
        decode_date_text dateSequence hdate
      obtain ⟨time, htimeEncode, htimeWf⟩ :=
        decode_time_text timeSequence htime
      obtain ⟨offset, hoffsetEncode, hoffsetWf⟩ :=
        decode_offset_text offsetSequence hoffset
      refine Or.inl (Or.inr
        ⟨date, time, offset,
          ⟨⟨?_, hdateWf⟩, htimeWf⟩, hoffsetWf⟩)
      apply encodeString_injective
      rw [encodeString_append, encodeString_append, encodeString_append,
        ← hdateEncode, ← htimeEncode, ← hoffsetEncode]
      simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
        Vermilion.Seq.empty] using hsource
    · obtain ⟨date, hdateEncode, hdateWf⟩ :=
        decode_date_text dateSequence hdate
      obtain ⟨time, htimeEncode, htimeWf⟩ :=
        decode_time_text timeSequence htime
      obtain ⟨sss, hsssEncode, hsssWf⟩ :=
        decode_sss_text sssSequence hsss
      obtain ⟨offset, hoffsetEncode, hoffsetWf⟩ :=
        decode_offset_text offsetSequence hoffset
      refine Or.inr
        ⟨date, time, sss, offset,
          ⟨⟨⟨?_, hdateWf⟩, htimeWf⟩, hsssWf⟩, hoffsetWf⟩
      apply encodeString_injective
      rw [encodeString_append, encodeString_append, encodeString_append,
        encodeString_append, encodeString_append, ← hdateEncode,
        ← htimeEncode, ← hsssEncode, ← hoffsetEncode]
      simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
        Vermilion.Seq.empty] using hsource

def dateText (yyyy mm dd : String) : String :=
  yyyy ++ "-" ++ mm ++ "-" ++ dd

def timeText (hh mm ss : String) : String :=
  hh ++ ":" ++ mm ++ ":" ++ ss

def dateFieldsWf (mm yyyy dd : String) : Prop :=
  Datetime.IsWf.MM mm ∧ Datetime.IsWf.YYYY yyyy ∧ Datetime.IsWf.DD dd

def timeFieldsWf (hh mm ss : String) : Prop :=
  Datetime.IsWf.hh hh ∧ Datetime.IsWf.mm mm ∧ Datetime.IsWf.ss ss

def offsetFieldsWf (offset hh mm : String) : Prop :=
  ((offset = "+" ++ hh ++ mm) ∨ (offset = "-" ++ hh ++ mm)) ∧
    Datetime.IsWf.hh hh ∧ Datetime.IsWf.mm mm

def bareParts
    (input yyyy mm dd timeHh timeMm ss sss offset offsetHh offsetMm :
      String) : Prop :=
  timeHh = "" ∧ timeMm = "" ∧ ss = "" ∧ sss = "" ∧
    offset = "" ∧ offsetHh = "" ∧ offsetMm = "" ∧
      input = dateText yyyy mm dd

def utcParts
    (input yyyy mm dd timeHh timeMm ss sss offset offsetHh offsetMm :
      String) : Prop :=
  timeFieldsWf timeHh timeMm ss ∧ sss = "" ∧ offset = "" ∧
    offsetHh = "" ∧ offsetMm = "" ∧
      input = dateText yyyy mm dd ++ "T" ++
        timeText timeHh timeMm ss ++ "Z"

def millisUtcParts
    (input yyyy mm dd timeHh timeMm ss sss offset offsetHh offsetMm :
      String) : Prop :=
  timeFieldsWf timeHh timeMm ss ∧ Datetime.IsWf.SSS sss ∧
    offset = "" ∧ offsetHh = "" ∧ offsetMm = "" ∧
      input = dateText yyyy mm dd ++ "T" ++
        timeText timeHh timeMm ss ++ "." ++ sss ++ "Z"

def offsetOnlyParts
    (input yyyy mm dd timeHh timeMm ss sss offset offsetHh offsetMm :
      String) : Prop :=
  timeFieldsWf timeHh timeMm ss ∧ sss = "" ∧
    offsetFieldsWf offset offsetHh offsetMm ∧
      input = dateText yyyy mm dd ++ "T" ++
        timeText timeHh timeMm ss ++ offset

def millisOffsetParts
    (input yyyy mm dd timeHh timeMm ss sss offset offsetHh offsetMm :
      String) : Prop :=
  timeFieldsWf timeHh timeMm ss ∧ Datetime.IsWf.SSS sss ∧
    offsetFieldsWf offset offsetHh offsetMm ∧
      input = dateText yyyy mm dd ++ "T" ++
        timeText timeHh timeMm ss ++ "." ++ sss ++ offset

def datetimeParts
    (input mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm :
      String) : Prop :=
  dateFieldsWf mm yyyy dd ∧
    (bareParts input yyyy mm dd timeHh timeMm ss sss offset offsetHh
        offsetMm ∨
      utcParts input yyyy mm dd timeHh timeMm ss sss offset offsetHh
        offsetMm ∨
      millisUtcParts input yyyy mm dd timeHh timeMm ss sss offset offsetHh
        offsetMm ∨
      offsetOnlyParts input yyyy mm dd timeHh timeMm ss sss offset offsetHh
        offsetMm ∨
      millisOffsetParts input yyyy mm dd timeHh timeMm ss sss offset offsetHh
        offsetMm)

theorem matches_date_equiv
    (sequence : Vermilion.Seq Int)
    (input mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm :
      String) :
    triptych_datetime_roundtrip.datetime_matches_Date sequence
        (.DatetimeView (encodeString input) (encodeString mm)
          (encodeString yyyy) (encodeString dd) (encodeString timeHh)
          (encodeString timeMm) (encodeString ss) (encodeString sss)
          (encodeString offset) (encodeString offsetHh)
          (encodeString offsetMm)) ↔
      sequence = encodeString (dateText yyyy mm dd) ∧
        dateFieldsWf mm yyyy dd := by
  constructor
  · rintro ⟨yyyySequence, mmSequence, ddSequence,
      ⟨⟨⟨hsequence, ⟨hyyyyField, hyyyy⟩⟩,
        ⟨hmmField, hmm⟩⟩, ⟨hddField, hdd⟩⟩⟩
    simp only [triptych_datetime_roundtrip.DatetimeView.get_DatetimeView_yyyy]
      at hyyyyField
    simp only [triptych_datetime_roundtrip.DatetimeView.get_DatetimeView_mm]
      at hmmField
    simp only [triptych_datetime_roundtrip.DatetimeView.get_DatetimeView_dd]
      at hddField
    subst yyyySequence
    subst mmSequence
    subst ddSequence
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold dateText
      rw [encodeString_append, encodeString_append, encodeString_append,
        encodeString_append]
      simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
        Vermilion.Seq.empty] using hsequence
    · exact (mm_equiv mm).2 (by
        simpa [triptych_datetime_roundtrip.datetime_matches_MM,
          triptych_datetime_roundtrip.datetime_is_wf_MM] using hmm)
    · exact (yyyy_equiv yyyy).2 (by
        simpa [triptych_datetime_roundtrip.datetime_matches_YYYY,
          triptych_datetime_roundtrip.datetime_is_wf_YYYY] using hyyyy)
    · exact (dd_equiv dd).2 (by
        simpa [triptych_datetime_roundtrip.datetime_matches_DD,
          triptych_datetime_roundtrip.datetime_is_wf_DD] using hdd)
  · rintro ⟨hsequence, hmm, hyyyy, hdd⟩
    refine ⟨encodeString yyyy, encodeString mm, encodeString dd, ?_⟩
    refine ⟨⟨⟨?_, ⟨rfl, ?_⟩⟩, ⟨rfl, ?_⟩⟩, ⟨rfl, ?_⟩⟩
    · unfold dateText at hsequence
      rw [encodeString_append, encodeString_append, encodeString_append,
        encodeString_append] at hsequence
      simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
        Vermilion.Seq.empty] using hsequence
    · simpa [triptych_datetime_roundtrip.datetime_matches_YYYY,
        triptych_datetime_roundtrip.datetime_is_wf_YYYY] using
          (yyyy_equiv yyyy).1 hyyyy
    · simpa [triptych_datetime_roundtrip.datetime_matches_MM,
        triptych_datetime_roundtrip.datetime_is_wf_MM] using
          (mm_equiv mm).1 hmm
    · simpa [triptych_datetime_roundtrip.datetime_matches_DD,
        triptych_datetime_roundtrip.datetime_is_wf_DD] using
          (dd_equiv dd).1 hdd

theorem matches_time_equiv
    (sequence : Vermilion.Seq Int)
    (input mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm :
      String) :
    triptych_datetime_roundtrip.datetime_matches_Time sequence
        (.DatetimeView (encodeString input) (encodeString mm)
          (encodeString yyyy) (encodeString dd) (encodeString timeHh)
          (encodeString timeMm) (encodeString ss) (encodeString sss)
          (encodeString offset) (encodeString offsetHh)
          (encodeString offsetMm)) ↔
      sequence = encodeString (timeText timeHh timeMm ss) ∧
        timeFieldsWf timeHh timeMm ss := by
  constructor
  · rintro ⟨hhSequence, mmSequence, ssSequence,
      ⟨⟨⟨hsequence, ⟨hhhField, hhh⟩⟩,
        ⟨hmmField, hmm⟩⟩, ⟨hssField, hss⟩⟩⟩
    simp only [
      triptych_datetime_roundtrip.DatetimeView.get_DatetimeView_time_hh]
        at hhhField
    simp only [
      triptych_datetime_roundtrip.DatetimeView.get_DatetimeView_time_mm]
        at hmmField
    simp only [triptych_datetime_roundtrip.DatetimeView.get_DatetimeView_ss]
      at hssField
    subst hhSequence
    subst mmSequence
    subst ssSequence
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold timeText
      rw [encodeString_append, encodeString_append, encodeString_append,
        encodeString_append]
      simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
        Vermilion.Seq.empty] using hsequence
    · exact (hh_equiv timeHh).2 (by
        simpa [triptych_datetime_roundtrip.datetime_matches_hh,
          triptych_datetime_roundtrip.datetime_is_wf_hh] using hhh)
    · exact (minute_equiv timeMm).2 (by
        simpa [triptych_datetime_roundtrip.datetime_matches_mm,
          triptych_datetime_roundtrip.datetime_is_wf_mm] using hmm)
    · exact (ss_equiv ss).2 (by
        simpa [triptych_datetime_roundtrip.datetime_matches_ss,
          triptych_datetime_roundtrip.datetime_is_wf_ss] using hss)
  · rintro ⟨hsequence, hhh, hmm, hss⟩
    refine ⟨encodeString timeHh, encodeString timeMm, encodeString ss, ?_⟩
    refine ⟨⟨⟨?_, ⟨rfl, ?_⟩⟩, ⟨rfl, ?_⟩⟩, ⟨rfl, ?_⟩⟩
    · unfold timeText at hsequence
      rw [encodeString_append, encodeString_append, encodeString_append,
        encodeString_append] at hsequence
      simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
        Vermilion.Seq.empty] using hsequence
    · simpa [triptych_datetime_roundtrip.datetime_matches_hh,
        triptych_datetime_roundtrip.datetime_is_wf_hh] using
          (hh_equiv timeHh).1 hhh
    · simpa [triptych_datetime_roundtrip.datetime_matches_mm,
        triptych_datetime_roundtrip.datetime_is_wf_mm] using
          (minute_equiv timeMm).1 hmm
    · simpa [triptych_datetime_roundtrip.datetime_matches_ss,
        triptych_datetime_roundtrip.datetime_is_wf_ss] using
          (ss_equiv ss).1 hss

theorem matches_offset_equiv
    (sequence : Vermilion.Seq Int)
    (input mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm :
      String) :
    triptych_datetime_roundtrip.datetime_matches_Offset sequence
        (.DatetimeView (encodeString input) (encodeString mm)
          (encodeString yyyy) (encodeString dd) (encodeString timeHh)
          (encodeString timeMm) (encodeString ss) (encodeString sss)
          (encodeString offset) (encodeString offsetHh)
          (encodeString offsetMm)) ↔
      ((sequence = encodeString ("+" ++ offsetHh ++ offsetMm)) ∨
        (sequence = encodeString ("-" ++ offsetHh ++ offsetMm))) ∧
        Datetime.IsWf.hh offsetHh ∧ Datetime.IsWf.mm offsetMm := by
  constructor
  · rintro (⟨hhSequence, mmSequence,
      ⟨⟨hsequence, ⟨hhhField, hhh⟩⟩, ⟨hmmField, hmm⟩⟩⟩ |
      ⟨hhSequence, mmSequence,
        ⟨⟨hsequence, ⟨hhhField, hhh⟩⟩, ⟨hmmField, hmm⟩⟩⟩)
    all_goals
      simp only [
        triptych_datetime_roundtrip.DatetimeView.get_DatetimeView_offset_hh]
          at hhhField
      simp only [
        triptych_datetime_roundtrip.DatetimeView.get_DatetimeView_offset_mm]
          at hmmField
      subst hhSequence
      subst mmSequence
    · refine ⟨Or.inl ?_, ?_, ?_⟩
      · rw [encodeString_append, encodeString_append]
        simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
          Vermilion.Seq.empty] using hsequence
      · exact (hh_equiv offsetHh).2 (by
          simpa [triptych_datetime_roundtrip.datetime_matches_hh,
            triptych_datetime_roundtrip.datetime_is_wf_hh] using hhh)
      · exact (minute_equiv offsetMm).2 (by
          simpa [triptych_datetime_roundtrip.datetime_matches_mm,
            triptych_datetime_roundtrip.datetime_is_wf_mm] using hmm)
    · refine ⟨Or.inr ?_, ?_, ?_⟩
      · rw [encodeString_append, encodeString_append]
        simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
          Vermilion.Seq.empty] using hsequence
      · exact (hh_equiv offsetHh).2 (by
          simpa [triptych_datetime_roundtrip.datetime_matches_hh,
            triptych_datetime_roundtrip.datetime_is_wf_hh] using hhh)
      · exact (minute_equiv offsetMm).2 (by
          simpa [triptych_datetime_roundtrip.datetime_matches_mm,
            triptych_datetime_roundtrip.datetime_is_wf_mm] using hmm)
  · rintro ⟨hpositive | hnegative, hhh, hmm⟩
    · left
      refine ⟨encodeString offsetHh, encodeString offsetMm,
        ⟨⟨?_, ⟨rfl, ?_⟩⟩, ⟨rfl, ?_⟩⟩⟩
      · rw [encodeString_append, encodeString_append] at hpositive
        simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
          Vermilion.Seq.empty] using hpositive
      · simpa [triptych_datetime_roundtrip.datetime_matches_hh,
          triptych_datetime_roundtrip.datetime_is_wf_hh] using
            (hh_equiv offsetHh).1 hhh
      · simpa [triptych_datetime_roundtrip.datetime_matches_mm,
          triptych_datetime_roundtrip.datetime_is_wf_mm] using
            (minute_equiv offsetMm).1 hmm
    · right
      refine ⟨encodeString offsetHh, encodeString offsetMm,
        ⟨⟨?_, ⟨rfl, ?_⟩⟩, ⟨rfl, ?_⟩⟩⟩
      · rw [encodeString_append, encodeString_append] at hnegative
        simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
          Vermilion.Seq.empty] using hnegative
      · simpa [triptych_datetime_roundtrip.datetime_matches_hh,
          triptych_datetime_roundtrip.datetime_is_wf_hh] using
            (hh_equiv offsetHh).1 hhh
      · simpa [triptych_datetime_roundtrip.datetime_matches_mm,
          triptych_datetime_roundtrip.datetime_is_wf_mm] using
            (minute_equiv offsetMm).1 hmm

theorem matches_sss_is_wf
    (sequence : Vermilion.Seq Int)
    (view : triptych_datetime_roundtrip.DatetimeView) :
    triptych_datetime_roundtrip.datetime_matches_SSS sequence view ↔
      triptych_datetime_roundtrip.datetime_is_wf_SSS sequence := by
  rfl

theorem matches_view_equiv
    (input mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm :
      String) :
    triptych_datetime_roundtrip.datetime_matches_view (encodeString input)
        (.DatetimeView (encodeString input) (encodeString mm)
          (encodeString yyyy) (encodeString dd) (encodeString timeHh)
          (encodeString timeMm) (encodeString ss) (encodeString sss)
          (encodeString offset) (encodeString offsetHh)
          (encodeString offsetMm)) ↔
      datetimeParts input mm yyyy dd timeHh timeMm ss sss offset offsetHh
        offsetMm := by
  unfold datetimeParts bareParts utcParts millisUtcParts offsetOnlyParts
    millisOffsetParts
  constructor
  · rintro ⟨_, ((((hbare | hutc) | hmillisUtc) | hoffsetOnly) |
      hmillisOffset)⟩
    · rcases hbare with ⟨dateSequence,
        ⟨⟨⟨⟨⟨⟨⟨⟨hinput, hdate⟩, htimeHh⟩, htimeMm⟩, hss⟩,
          hsss⟩, hoffset⟩, hoffsetHh⟩, hoffsetMm⟩⟩
      have hdate' := (matches_date_equiv dateSequence input mm yyyy dd
        timeHh timeMm ss sss offset offsetHh offsetMm).1 hdate
      refine ⟨hdate'.2, Or.inl ?_⟩
      exact ⟨(encodeString_eq_empty_iff timeHh).1 htimeHh,
        (encodeString_eq_empty_iff timeMm).1 htimeMm,
        (encodeString_eq_empty_iff ss).1 hss,
        (encodeString_eq_empty_iff sss).1 hsss,
        (encodeString_eq_empty_iff offset).1 hoffset,
        (encodeString_eq_empty_iff offsetHh).1 hoffsetHh,
        (encodeString_eq_empty_iff offsetMm).1 hoffsetMm,
        encodeString_injective (hinput.trans hdate'.1)⟩
    · rcases hutc with ⟨dateSequence, timeSequence,
        ⟨⟨⟨⟨⟨⟨hinput, hdate⟩, htime⟩, hsss⟩, hoffset⟩,
          hoffsetHh⟩, hoffsetMm⟩⟩
      have hdate' := (matches_date_equiv dateSequence input mm yyyy dd
        timeHh timeMm ss sss offset offsetHh offsetMm).1 hdate
      have htime' := (matches_time_equiv timeSequence input mm yyyy dd
        timeHh timeMm ss sss offset offsetHh offsetMm).1 htime
      refine ⟨hdate'.2, Or.inr (Or.inl ?_)⟩
      refine ⟨htime'.2, (encodeString_eq_empty_iff sss).1 hsss,
        (encodeString_eq_empty_iff offset).1 hoffset,
        (encodeString_eq_empty_iff offsetHh).1 hoffsetHh,
        (encodeString_eq_empty_iff offsetMm).1 hoffsetMm, ?_⟩
      apply encodeString_injective
      simpa [encodeString_append, encodeString, Vermilion.Seq.add,
        Vermilion.Seq.push, Vermilion.Seq.empty, hdate'.1, htime'.1]
        using hinput
    · rcases hmillisUtc with ⟨dateSequence, timeSequence, sssSequence,
        ⟨⟨⟨⟨⟨⟨hinput, hdate⟩, htime⟩, ⟨hsssField, hsssMatch⟩⟩,
          hoffset⟩, hoffsetHh⟩, hoffsetMm⟩⟩
      have hdate' := (matches_date_equiv dateSequence input mm yyyy dd
        timeHh timeMm ss sss offset offsetHh offsetMm).1 hdate
      have htime' := (matches_time_equiv timeSequence input mm yyyy dd
        timeHh timeMm ss sss offset offsetHh offsetMm).1 htime
      simp only [triptych_datetime_roundtrip.DatetimeView.get_DatetimeView_sss]
        at hsssField
      subst sssSequence
      have hsssWf : Datetime.IsWf.SSS sss := by
        apply (sss_equiv sss).2
        exact (matches_sss_is_wf (encodeString sss)
          (.DatetimeView (encodeString input) (encodeString mm)
            (encodeString yyyy) (encodeString dd) (encodeString timeHh)
            (encodeString timeMm) (encodeString ss) (encodeString sss)
            (encodeString offset) (encodeString offsetHh)
            (encodeString offsetMm))).1 hsssMatch
      refine ⟨hdate'.2, Or.inr (Or.inr (Or.inl ?_))⟩
      refine ⟨htime'.2, hsssWf,
        (encodeString_eq_empty_iff offset).1 hoffset,
        (encodeString_eq_empty_iff offsetHh).1 hoffsetHh,
        (encodeString_eq_empty_iff offsetMm).1 hoffsetMm, ?_⟩
      apply encodeString_injective
      simpa [encodeString_append, encodeString, Vermilion.Seq.add,
        Vermilion.Seq.push, Vermilion.Seq.empty, hdate'.1, htime'.1]
        using hinput
    · rcases hoffsetOnly with ⟨dateSequence, timeSequence, offsetSequence,
        ⟨⟨⟨⟨hinput, hdate⟩, htime⟩,
          ⟨hoffsetField, hoffsetMatch⟩⟩, hsss⟩⟩
      have hdate' := (matches_date_equiv dateSequence input mm yyyy dd
        timeHh timeMm ss sss offset offsetHh offsetMm).1 hdate
      have htime' := (matches_time_equiv timeSequence input mm yyyy dd
        timeHh timeMm ss sss offset offsetHh offsetMm).1 htime
      simp only [
        triptych_datetime_roundtrip.DatetimeView.get_DatetimeView_offset]
          at hoffsetField
      subst offsetSequence
      have hoffset' := (matches_offset_equiv (encodeString offset) input mm
        yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm).1
          hoffsetMatch
      have hoffsetWf : offsetFieldsWf offset offsetHh offsetMm := by
        refine ⟨?_, hoffset'.2.1, hoffset'.2.2⟩
        rcases hoffset'.1 with hpositive | hnegative
        · exact Or.inl (encodeString_injective hpositive)
        · exact Or.inr (encodeString_injective hnegative)
      refine ⟨hdate'.2, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
      refine ⟨htime'.2, (encodeString_eq_empty_iff sss).1 hsss,
        hoffsetWf, ?_⟩
      apply encodeString_injective
      simpa [encodeString_append, encodeString, Vermilion.Seq.add,
        Vermilion.Seq.push, Vermilion.Seq.empty, hdate'.1, htime'.1]
        using hinput
    · rcases hmillisOffset with
        ⟨dateSequence, timeSequence, sssSequence, offsetSequence,
          ⟨⟨⟨⟨hinput, hdate⟩, htime⟩,
            ⟨hsssField, hsssMatch⟩⟩,
              ⟨hoffsetField, hoffsetMatch⟩⟩⟩
      have hdate' := (matches_date_equiv dateSequence input mm yyyy dd
        timeHh timeMm ss sss offset offsetHh offsetMm).1 hdate
      have htime' := (matches_time_equiv timeSequence input mm yyyy dd
        timeHh timeMm ss sss offset offsetHh offsetMm).1 htime
      simp only [triptych_datetime_roundtrip.DatetimeView.get_DatetimeView_sss]
        at hsssField
      simp only [
        triptych_datetime_roundtrip.DatetimeView.get_DatetimeView_offset]
          at hoffsetField
      subst sssSequence
      subst offsetSequence
      have hsssWf : Datetime.IsWf.SSS sss := by
        apply (sss_equiv sss).2
        exact (matches_sss_is_wf (encodeString sss)
          (.DatetimeView (encodeString input) (encodeString mm)
            (encodeString yyyy) (encodeString dd) (encodeString timeHh)
            (encodeString timeMm) (encodeString ss) (encodeString sss)
            (encodeString offset) (encodeString offsetHh)
            (encodeString offsetMm))).1 hsssMatch
      have hoffset' := (matches_offset_equiv (encodeString offset) input mm
        yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm).1
          hoffsetMatch
      have hoffsetWf : offsetFieldsWf offset offsetHh offsetMm := by
        refine ⟨?_, hoffset'.2.1, hoffset'.2.2⟩
        rcases hoffset'.1 with hpositive | hnegative
        · exact Or.inl (encodeString_injective hpositive)
        · exact Or.inr (encodeString_injective hnegative)
      refine ⟨hdate'.2, Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
      refine ⟨htime'.2, hsssWf, hoffsetWf, ?_⟩
      apply encodeString_injective
      simpa [encodeString_append, encodeString, Vermilion.Seq.add,
        Vermilion.Seq.push, Vermilion.Seq.empty, hdate'.1, htime'.1]
        using hinput
  · rintro ⟨hdate, hbranches⟩
    refine ⟨rfl, ?_⟩
    rcases hbranches with hbare | hutc | hmillisUtc | hoffsetOnly |
      hmillisOffset
    · rcases hbare with
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hinput⟩
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply Or.inl
      refine ⟨encodeString (dateText yyyy mm dd), ?_⟩
      refine ⟨⟨⟨⟨⟨⟨⟨⟨?_,
        (matches_date_equiv _ input mm yyyy dd "" "" "" "" "" "" "").2
          ⟨rfl, hdate⟩⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
      simpa [encodeString, Vermilion.Seq.empty] using
        congrArg encodeString hinput
    · rcases hutc with
        ⟨htime, rfl, rfl, rfl, rfl, hinput⟩
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply Or.inr
      refine ⟨encodeString (dateText yyyy mm dd),
        encodeString (timeText timeHh timeMm ss), ?_⟩
      refine ⟨⟨⟨⟨⟨⟨?_,
        (matches_date_equiv _ input mm yyyy dd timeHh timeMm ss "" "" "" "").2
          ⟨rfl, hdate⟩⟩,
        (matches_time_equiv _ input mm yyyy dd timeHh timeMm ss "" "" "" "").2
          ⟨rfl, htime⟩⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
      simpa [encodeString_append, encodeString, Vermilion.Seq.add,
        Vermilion.Seq.push, Vermilion.Seq.empty] using
          congrArg encodeString hinput
    · rcases hmillisUtc with
        ⟨htime, hsss, rfl, rfl, rfl, hinput⟩
      apply Or.inl
      apply Or.inl
      apply Or.inr
      refine ⟨encodeString (dateText yyyy mm dd),
        encodeString (timeText timeHh timeMm ss), encodeString sss, ?_⟩
      refine ⟨⟨⟨⟨⟨⟨?_,
        (matches_date_equiv _ input mm yyyy dd timeHh timeMm ss sss "" "" "").2
          ⟨rfl, hdate⟩⟩,
        (matches_time_equiv _ input mm yyyy dd timeHh timeMm ss sss "" "" "").2
          ⟨rfl, htime⟩⟩, ⟨rfl, ?_⟩⟩, rfl⟩, rfl⟩, rfl⟩
      · simpa [encodeString_append, encodeString, Vermilion.Seq.add,
          Vermilion.Seq.push, Vermilion.Seq.empty] using
            congrArg encodeString hinput
      · exact (matches_sss_is_wf (encodeString sss)
          (.DatetimeView (encodeString input) (encodeString mm)
            (encodeString yyyy) (encodeString dd) (encodeString timeHh)
            (encodeString timeMm) (encodeString ss) (encodeString sss)
            (encodeString "") (encodeString "") (encodeString ""))).2
              ((sss_equiv sss).1 hsss)
    · rcases hoffsetOnly with ⟨htime, rfl, hoffset, hinput⟩
      apply Or.inl
      apply Or.inr
      refine ⟨encodeString (dateText yyyy mm dd),
        encodeString (timeText timeHh timeMm ss), encodeString offset, ?_⟩
      refine ⟨⟨⟨⟨?_,
        (matches_date_equiv _ input mm yyyy dd timeHh timeMm ss "" offset
          offsetHh offsetMm).2 ⟨rfl, hdate⟩⟩,
        (matches_time_equiv _ input mm yyyy dd timeHh timeMm ss "" offset
          offsetHh offsetMm).2 ⟨rfl, htime⟩⟩, ⟨rfl, ?_⟩⟩, rfl⟩
      · simpa [encodeString_append, encodeString, Vermilion.Seq.add,
          Vermilion.Seq.push, Vermilion.Seq.empty] using
            congrArg encodeString hinput
      · apply (matches_offset_equiv (encodeString offset) input mm yyyy dd
          timeHh timeMm ss "" offset offsetHh offsetMm).2
        rcases hoffset with ⟨htext, hhh, hmm⟩
        refine ⟨?_, hhh, hmm⟩
        rcases htext with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
    · rcases hmillisOffset with ⟨htime, hsss, hoffset, hinput⟩
      apply Or.inr
      refine ⟨encodeString (dateText yyyy mm dd),
        encodeString (timeText timeHh timeMm ss), encodeString sss,
        encodeString offset, ?_⟩
      refine ⟨⟨⟨⟨?_,
        (matches_date_equiv _ input mm yyyy dd timeHh timeMm ss sss offset
          offsetHh offsetMm).2 ⟨rfl, hdate⟩⟩,
        (matches_time_equiv _ input mm yyyy dd timeHh timeMm ss sss offset
          offsetHh offsetMm).2 ⟨rfl, htime⟩⟩, ⟨rfl, ?_⟩⟩,
          ⟨rfl, ?_⟩⟩
      · simpa [encodeString_append, encodeString, Vermilion.Seq.add,
          Vermilion.Seq.push, Vermilion.Seq.empty] using
            congrArg encodeString hinput
      · exact (matches_sss_is_wf (encodeString sss)
          (.DatetimeView (encodeString input) (encodeString mm)
            (encodeString yyyy) (encodeString dd) (encodeString timeHh)
            (encodeString timeMm) (encodeString ss) (encodeString sss)
            (encodeString offset) (encodeString offsetHh)
            (encodeString offsetMm))).2 ((sss_equiv sss).1 hsss)
      · apply (matches_offset_equiv (encodeString offset) input mm yyyy dd
          timeHh timeMm ss sss offset offsetHh offsetMm).2
        rcases hoffset with ⟨htext, hhh, hmm⟩
        refine ⟨?_, hhh, hmm⟩
        rcases htext with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl

theorem source_date_parts (source : String) :
    Datetime.IsWf.Date source ↔
      ∃ mm yyyy dd : String,
        dateFieldsWf mm yyyy dd ∧ source = dateText yyyy mm dd := by
  constructor
  · rintro ⟨yyyy, mm, dd, ⟨⟨⟨hsource, hyyyy⟩, hmm⟩, hdd⟩⟩
    exact ⟨mm, yyyy, dd, ⟨hmm, hyyyy, hdd⟩, hsource⟩
  · rintro ⟨mm, yyyy, dd, ⟨hmm, hyyyy, hdd⟩, hsource⟩
    exact ⟨yyyy, mm, dd, ⟨⟨⟨hsource, hyyyy⟩, hmm⟩, hdd⟩⟩

theorem source_time_parts (source : String) :
    Datetime.IsWf.Time source ↔
      ∃ hh mm ss : String,
        timeFieldsWf hh mm ss ∧ source = timeText hh mm ss := by
  constructor
  · rintro ⟨hh, mm, ss, ⟨⟨⟨hsource, hhh⟩, hmm⟩, hss⟩⟩
    exact ⟨hh, mm, ss, ⟨hhh, hmm, hss⟩, hsource⟩
  · rintro ⟨hh, mm, ss, ⟨hhh, hmm, hss⟩, hsource⟩
    exact ⟨hh, mm, ss, ⟨⟨⟨hsource, hhh⟩, hmm⟩, hss⟩⟩

theorem source_offset_parts (source : String) :
    Datetime.IsWf.Offset source ↔
      ∃ hh mm : String, offsetFieldsWf source hh mm := by
  constructor
  · rintro (⟨hh, mm, ⟨hsource, hhh⟩, hmm⟩ |
      ⟨hh, mm, ⟨hsource, hhh⟩, hmm⟩)
    · exact ⟨hh, mm, Or.inl hsource, hhh, hmm⟩
    · exact ⟨hh, mm, Or.inr hsource, hhh, hmm⟩
  · rintro ⟨hh, mm, ⟨hpositive | hnegative, hhh, hmm⟩⟩
    · exact Or.inl ⟨hh, mm, ⟨hpositive, hhh⟩, hmm⟩
    · exact Or.inr ⟨hh, mm, ⟨hnegative, hhh⟩, hmm⟩

theorem datetime_parts_exists_equiv (input : String) :
    Datetime.IsWf.Datetime input ↔
      ∃ mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm : String,
        datetimeParts input mm yyyy dd timeHh timeMm ss sss offset offsetHh
          offsetMm := by
  unfold Datetime.IsWf.Datetime Datetime.Production
  constructor
  · rintro ((((hbare | hutc) | hmillisUtc) | hoffsetOnly) |
      hmillisOffset)
    · obtain ⟨mm, yyyy, dd, hdate, hinput⟩ :=
        (source_date_parts input).1 hbare
      refine ⟨mm, yyyy, dd, "", "", "", "", "", "", "", ?_⟩
      unfold datetimeParts bareParts utcParts millisUtcParts offsetOnlyParts
        millisOffsetParts
      exact ⟨hdate, Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        hinput⟩⟩
    · rcases hutc with ⟨date, time, ⟨hinput, hdate⟩, htime⟩
      obtain ⟨mm, yyyy, dd, hdateFields, hdateText⟩ :=
        (source_date_parts date).1 hdate
      obtain ⟨timeHh, timeMm, ss, htimeFields, htimeText⟩ :=
        (source_time_parts time).1 htime
      refine ⟨mm, yyyy, dd, timeHh, timeMm, ss, "", "", "", "", ?_⟩
      unfold datetimeParts bareParts utcParts millisUtcParts offsetOnlyParts
        millisOffsetParts
      refine ⟨hdateFields, Or.inr (Or.inl
        ⟨htimeFields, rfl, rfl, rfl, rfl, ?_⟩)⟩
      rw [hinput, hdateText, htimeText]
    · rcases hmillisUtc with
        ⟨date, time, sss, ⟨⟨hinput, hdate⟩, htime⟩, hsss⟩
      obtain ⟨mm, yyyy, dd, hdateFields, hdateText⟩ :=
        (source_date_parts date).1 hdate
      obtain ⟨timeHh, timeMm, ss, htimeFields, htimeText⟩ :=
        (source_time_parts time).1 htime
      refine ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, "", "", "", ?_⟩
      unfold datetimeParts bareParts utcParts millisUtcParts offsetOnlyParts
        millisOffsetParts
      refine ⟨hdateFields, Or.inr (Or.inr (Or.inl
        ⟨htimeFields, hsss, rfl, rfl, rfl, ?_⟩))⟩
      rw [hinput, hdateText, htimeText]
    · rcases hoffsetOnly with
        ⟨date, time, offset, ⟨⟨hinput, hdate⟩, htime⟩, hoffset⟩
      obtain ⟨mm, yyyy, dd, hdateFields, hdateText⟩ :=
        (source_date_parts date).1 hdate
      obtain ⟨timeHh, timeMm, ss, htimeFields, htimeText⟩ :=
        (source_time_parts time).1 htime
      obtain ⟨offsetHh, offsetMm, hoffsetFields⟩ :=
        (source_offset_parts offset).1 hoffset
      refine ⟨mm, yyyy, dd, timeHh, timeMm, ss, "", offset,
        offsetHh, offsetMm, ?_⟩
      unfold datetimeParts bareParts utcParts millisUtcParts offsetOnlyParts
        millisOffsetParts
      refine ⟨hdateFields, Or.inr (Or.inr (Or.inr (Or.inl
        ⟨htimeFields, rfl, hoffsetFields, ?_⟩)))⟩
      rw [hinput, hdateText, htimeText]
    · rcases hmillisOffset with
        ⟨date, time, sss, offset,
          ⟨⟨⟨hinput, hdate⟩, htime⟩, hsss⟩, hoffset⟩
      obtain ⟨mm, yyyy, dd, hdateFields, hdateText⟩ :=
        (source_date_parts date).1 hdate
      obtain ⟨timeHh, timeMm, ss, htimeFields, htimeText⟩ :=
        (source_time_parts time).1 htime
      obtain ⟨offsetHh, offsetMm, hoffsetFields⟩ :=
        (source_offset_parts offset).1 hoffset
      refine ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset,
        offsetHh, offsetMm, ?_⟩
      unfold datetimeParts bareParts utcParts millisUtcParts offsetOnlyParts
        millisOffsetParts
      refine ⟨hdateFields, Or.inr (Or.inr (Or.inr (Or.inr
        ⟨htimeFields, hsss, hoffsetFields, ?_⟩)))⟩
      rw [hinput, hdateText, htimeText]
  · rintro ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, hparts⟩
    unfold datetimeParts bareParts utcParts millisUtcParts offsetOnlyParts
      millisOffsetParts at hparts
    rcases hparts with ⟨hdate,
      hbare | hutc | hmillisUtc | hoffsetOnly | hmillisOffset⟩
    · rcases hbare with
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hinput⟩
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply (source_date_parts input).2
      exact ⟨mm, yyyy, dd, hdate, hinput⟩
    · rcases hutc with ⟨htime, rfl, rfl, rfl, rfl, hinput⟩
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply Or.inr
      exact ⟨dateText yyyy mm dd, timeText timeHh timeMm ss,
        ⟨hinput, (source_date_parts _).2 ⟨mm, yyyy, dd, hdate, rfl⟩⟩,
        (source_time_parts _).2 ⟨timeHh, timeMm, ss, htime, rfl⟩⟩
    · rcases hmillisUtc with ⟨htime, hsss, rfl, rfl, rfl, hinput⟩
      apply Or.inl
      apply Or.inl
      apply Or.inr
      exact ⟨dateText yyyy mm dd, timeText timeHh timeMm ss, sss,
        ⟨⟨hinput, (source_date_parts _).2
          ⟨mm, yyyy, dd, hdate, rfl⟩⟩,
          (source_time_parts _).2
            ⟨timeHh, timeMm, ss, htime, rfl⟩⟩, hsss⟩
    · rcases hoffsetOnly with ⟨htime, rfl, hoffset, hinput⟩
      apply Or.inl
      apply Or.inr
      exact ⟨dateText yyyy mm dd, timeText timeHh timeMm ss, offset,
        ⟨⟨hinput, (source_date_parts _).2
          ⟨mm, yyyy, dd, hdate, rfl⟩⟩,
          (source_time_parts _).2
            ⟨timeHh, timeMm, ss, htime, rfl⟩⟩,
        (source_offset_parts _).2 ⟨offsetHh, offsetMm, hoffset⟩⟩
    · rcases hmillisOffset with ⟨htime, hsss, hoffset, hinput⟩
      apply Or.inr
      exact ⟨dateText yyyy mm dd, timeText timeHh timeMm ss, sss, offset,
        ⟨⟨⟨hinput, (source_date_parts _).2
          ⟨mm, yyyy, dd, hdate, rfl⟩⟩,
          (source_time_parts _).2
            ⟨timeHh, timeMm, ss, htime, rfl⟩⟩, hsss⟩,
        (source_offset_parts _).2 ⟨offsetHh, offsetMm, hoffset⟩⟩

theorem matching_view_exists_equiv (input : String) :
    Datetime.IsWf.Datetime input ↔
      ∃ mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm : String,
        triptych_datetime_roundtrip.datetime_matches_view (encodeString input)
          (.DatetimeView (encodeString input) (encodeString mm)
            (encodeString yyyy) (encodeString dd) (encodeString timeHh)
            (encodeString timeMm) (encodeString ss) (encodeString sss)
            (encodeString offset) (encodeString offsetHh)
            (encodeString offsetMm)) := by
  rw [datetime_parts_exists_equiv]
  constructor
  · rintro ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, hparts⟩
    exact ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, (matches_view_equiv input mm yyyy dd timeHh timeMm ss sss
        offset offsetHh offsetMm).2 hparts⟩
  · rintro ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, hmatch⟩
    exact ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, (matches_view_equiv input mm yyyy dd timeHh timeMm ss sss
        offset offsetHh offsetMm).1 hmatch⟩

def componentsFields
    (components : Cedar.Thm.Datetime.DatetimeComponents)
    (mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm : String) :
    Prop :=
  (CaptureMap.toEnv (componentsCaptures components) "MM").getD "" = mm ∧
    (CaptureMap.toEnv (componentsCaptures components) "YYYY").getD "" = yyyy ∧
    (CaptureMap.toEnv (componentsCaptures components) "DD").getD "" = dd ∧
    (CaptureMap.toEnv (componentsCaptures components) "Time.hh").getD "" =
      timeHh ∧
    (CaptureMap.toEnv (componentsCaptures components) "Time.mm").getD "" =
      timeMm ∧
    (CaptureMap.toEnv (componentsCaptures components) "ss").getD "" = ss ∧
    (CaptureMap.toEnv (componentsCaptures components) "SSS").getD "" = sss ∧
    (CaptureMap.toEnv (componentsCaptures components) "Offset").getD "" =
      offset ∧
    (CaptureMap.toEnv (componentsCaptures components) "Offset.hh").getD "" =
      offsetHh ∧
    (CaptureMap.toEnv (componentsCaptures components) "Offset.mm").getD "" =
      offsetMm

theorem components_of_datetime_parts
    (input mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm :
      String)
    (hparts :
      datetimeParts input mm yyyy dd timeHh timeMm ss sss offset offsetHh
        offsetMm) :
    ∃ components : Cedar.Thm.Datetime.DatetimeComponents,
      components.syntaxWf ∧ components.asString = input ∧
        componentsFields components mm yyyy dd timeHh timeMm ss sss offset
          offsetHh offsetMm := by
  unfold datetimeParts bareParts utcParts millisUtcParts offsetOnlyParts
    millisOffsetParts at hparts
  rcases hparts with ⟨⟨hmm, hyyyy, hdd⟩,
    hbare | hutc | hmillisUtc | hoffsetOnly | hmillisOffset⟩
  all_goals
    have hmm' : String.IsFixedDigits 2 mm :=
      (fixedDigits_iff 2 (by omega) mm).mp hmm
    have hyyyy' : String.IsFixedDigits 4 yyyy :=
      (fixedDigits_iff 4 (by omega) yyyy).mp hyyyy
    have hdd' : String.IsFixedDigits 2 dd :=
      (fixedDigits_iff 2 (by omega) dd).mp hdd
  · rcases hbare with
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hinput⟩
    let date : Cedar.Thm.Datetime.DateComponents := ⟨yyyy, mm, dd⟩
    let components : Cedar.Thm.Datetime.DatetimeComponents := ⟨date, none⟩
    refine ⟨components, ?_, ?_, ?_⟩
    · exact ⟨⟨hyyyy', hmm', hdd'⟩, trivial⟩
    · simpa [components, date, Cedar.Thm.Datetime.DatetimeComponents.asString,
        Cedar.Thm.Datetime.DateComponents.asString, dateText] using hinput.symm
    · simp [componentsFields, components, date, componentsCaptures,
        dateCaptures, CaptureMap.toEnv]
  · rcases hutc with ⟨⟨htimeHh, htimeMm, hss⟩, rfl, rfl, rfl, rfl,
      hinput⟩
    have htimeHh' : String.IsFixedDigits 2 timeHh :=
      (fixedDigits_iff 2 (by omega) timeHh).mp htimeHh
    have htimeMm' : String.IsFixedDigits 2 timeMm :=
      (fixedDigits_iff 2 (by omega) timeMm).mp htimeMm
    have hss' : String.IsFixedDigits 2 ss :=
      (fixedDigits_iff 2 (by omega) ss).mp hss
    let date : Cedar.Thm.Datetime.DateComponents := ⟨yyyy, mm, dd⟩
    let time : Cedar.Thm.Datetime.TimeComponents :=
      ⟨timeHh, timeMm, ss⟩
    let timePart : Cedar.Thm.Datetime.TimePart := ⟨time, none, .utc⟩
    let components : Cedar.Thm.Datetime.DatetimeComponents :=
      ⟨date, some timePart⟩
    refine ⟨components, ?_, ?_, ?_⟩
    · exact ⟨⟨hyyyy', hmm', hdd'⟩,
        ⟨⟨htimeHh', htimeMm', hss'⟩, trivial, trivial⟩⟩
    · simpa [components, timePart, date, time,
        Cedar.Thm.Datetime.DatetimeComponents.asString,
        Cedar.Thm.Datetime.DateComponents.asString,
        Cedar.Thm.Datetime.TimePart.asString,
        Cedar.Thm.Datetime.TimeComponents.asString,
        Cedar.Thm.Datetime.Zone.asString, dateText, timeText,
        String.append_assoc] using hinput.symm
    · simp [componentsFields, components, timePart, date, time,
        componentsCaptures, dateCaptures, timeCaptures, CaptureMap.toEnv]
  · rcases hmillisUtc with
      ⟨⟨htimeHh, htimeMm, hss⟩, hsss, rfl, rfl, rfl, hinput⟩
    have htimeHh' : String.IsFixedDigits 2 timeHh :=
      (fixedDigits_iff 2 (by omega) timeHh).mp htimeHh
    have htimeMm' : String.IsFixedDigits 2 timeMm :=
      (fixedDigits_iff 2 (by omega) timeMm).mp htimeMm
    have hss' : String.IsFixedDigits 2 ss :=
      (fixedDigits_iff 2 (by omega) ss).mp hss
    have hsss' : String.IsFixedDigits 3 sss :=
      (fixedDigits_iff 3 (by omega) sss).mp hsss
    let date : Cedar.Thm.Datetime.DateComponents := ⟨yyyy, mm, dd⟩
    let time : Cedar.Thm.Datetime.TimeComponents :=
      ⟨timeHh, timeMm, ss⟩
    let timePart : Cedar.Thm.Datetime.TimePart := ⟨time, some sss, .utc⟩
    let components : Cedar.Thm.Datetime.DatetimeComponents :=
      ⟨date, some timePart⟩
    refine ⟨components, ?_, ?_, ?_⟩
    · exact ⟨⟨hyyyy', hmm', hdd'⟩,
        ⟨⟨htimeHh', htimeMm', hss'⟩, hsss', trivial⟩⟩
    · simpa [components, timePart, date, time,
        Cedar.Thm.Datetime.DatetimeComponents.asString,
        Cedar.Thm.Datetime.DateComponents.asString,
        Cedar.Thm.Datetime.TimePart.asString,
        Cedar.Thm.Datetime.TimeComponents.asString,
        Cedar.Thm.Datetime.Zone.asString, dateText, timeText,
        String.append_assoc] using hinput.symm
    · simp [componentsFields, components, timePart, date, time,
        componentsCaptures, dateCaptures, timeCaptures, CaptureMap.toEnv]
  · rcases hoffsetOnly with
      ⟨⟨htimeHh, htimeMm, hss⟩, rfl,
        ⟨hoffsetText, hoffsetHh, hoffsetMm⟩, hinput⟩
    have htimeHh' : String.IsFixedDigits 2 timeHh :=
      (fixedDigits_iff 2 (by omega) timeHh).mp htimeHh
    have htimeMm' : String.IsFixedDigits 2 timeMm :=
      (fixedDigits_iff 2 (by omega) timeMm).mp htimeMm
    have hss' : String.IsFixedDigits 2 ss :=
      (fixedDigits_iff 2 (by omega) ss).mp hss
    have hoffsetHh' : String.IsFixedDigits 2 offsetHh :=
      (fixedDigits_iff 2 (by omega) offsetHh).mp hoffsetHh
    have hoffsetMm' : String.IsFixedDigits 2 offsetMm :=
      (fixedDigits_iff 2 (by omega) offsetMm).mp hoffsetMm
    rcases hoffsetText with hpositive | hnegative
    · let date : Cedar.Thm.Datetime.DateComponents := ⟨yyyy, mm, dd⟩
      let time : Cedar.Thm.Datetime.TimeComponents :=
        ⟨timeHh, timeMm, ss⟩
      let zoneOffset : Cedar.Thm.Datetime.OffsetComponents :=
        ⟨false, offsetHh, offsetMm⟩
      let timePart : Cedar.Thm.Datetime.TimePart :=
        ⟨time, none, .offset zoneOffset⟩
      let components : Cedar.Thm.Datetime.DatetimeComponents :=
        ⟨date, some timePart⟩
      refine ⟨components, ?_, ?_, ?_⟩
      · exact ⟨⟨hyyyy', hmm', hdd'⟩,
          ⟨⟨htimeHh', htimeMm', hss'⟩, trivial,
            ⟨hoffsetHh', hoffsetMm'⟩⟩⟩
      · have hzoneOffsetString :
            zoneOffset.asString = "+" ++ offsetHh ++ offsetMm := by
          simp [zoneOffset, Cedar.Thm.Datetime.OffsetComponents.asString]
        simpa [components, timePart, date, time,
          Cedar.Thm.Datetime.DatetimeComponents.asString,
          Cedar.Thm.Datetime.DateComponents.asString,
          Cedar.Thm.Datetime.TimePart.asString,
          Cedar.Thm.Datetime.TimeComponents.asString,
          Cedar.Thm.Datetime.Zone.asString, dateText, timeText,
          String.append_assoc, hpositive, hzoneOffsetString] using hinput.symm
      · simp [componentsFields, components, timePart, zoneOffset, date, time,
          componentsCaptures, dateCaptures, timeCaptures, offsetCaptures,
          CaptureMap.toEnv, Cedar.Thm.Datetime.OffsetComponents.asString,
          hpositive]
    · let date : Cedar.Thm.Datetime.DateComponents := ⟨yyyy, mm, dd⟩
      let time : Cedar.Thm.Datetime.TimeComponents :=
        ⟨timeHh, timeMm, ss⟩
      let zoneOffset : Cedar.Thm.Datetime.OffsetComponents :=
        ⟨true, offsetHh, offsetMm⟩
      let timePart : Cedar.Thm.Datetime.TimePart :=
        ⟨time, none, .offset zoneOffset⟩
      let components : Cedar.Thm.Datetime.DatetimeComponents :=
        ⟨date, some timePart⟩
      refine ⟨components, ?_, ?_, ?_⟩
      · exact ⟨⟨hyyyy', hmm', hdd'⟩,
          ⟨⟨htimeHh', htimeMm', hss'⟩, trivial,
            ⟨hoffsetHh', hoffsetMm'⟩⟩⟩
      · have hzoneOffsetString :
            zoneOffset.asString = "-" ++ offsetHh ++ offsetMm := by
          simp [zoneOffset, Cedar.Thm.Datetime.OffsetComponents.asString]
        simpa [components, timePart, date, time,
          Cedar.Thm.Datetime.DatetimeComponents.asString,
          Cedar.Thm.Datetime.DateComponents.asString,
          Cedar.Thm.Datetime.TimePart.asString,
          Cedar.Thm.Datetime.TimeComponents.asString,
          Cedar.Thm.Datetime.Zone.asString, dateText, timeText,
          String.append_assoc, hnegative, hzoneOffsetString] using hinput.symm
      · simp [componentsFields, components, timePart, zoneOffset, date, time,
          componentsCaptures, dateCaptures, timeCaptures, offsetCaptures,
          CaptureMap.toEnv, Cedar.Thm.Datetime.OffsetComponents.asString,
          hnegative]
  · rcases hmillisOffset with
      ⟨⟨htimeHh, htimeMm, hss⟩, hsss,
        ⟨hoffsetText, hoffsetHh, hoffsetMm⟩, hinput⟩
    have htimeHh' : String.IsFixedDigits 2 timeHh :=
      (fixedDigits_iff 2 (by omega) timeHh).mp htimeHh
    have htimeMm' : String.IsFixedDigits 2 timeMm :=
      (fixedDigits_iff 2 (by omega) timeMm).mp htimeMm
    have hss' : String.IsFixedDigits 2 ss :=
      (fixedDigits_iff 2 (by omega) ss).mp hss
    have hsss' : String.IsFixedDigits 3 sss :=
      (fixedDigits_iff 3 (by omega) sss).mp hsss
    have hoffsetHh' : String.IsFixedDigits 2 offsetHh :=
      (fixedDigits_iff 2 (by omega) offsetHh).mp hoffsetHh
    have hoffsetMm' : String.IsFixedDigits 2 offsetMm :=
      (fixedDigits_iff 2 (by omega) offsetMm).mp hoffsetMm
    rcases hoffsetText with hpositive | hnegative
    · let date : Cedar.Thm.Datetime.DateComponents := ⟨yyyy, mm, dd⟩
      let time : Cedar.Thm.Datetime.TimeComponents :=
        ⟨timeHh, timeMm, ss⟩
      let zoneOffset : Cedar.Thm.Datetime.OffsetComponents :=
        ⟨false, offsetHh, offsetMm⟩
      let timePart : Cedar.Thm.Datetime.TimePart :=
        ⟨time, some sss, .offset zoneOffset⟩
      let components : Cedar.Thm.Datetime.DatetimeComponents :=
        ⟨date, some timePart⟩
      refine ⟨components, ?_, ?_, ?_⟩
      · exact ⟨⟨hyyyy', hmm', hdd'⟩,
          ⟨⟨htimeHh', htimeMm', hss'⟩, hsss',
            ⟨hoffsetHh', hoffsetMm'⟩⟩⟩
      · have hzoneOffsetString :
            zoneOffset.asString = "+" ++ offsetHh ++ offsetMm := by
          simp [zoneOffset, Cedar.Thm.Datetime.OffsetComponents.asString]
        simpa [components, timePart, date, time,
          Cedar.Thm.Datetime.DatetimeComponents.asString,
          Cedar.Thm.Datetime.DateComponents.asString,
          Cedar.Thm.Datetime.TimePart.asString,
          Cedar.Thm.Datetime.TimeComponents.asString,
          Cedar.Thm.Datetime.Zone.asString, dateText, timeText,
          String.append_assoc, hpositive, hzoneOffsetString] using hinput.symm
      · simp [componentsFields, components, timePart, zoneOffset, date, time,
          componentsCaptures, dateCaptures, timeCaptures, offsetCaptures,
          CaptureMap.toEnv, Cedar.Thm.Datetime.OffsetComponents.asString,
          hpositive]
    · let date : Cedar.Thm.Datetime.DateComponents := ⟨yyyy, mm, dd⟩
      let time : Cedar.Thm.Datetime.TimeComponents :=
        ⟨timeHh, timeMm, ss⟩
      let zoneOffset : Cedar.Thm.Datetime.OffsetComponents :=
        ⟨true, offsetHh, offsetMm⟩
      let timePart : Cedar.Thm.Datetime.TimePart :=
        ⟨time, some sss, .offset zoneOffset⟩
      let components : Cedar.Thm.Datetime.DatetimeComponents :=
        ⟨date, some timePart⟩
      refine ⟨components, ?_, ?_, ?_⟩
      · exact ⟨⟨hyyyy', hmm', hdd'⟩,
          ⟨⟨htimeHh', htimeMm', hss'⟩, hsss',
            ⟨hoffsetHh', hoffsetMm'⟩⟩⟩
      · have hzoneOffsetString :
            zoneOffset.asString = "-" ++ offsetHh ++ offsetMm := by
          simp [zoneOffset, Cedar.Thm.Datetime.OffsetComponents.asString]
        simpa [components, timePart, date, time,
          Cedar.Thm.Datetime.DatetimeComponents.asString,
          Cedar.Thm.Datetime.DateComponents.asString,
          Cedar.Thm.Datetime.TimePart.asString,
          Cedar.Thm.Datetime.TimeComponents.asString,
          Cedar.Thm.Datetime.Zone.asString, dateText, timeText,
          String.append_assoc, hnegative, hzoneOffsetString] using hinput.symm
      · simp [componentsFields, components, timePart, zoneOffset, date, time,
          componentsCaptures, dateCaptures, timeCaptures, offsetCaptures,
          CaptureMap.toEnv, Cedar.Thm.Datetime.OffsetComponents.asString,
          hnegative]

theorem date_match_field_specs
    (sequence : Vermilion.Seq Int)
    (view : triptych_datetime_roundtrip.DatetimeView)
    (hmatch :
      triptych_datetime_roundtrip.datetime_matches_Date sequence view) :
    triptych_datetime_roundtrip.datetime_is_wf_MM
        view.get_DatetimeView_mm ∧
      triptych_datetime_roundtrip.datetime_is_wf_YYYY
        view.get_DatetimeView_yyyy ∧
      triptych_datetime_roundtrip.datetime_is_wf_DD
        view.get_DatetimeView_dd := by
  rcases hmatch with ⟨yyyy, mm, dd,
    ⟨⟨⟨_, ⟨hyyyyField, hyyyy⟩⟩, ⟨hmmField, hmm⟩⟩,
      ⟨hddField, hdd⟩⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hmmField]
    simpa [triptych_datetime_roundtrip.datetime_matches_MM,
      triptych_datetime_roundtrip.datetime_is_wf_MM] using hmm
  · rw [hyyyyField]
    simpa [triptych_datetime_roundtrip.datetime_matches_YYYY,
      triptych_datetime_roundtrip.datetime_is_wf_YYYY] using hyyyy
  · rw [hddField]
    simpa [triptych_datetime_roundtrip.datetime_matches_DD,
      triptych_datetime_roundtrip.datetime_is_wf_DD] using hdd

theorem time_match_field_specs
    (sequence : Vermilion.Seq Int)
    (view : triptych_datetime_roundtrip.DatetimeView)
    (hmatch :
      triptych_datetime_roundtrip.datetime_matches_Time sequence view) :
    triptych_datetime_roundtrip.datetime_is_wf_hh
        view.get_DatetimeView_time_hh ∧
      triptych_datetime_roundtrip.datetime_is_wf_mm
        view.get_DatetimeView_time_mm ∧
      triptych_datetime_roundtrip.datetime_is_wf_ss
        view.get_DatetimeView_ss := by
  rcases hmatch with ⟨hh, mm, ss,
    ⟨⟨⟨_, ⟨hhhField, hhh⟩⟩, ⟨hmmField, hmm⟩⟩,
      ⟨hssField, hss⟩⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hhhField]
    simpa [triptych_datetime_roundtrip.datetime_matches_hh,
      triptych_datetime_roundtrip.datetime_is_wf_hh] using hhh
  · rw [hmmField]
    simpa [triptych_datetime_roundtrip.datetime_matches_mm,
      triptych_datetime_roundtrip.datetime_is_wf_mm] using hmm
  · rw [hssField]
    simpa [triptych_datetime_roundtrip.datetime_matches_ss,
      triptych_datetime_roundtrip.datetime_is_wf_ss] using hss

theorem offset_match_is_wf
    (sequence : Vermilion.Seq Int)
    (view : triptych_datetime_roundtrip.DatetimeView)
    (hmatch :
      triptych_datetime_roundtrip.datetime_matches_Offset sequence view) :
    triptych_datetime_roundtrip.datetime_is_wf_Offset sequence := by
  rcases hmatch with
    ⟨hh, mm, ⟨⟨hsequence, ⟨_, hhh⟩⟩, ⟨_, hmm⟩⟩⟩ |
    ⟨hh, mm, ⟨⟨hsequence, ⟨_, hhh⟩⟩, ⟨_, hmm⟩⟩⟩
  · exact Or.inl ⟨hh, mm, ⟨⟨hsequence, by
      simpa [triptych_datetime_roundtrip.datetime_matches_hh,
        triptych_datetime_roundtrip.datetime_is_wf_hh] using hhh⟩, by
      simpa [triptych_datetime_roundtrip.datetime_matches_mm,
        triptych_datetime_roundtrip.datetime_is_wf_mm] using hmm⟩⟩
  · exact Or.inr ⟨hh, mm, ⟨⟨hsequence, by
      simpa [triptych_datetime_roundtrip.datetime_matches_hh,
        triptych_datetime_roundtrip.datetime_is_wf_hh] using hhh⟩, by
      simpa [triptych_datetime_roundtrip.datetime_matches_mm,
        triptych_datetime_roundtrip.datetime_is_wf_mm] using hmm⟩⟩

theorem offset_match_field_specs
    (sequence : Vermilion.Seq Int)
    (view : triptych_datetime_roundtrip.DatetimeView)
    (hmatch :
      triptych_datetime_roundtrip.datetime_matches_Offset sequence view) :
    triptych_datetime_roundtrip.datetime_is_wf_hh
        view.get_DatetimeView_offset_hh ∧
      triptych_datetime_roundtrip.datetime_is_wf_mm
        view.get_DatetimeView_offset_mm := by
  rcases hmatch with
    ⟨hh, mm, ⟨⟨_, ⟨hhhField, hhh⟩⟩, ⟨hmmField, hmm⟩⟩⟩ |
    ⟨hh, mm, ⟨⟨_, ⟨hhhField, hhh⟩⟩, ⟨hmmField, hmm⟩⟩⟩
  all_goals
    constructor
    · rw [hhhField]
      simpa [triptych_datetime_roundtrip.datetime_matches_hh,
        triptych_datetime_roundtrip.datetime_is_wf_hh] using hhh
    · rw [hmmField]
      simpa [triptych_datetime_roundtrip.datetime_matches_mm,
        triptych_datetime_roundtrip.datetime_is_wf_mm] using hmm

theorem view_field_specs
    (input : Vermilion.Seq Int)
    (view : triptych_datetime_roundtrip.DatetimeView)
    (hmatch :
      triptych_datetime_roundtrip.datetime_matches_Datetime input view) :
    triptych_datetime_roundtrip.datetime_is_wf_MM view.get_DatetimeView_mm ∧
      triptych_datetime_roundtrip.datetime_is_wf_YYYY
        view.get_DatetimeView_yyyy ∧
      triptych_datetime_roundtrip.datetime_is_wf_DD view.get_DatetimeView_dd ∧
      (view.get_DatetimeView_time_hh = Vermilion.Seq.empty ∨
        triptych_datetime_roundtrip.datetime_is_wf_hh
          view.get_DatetimeView_time_hh) ∧
      (view.get_DatetimeView_time_mm = Vermilion.Seq.empty ∨
        triptych_datetime_roundtrip.datetime_is_wf_mm
          view.get_DatetimeView_time_mm) ∧
      (view.get_DatetimeView_ss = Vermilion.Seq.empty ∨
        triptych_datetime_roundtrip.datetime_is_wf_ss
          view.get_DatetimeView_ss) ∧
      (view.get_DatetimeView_sss = Vermilion.Seq.empty ∨
        triptych_datetime_roundtrip.datetime_is_wf_SSS
          view.get_DatetimeView_sss) ∧
      (view.get_DatetimeView_offset = Vermilion.Seq.empty ∨
        triptych_datetime_roundtrip.datetime_is_wf_Offset
          view.get_DatetimeView_offset) ∧
      (view.get_DatetimeView_offset_hh = Vermilion.Seq.empty ∨
        triptych_datetime_roundtrip.datetime_is_wf_hh
          view.get_DatetimeView_offset_hh) ∧
      (view.get_DatetimeView_offset_mm = Vermilion.Seq.empty ∨
        triptych_datetime_roundtrip.datetime_is_wf_mm
          view.get_DatetimeView_offset_mm) := by
  rcases hmatch with ((((hbare | hutc) | hmillisUtc) | hoffsetOnly) |
    hmillisOffset)
  · rcases hbare with ⟨date, ⟨⟨⟨⟨⟨⟨⟨⟨_, hdate⟩, htimeHh⟩,
      htimeMm⟩, hss⟩, hsss⟩, hoffset⟩, hoffsetHh⟩, hoffsetMm⟩⟩
    have hfields := date_match_field_specs date view hdate
    exact ⟨hfields.1, hfields.2.1, hfields.2.2,
      Or.inl htimeHh, Or.inl htimeMm, Or.inl hss, Or.inl hsss,
      Or.inl hoffset, Or.inl hoffsetHh, Or.inl hoffsetMm⟩
  · rcases hutc with ⟨date, time,
      ⟨⟨⟨⟨⟨⟨_, hdate⟩, htime⟩, hsss⟩, hoffset⟩,
        hoffsetHh⟩, hoffsetMm⟩⟩
    have hdateFields := date_match_field_specs date view hdate
    have htimeFields := time_match_field_specs time view htime
    exact ⟨hdateFields.1, hdateFields.2.1, hdateFields.2.2,
      Or.inr htimeFields.1, Or.inr htimeFields.2.1,
      Or.inr htimeFields.2.2, Or.inl hsss, Or.inl hoffset,
      Or.inl hoffsetHh, Or.inl hoffsetMm⟩
  · rcases hmillisUtc with ⟨date, time, sss,
      ⟨⟨⟨⟨⟨⟨_, hdate⟩, htime⟩, ⟨hsssField, hsssMatch⟩⟩,
        hoffset⟩, hoffsetHh⟩, hoffsetMm⟩⟩
    have hdateFields := date_match_field_specs date view hdate
    have htimeFields := time_match_field_specs time view htime
    have hsssWf :
        triptych_datetime_roundtrip.datetime_is_wf_SSS
          view.get_DatetimeView_sss := by
      rw [hsssField]
      exact (matches_sss_is_wf sss view).1 hsssMatch
    exact ⟨hdateFields.1, hdateFields.2.1, hdateFields.2.2,
      Or.inr htimeFields.1, Or.inr htimeFields.2.1,
      Or.inr htimeFields.2.2, Or.inr hsssWf, Or.inl hoffset,
      Or.inl hoffsetHh, Or.inl hoffsetMm⟩
  · rcases hoffsetOnly with ⟨date, time, offset,
      ⟨⟨⟨⟨_, hdate⟩, htime⟩, ⟨hoffsetField, hoffsetMatch⟩⟩,
        hsss⟩⟩
    have hdateFields := date_match_field_specs date view hdate
    have htimeFields := time_match_field_specs time view htime
    have hoffsetFields := offset_match_field_specs offset view hoffsetMatch
    have hoffsetWf :
        triptych_datetime_roundtrip.datetime_is_wf_Offset
          view.get_DatetimeView_offset := by
      rw [hoffsetField]
      exact offset_match_is_wf offset view hoffsetMatch
    exact ⟨hdateFields.1, hdateFields.2.1, hdateFields.2.2,
      Or.inr htimeFields.1, Or.inr htimeFields.2.1,
      Or.inr htimeFields.2.2, Or.inl hsss, Or.inr hoffsetWf,
      Or.inr hoffsetFields.1, Or.inr hoffsetFields.2⟩
  · rcases hmillisOffset with ⟨date, time, sss, offset,
      ⟨⟨⟨⟨_, hdate⟩, htime⟩, ⟨hsssField, hsssMatch⟩⟩,
        ⟨hoffsetField, hoffsetMatch⟩⟩⟩
    have hdateFields := date_match_field_specs date view hdate
    have htimeFields := time_match_field_specs time view htime
    have hoffsetFields := offset_match_field_specs offset view hoffsetMatch
    have hsssWf :
        triptych_datetime_roundtrip.datetime_is_wf_SSS
          view.get_DatetimeView_sss := by
      rw [hsssField]
      exact (matches_sss_is_wf sss view).1 hsssMatch
    have hoffsetWf :
        triptych_datetime_roundtrip.datetime_is_wf_Offset
          view.get_DatetimeView_offset := by
      rw [hoffsetField]
      exact offset_match_is_wf offset view hoffsetMatch
    exact ⟨hdateFields.1, hdateFields.2.1, hdateFields.2.2,
      Or.inr htimeFields.1, Or.inr htimeFields.2.1,
      Or.inr htimeFields.2.2, Or.inr hsssWf, Or.inr hoffsetWf,
      Or.inr hoffsetFields.1, Or.inr hoffsetFields.2⟩

theorem decode_datetime_optional_fixed_digits
    (sequence : Vermilion.Seq Int) (width : Nat)
    (hwf :
      sequence = Vermilion.Seq.empty ∨
        ∃ digits : Vermilion.Seq Int,
          sequence = digits ∧
            Vermilion.Seq.len digits = Int.ofNat width ∧
            ∀ index : Int,
              0 ≤ index ∧ index < Vermilion.Seq.len digits →
              triptych_datetime_roundtrip.triptych_is_digit
                  (Vermilion.Seq.index digits index)) :
    ∃ text : String, sequence = encodeString text := by
  apply Triptych.Vermilion.String.decode_optional_fixed_digits
  rcases hwf with hempty | hfixed
  · exact Or.inl hempty
  · exact Or.inr (by
      simpa [triptych_datetime_roundtrip.triptych_is_digit, IsDigitCode] using
        hfixed)

theorem decode_optional_offset
    (sequence : Vermilion.Seq Int)
    (hwf :
      sequence = Vermilion.Seq.empty ∨
        triptych_datetime_roundtrip.datetime_is_wf_Offset sequence) :
    ∃ text : String, sequence = encodeString text := by
  rcases hwf with hempty | hoffset
  · subst sequence
    exact ⟨"", by simp [encodeString, Vermilion.Seq.empty]⟩
  · obtain ⟨text, hencode, _⟩ := decode_offset_text sequence hoffset
    exact ⟨text, hencode⟩

theorem normalize_matching_view (input : String)
    (condition : triptych_datetime_roundtrip.DatetimeView → Prop) :
    (∃ view : triptych_datetime_roundtrip.DatetimeView,
      triptych_datetime_roundtrip.datetime_matches_view
          (encodeString input) view ∧
        condition view) ↔
      ∃ mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm : String,
        triptych_datetime_roundtrip.datetime_matches_view
            (encodeString input)
            (.DatetimeView (encodeString input) (encodeString mm)
              (encodeString yyyy) (encodeString dd) (encodeString timeHh)
              (encodeString timeMm) (encodeString ss) (encodeString sss)
              (encodeString offset) (encodeString offsetHh)
              (encodeString offsetMm)) ∧
          condition
            (.DatetimeView (encodeString input) (encodeString mm)
              (encodeString yyyy) (encodeString dd) (encodeString timeHh)
              (encodeString timeMm) (encodeString ss) (encodeString sss)
              (encodeString offset) (encodeString offsetHh)
              (encodeString offsetMm)) := by
  constructor
  · rintro ⟨view, hmatch, hcondition⟩
    cases view with
    | DatetimeView viewInput mmSequence yyyySequence ddSequence
        timeHhSequence timeMmSequence ssSequence sssSequence offsetSequence
        offsetHhSequence offsetMmSequence =>
      rcases hmatch with ⟨hviewInput, hgrammar⟩
      simp only [
        triptych_datetime_roundtrip.DatetimeView.get_DatetimeView_input]
          at hviewInput
      subst viewInput
      rcases view_field_specs (encodeString input)
          (.DatetimeView (encodeString input) mmSequence yyyySequence
            ddSequence timeHhSequence timeMmSequence ssSequence sssSequence
            offsetSequence offsetHhSequence offsetMmSequence)
          hgrammar with
        ⟨hmmSpec, hyyyySpec, hddSpec, htimeHhSpec, htimeMmSpec, hssSpec,
          hsssSpec, hoffsetSpec, hoffsetHhSpec, hoffsetMmSpec⟩
      obtain ⟨mm, hmmEncode, _⟩ :=
        decode_datetime_fixed_digits mmSequence 2 (by
          simpa [triptych_datetime_roundtrip.datetime_is_wf_MM] using
            hmmSpec)
      obtain ⟨yyyy, hyyyyEncode, _⟩ :=
        decode_datetime_fixed_digits yyyySequence 4 (by
          simpa [triptych_datetime_roundtrip.datetime_is_wf_YYYY] using
            hyyyySpec)
      obtain ⟨dd, hddEncode, _⟩ :=
        decode_datetime_fixed_digits ddSequence 2 (by
          simpa [triptych_datetime_roundtrip.datetime_is_wf_DD] using
            hddSpec)
      obtain ⟨timeHh, htimeHhEncode⟩ :=
        decode_datetime_optional_fixed_digits timeHhSequence 2 (by
          rcases htimeHhSpec with hempty | hwf
          · exact Or.inl hempty
          · exact Or.inr (by
              simpa [triptych_datetime_roundtrip.datetime_is_wf_hh] using
                hwf))
      obtain ⟨timeMm, htimeMmEncode⟩ :=
        decode_datetime_optional_fixed_digits timeMmSequence 2 (by
          rcases htimeMmSpec with hempty | hwf
          · exact Or.inl hempty
          · exact Or.inr (by
              simpa [triptych_datetime_roundtrip.datetime_is_wf_mm] using
                hwf))
      obtain ⟨ss, hssEncode⟩ :=
        decode_datetime_optional_fixed_digits ssSequence 2 (by
          rcases hssSpec with hempty | hwf
          · exact Or.inl hempty
          · exact Or.inr (by
              simpa [triptych_datetime_roundtrip.datetime_is_wf_ss] using
                hwf))
      obtain ⟨sss, hsssEncode⟩ :=
        decode_datetime_optional_fixed_digits sssSequence 3 (by
          rcases hsssSpec with hempty | hwf
          · exact Or.inl hempty
          · exact Or.inr (by
              simpa [triptych_datetime_roundtrip.datetime_is_wf_SSS] using
                hwf))
      obtain ⟨offset, hoffsetEncode⟩ :=
        decode_optional_offset offsetSequence hoffsetSpec
      obtain ⟨offsetHh, hoffsetHhEncode⟩ :=
        decode_datetime_optional_fixed_digits offsetHhSequence 2 (by
          rcases hoffsetHhSpec with hempty | hwf
          · exact Or.inl hempty
          · exact Or.inr (by
              simpa [triptych_datetime_roundtrip.datetime_is_wf_hh] using
                hwf))
      obtain ⟨offsetMm, hoffsetMmEncode⟩ :=
        decode_datetime_optional_fixed_digits offsetMmSequence 2 (by
          rcases hoffsetMmSpec with hempty | hwf
          · exact Or.inl hempty
          · exact Or.inr (by
              simpa [triptych_datetime_roundtrip.datetime_is_wf_mm] using
                hwf))
      refine ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
        offsetMm, ?_, ?_⟩
      · have hmatch' :
            triptych_datetime_roundtrip.datetime_matches_view
              (encodeString input)
              (.DatetimeView (encodeString input) mmSequence yyyySequence
                ddSequence timeHhSequence timeMmSequence ssSequence
                sssSequence offsetSequence offsetHhSequence
                offsetMmSequence) :=
          ⟨rfl, hgrammar⟩
        simpa only [hmmEncode, hyyyyEncode, hddEncode, htimeHhEncode,
          htimeMmEncode, hssEncode, hsssEncode, hoffsetEncode,
          hoffsetHhEncode, hoffsetMmEncode] using hmatch'
      · simpa only [hmmEncode, hyyyyEncode, hddEncode, htimeHhEncode,
          htimeMmEncode, hssEncode, hsssEncode, hoffsetEncode,
          hoffsetHhEncode, hoffsetMmEncode] using hcondition
  · rintro ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, hmatch, hcondition⟩
    exact ⟨.DatetimeView (encodeString input) (encodeString mm)
      (encodeString yyyy) (encodeString dd) (encodeString timeHh)
      (encodeString timeMm) (encodeString ss) (encodeString sss)
      (encodeString offset) (encodeString offsetHh) (encodeString offsetMm),
      hmatch, hcondition⟩

theorem natFrom_eq_fold (bytes : List Int) (index : Nat)
    (accumulator : Int) (hindex : index ≤ bytes.length) :
    triptych_datetime_roundtrip.triptych_nat_of_from
        bytes (Int.ofNat index) accumulator =
      (bytes.drop index).foldl
        (fun current byte => current * 10 + recoveredDigit byte)
        accumulator := by
  apply Triptych.Vermilion.String.natFrom_eq_fold
    triptych_datetime_roundtrip.triptych_nat_of_from
  · intro stepBytes stepIndex stepAccumulator hrange
    rw [triptych_datetime_roundtrip.triptych_nat_of_from, dif_pos hrange]
    rfl
  · exact hindex

theorem natOf_equiv (source : String) :
    triptych_datetime_roundtrip.triptych_nat_of (encodeString source) =
      Triptych.natOf source := by
  unfold triptych_datetime_roundtrip.triptych_nat_of
  change triptych_datetime_roundtrip.triptych_nat_of_from
      (encodeString source) (Int.ofNat 0) 0 = Triptych.natOf source
  rw [natFrom_eq_fold _ 0 0 (Nat.zero_le _)]
  simpa using encodedDigitFold_eq_natOf source

theorem signOf_equiv (source : String) :
    triptych_datetime_roundtrip.triptych_sign_of (encodeString source) =
      Triptych.signOf source := by
  simpa [triptych_datetime_roundtrip.triptych_sign_of,
    triptych_datetime_roundtrip.TRIPTYCH_MINUS, recoveredSignOf] using
      recoveredSignOf_encodeString source

theorem natOf_emod_4 (source : String) :
    Triptych.natOf source % (4 : Int) =
      Int.tmod (Triptych.natOf source) 4 := by
  simpa using natOf_emod_eq_tmod source 4

theorem natOf_emod_100 (source : String) :
    Triptych.natOf source % (100 : Int) =
      Int.tmod (Triptych.natOf source) 100 := by
  simpa using natOf_emod_eq_tmod source 100

theorem natOf_emod_400 (source : String) :
    Triptych.natOf source % (400 : Int) =
      Int.tmod (Triptych.natOf source) 400 := by
  simpa using natOf_emod_eq_tmod source 400

theorem rust_div_eq_tdiv (a b : Int) (hb : 0 < b) :
    vstd.arithmetic.div_mod.rust_div a b = Int.tdiv a b := by
  cases a with
  | ofNat m =>
      cases b with
      | ofNat n =>
          have hn : n ≠ 0 := by
            intro hn
            subst n
            simp at hb
          cases m with
          | zero =>
              simp [vstd.arithmetic.div_mod.rust_div, Vermilion.iteP]
          | succ m =>
              have ha : (0 : Int) < Int.ofNat (Nat.succ m) := by simp
              unfold vstd.arithmetic.div_mod.rust_div
              rw [Vermilion.iteP_neg (ne_of_gt ha),
                Vermilion.iteP_pos ha]
              simp [Vermilion.ediv, Int.tdiv, hn]
      | negSucc n => omega
  | negSucc m =>
      cases b with
      | ofNat n =>
          have hn : n ≠ 0 := by
            intro hn
            subst n
            simp at hb
          simp [vstd.arithmetic.div_mod.rust_div, Vermilion.iteP,
            Vermilion.ediv, Int.tdiv, hn]
      | negSucc n => omega

theorem rust_div_400 (a : Int) :
    vstd.arithmetic.div_mod.rust_div a 400 = Int.tdiv a 400 :=
  rust_div_eq_tdiv a 400 (by norm_num)

theorem rust_div_100 (a : Int) :
    vstd.arithmetic.div_mod.rust_div a 100 = Int.tdiv a 100 :=
  rust_div_eq_tdiv a 100 (by norm_num)

theorem rust_div_5 (a : Int) :
    vstd.arithmetic.div_mod.rust_div a 5 = Int.tdiv a 5 :=
  rust_div_eq_tdiv a 5 (by norm_num)

theorem rust_div_4 (a : Int) :
    vstd.arithmetic.div_mod.rust_div a 4 = Int.tdiv a 4 :=
  rust_div_eq_tdiv a 4 (by norm_num)

theorem datetime_value_equiv
    (mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm : String) :
    Datetime.value mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm =
      triptych_datetime_roundtrip.datetime_value
        (encodeString mm) (encodeString yyyy) (encodeString dd)
        (encodeString timeHh) (encodeString timeMm) (encodeString ss)
        (encodeString sss) (encodeString offset) (encodeString offsetHh)
        (encodeString offsetMm) := by
  unfold Datetime.value triptych_datetime_roundtrip.datetime_value
  rw [natOf_equiv, natOf_equiv, natOf_equiv, natOf_equiv, natOf_equiv,
    natOf_equiv, natOf_equiv, signOf_equiv, natOf_equiv, natOf_equiv]
  simp [rust_div_400, rust_div_4, rust_div_100, rust_div_5,
    Vermilion.iteP]

theorem datetime_wf_constraints_equiv
    (mm timeHh timeMm ss offsetHh offsetMm dd yyyy : String) :
    Datetime.WfConstraints mm timeHh timeMm ss offsetHh offsetMm dd yyyy ↔
      triptych_datetime_roundtrip.datetime_wf_constraints
        (encodeString mm) (encodeString timeHh) (encodeString timeMm)
        (encodeString ss) (encodeString offsetHh) (encodeString offsetMm)
        (encodeString dd) (encodeString yyyy) := by
  unfold Datetime.WfConstraints
    triptych_datetime_roundtrip.datetime_wf_constraints
  rw [natOf_equiv, natOf_equiv, natOf_equiv, natOf_equiv, natOf_equiv,
    natOf_equiv, natOf_equiv, natOf_equiv]
  simp only [natOf_emod_4 yyyy, natOf_emod_100 yyyy,
    natOf_emod_400 yyyy]
  simp only [Vermilion.iteP]
  split_ifs <;> simp_all

theorem datetime_constraints_equiv
    (mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm : String) :
    Datetime.Constraints mm yyyy dd timeHh timeMm ss sss offset offsetHh
        offsetMm ↔
      triptych_datetime_roundtrip.datetime_constraints
        (encodeString mm) (encodeString yyyy) (encodeString dd)
        (encodeString timeHh) (encodeString timeMm) (encodeString ss)
        (encodeString sss) (encodeString offset) (encodeString offsetHh)
        (encodeString offsetMm) := by
  unfold Datetime.Constraints triptych_datetime_roundtrip.datetime_constraints
  rw [← datetime_value_equiv mm yyyy dd timeHh timeMm ss sss offset
    offsetHh offsetMm]
  norm_num

theorem decoded_components (input : String)
    (hwf : Datetime.IsWf.Datetime input) :
    ∃ components : Cedar.Thm.Datetime.DatetimeComponents,
      decode Datetime.grammar input = some (componentsCaptures components) ∧
        components.syntaxWf ∧ components.asString = input := by
  have hgrammar : Triptych.IsWf Datetime.grammar input :=
    (Datetime.IsWfGrammar_equiv input).2 hwf
  have hsome : (decode Datetime.grammar input).isSome = true :=
    (decodeSome_iff_IsWf Datetime.grammar (by decide) input).2 hgrammar
  obtain ⟨captures, hdecode⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨components, hcaptures, hinput, hsyntax⟩ :=
    components_of_decode hdecode
  subst captures
  exact ⟨components, hdecode, hsyntax, hinput.symm⟩

theorem source_wf_constraints_of_parts
    (input mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm :
      String)
    (hwf : Datetime.IsWf.Datetime input)
    (hparts :
      datetimeParts input mm yyyy dd timeHh timeMm ss sss offset offsetHh
        offsetMm) :
    Datetime.SatisfiesWfConstraints input ↔
      Datetime.WfConstraints mm timeHh timeMm ss offsetHh offsetMm dd yyyy := by
  obtain ⟨supplied, hsuppliedSyntax, hsuppliedInput, hfields⟩ :=
    components_of_datetime_parts input mm yyyy dd timeHh timeMm ss sss
      offset offsetHh offsetMm hparts
  obtain ⟨decoded, hdecode, hdecodedSyntax, hdecodedInput⟩ :=
    decoded_components input hwf
  have hcomponents : decoded = supplied :=
    components_eq_of_asString hdecodedSyntax hsuppliedSyntax
      (hdecodedInput.trans hsuppliedInput.symm)
  subst decoded
  rw [Datetime.SatisfiesWfConstraints_of_decode hdecode]
  rcases hfields with
    ⟨hmm, hyyyy, hdd, htimeHh, htimeMm, hss, hsss, hoffset, hoffsetHh,
      hoffsetMm⟩
  rw [hmm, htimeHh, htimeMm, hss, hoffsetHh, hoffsetMm, hdd, hyyyy]

theorem source_constraints_of_parts
    (input mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm :
      String)
    (hwf : Datetime.IsWf.Datetime input)
    (hparts :
      datetimeParts input mm yyyy dd timeHh timeMm ss sss offset offsetHh
        offsetMm) :
    Datetime.SatisfiesConstraints input ↔
      Datetime.Constraints mm yyyy dd timeHh timeMm ss sss offset offsetHh
        offsetMm := by
  obtain ⟨supplied, hsuppliedSyntax, hsuppliedInput, hfields⟩ :=
    components_of_datetime_parts input mm yyyy dd timeHh timeMm ss sss
      offset offsetHh offsetMm hparts
  obtain ⟨decoded, hdecode, hdecodedSyntax, hdecodedInput⟩ :=
    decoded_components input hwf
  have hcomponents : decoded = supplied :=
    components_eq_of_asString hdecodedSyntax hsuppliedSyntax
      (hdecodedInput.trans hsuppliedInput.symm)
  subst decoded
  rw [Datetime.SatisfiesConstraints_of_decode hdecode]
  rcases hfields with
    ⟨hmm, hyyyy, hdd, htimeHh, htimeMm, hss, hsss, hoffset, hoffsetHh,
      hoffsetMm⟩
  rw [hmm, hyyyy, hdd, htimeHh, htimeMm, hss, hsss, hoffset, hoffsetHh,
    hoffsetMm]

theorem source_satisfies_wf_constraints_parts (input : String)
    (hwf : Datetime.IsWf.Datetime input) :
    Datetime.SatisfiesWfConstraints input ↔
      ∃ mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm : String,
        datetimeParts input mm yyyy dd timeHh timeMm ss sss offset offsetHh
            offsetMm ∧
          Datetime.WfConstraints mm timeHh timeMm ss offsetHh offsetMm dd
            yyyy := by
  constructor
  · intro hconstraints
    obtain ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, hparts⟩ := (datetime_parts_exists_equiv input).1 hwf
    exact ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, hparts,
      (source_wf_constraints_of_parts input mm yyyy dd timeHh timeMm ss sss
        offset offsetHh offsetMm hwf hparts).1 hconstraints⟩
  · rintro ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, hparts, hconstraints⟩
    exact
      (source_wf_constraints_of_parts input mm yyyy dd timeHh timeMm ss sss
        offset offsetHh offsetMm hwf hparts).2 hconstraints

theorem source_satisfies_constraints_parts (input : String)
    (hwf : Datetime.IsWf.Datetime input) :
    Datetime.SatisfiesConstraints input ↔
      ∃ mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm : String,
        datetimeParts input mm yyyy dd timeHh timeMm ss sss offset offsetHh
            offsetMm ∧
          Datetime.Constraints mm yyyy dd timeHh timeMm ss sss offset
            offsetHh offsetMm := by
  constructor
  · intro hconstraints
    obtain ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, hparts⟩ := (datetime_parts_exists_equiv input).1 hwf
    exact ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, hparts,
      (source_constraints_of_parts input mm yyyy dd timeHh timeMm ss sss
        offset offsetHh offsetMm hwf hparts).1 hconstraints⟩
  · rintro ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, hparts, hconstraints⟩
    exact
      (source_constraints_of_parts input mm yyyy dd timeHh timeMm ss sss
        offset offsetHh offsetMm hwf hparts).2 hconstraints

theorem datetime_satisfies_wf_constraints_equiv (input : String)
    (hwf : Datetime.IsWf.Datetime input) :
    Datetime.SatisfiesWfConstraints input ↔
      triptych_datetime_roundtrip.datetime_satisfies_wf_constraints
        (encodeString input) := by
  rw [source_satisfies_wf_constraints_parts input hwf]
  unfold triptych_datetime_roundtrip.datetime_satisfies_wf_constraints
  rw [normalize_matching_view input
    triptych_datetime_roundtrip.datetime_view_wf_constraints]
  constructor
  · rintro ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, hparts, hconstraints⟩
    refine ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, (matches_view_equiv input mm yyyy dd timeHh timeMm ss sss
        offset offsetHh offsetMm).2 hparts, ?_⟩
    change triptych_datetime_roundtrip.datetime_wf_constraints
      (encodeString mm) (encodeString timeHh) (encodeString timeMm)
      (encodeString ss) (encodeString offsetHh) (encodeString offsetMm)
      (encodeString dd) (encodeString yyyy)
    exact (datetime_wf_constraints_equiv mm timeHh timeMm ss offsetHh
      offsetMm dd yyyy).1 hconstraints
  · rintro ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, hmatch, hconstraints⟩
    refine ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, (matches_view_equiv input mm yyyy dd timeHh timeMm ss sss
        offset offsetHh offsetMm).1 hmatch, ?_⟩
    change triptych_datetime_roundtrip.datetime_wf_constraints
      (encodeString mm) (encodeString timeHh) (encodeString timeMm)
      (encodeString ss) (encodeString offsetHh) (encodeString offsetMm)
      (encodeString dd) (encodeString yyyy) at hconstraints
    exact (datetime_wf_constraints_equiv mm timeHh timeMm ss offsetHh
      offsetMm dd yyyy).2 hconstraints

theorem datetime_satisfies_constraints_equiv (input : String)
    (hwf : Datetime.IsWf.Datetime input) :
    Datetime.SatisfiesConstraints input ↔
      triptych_datetime_roundtrip.datetime_satisfies_constraints
        (encodeString input) := by
  rw [source_satisfies_constraints_parts input hwf]
  unfold triptych_datetime_roundtrip.datetime_satisfies_constraints
  rw [normalize_matching_view input
    triptych_datetime_roundtrip.datetime_view_constraints]
  constructor
  · rintro ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, hparts, hconstraints⟩
    refine ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, (matches_view_equiv input mm yyyy dd timeHh timeMm ss sss
        offset offsetHh offsetMm).2 hparts, ?_⟩
    change triptych_datetime_roundtrip.datetime_constraints
      (encodeString mm) (encodeString yyyy) (encodeString dd)
      (encodeString timeHh) (encodeString timeMm) (encodeString ss)
      (encodeString sss) (encodeString offset) (encodeString offsetHh)
      (encodeString offsetMm)
    exact (datetime_constraints_equiv mm yyyy dd timeHh timeMm ss sss offset
      offsetHh offsetMm).1 hconstraints
  · rintro ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, hmatch, hconstraints⟩
    refine ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, (matches_view_equiv input mm yyyy dd timeHh timeMm ss sss
        offset offsetHh offsetMm).1 hmatch, ?_⟩
    change triptych_datetime_roundtrip.datetime_constraints
      (encodeString mm) (encodeString yyyy) (encodeString dd)
      (encodeString timeHh) (encodeString timeMm) (encodeString ss)
      (encodeString sss) (encodeString offset) (encodeString offsetHh)
      (encodeString offsetMm) at hconstraints
    exact (datetime_constraints_equiv mm yyyy dd timeHh timeMm ss sss offset
      offsetHh offsetMm).2 hconstraints

theorem datetime_is_wf_equiv (input : String) :
    Datetime.IsWf input ↔
      triptych_datetime_roundtrip.datetime_is_wf (encodeString input) := by
  change
    (Datetime.IsWf.Datetime input ∧ Datetime.SatisfiesWfConstraints input) ↔
      (triptych_datetime_roundtrip.datetime_is_wf_Datetime
          (encodeString input) ∧
        triptych_datetime_roundtrip.datetime_satisfies_wf_constraints
          (encodeString input))
  constructor
  · rintro ⟨hgrammar, hconstraints⟩
    exact ⟨(datetime_equiv input).1 hgrammar,
      (datetime_satisfies_wf_constraints_equiv input hgrammar).1
        hconstraints⟩
  · rintro ⟨hgrammar, hconstraints⟩
    have hsourceGrammar := (datetime_equiv input).2 hgrammar
    exact ⟨hsourceGrammar,
      (datetime_satisfies_wf_constraints_equiv input hsourceGrammar).2
        hconstraints⟩

theorem datetime_is_valid_equiv (input : String) :
    Datetime.IsValid input ↔
      triptych_datetime_roundtrip.datetime_is_valid (encodeString input) := by
  change
    (Datetime.IsWf input ∧ Datetime.SatisfiesConstraints input) ↔
      (triptych_datetime_roundtrip.datetime_is_wf (encodeString input) ∧
        triptych_datetime_roundtrip.datetime_satisfies_constraints
          (encodeString input))
  constructor
  · rintro ⟨hwellFormed, hconstraints⟩
    exact ⟨(datetime_is_wf_equiv input).1 hwellFormed,
      (datetime_satisfies_constraints_equiv input hwellFormed.1).1
        hconstraints⟩
  · rintro ⟨hwellFormed, hconstraints⟩
    have hsourceWf := (datetime_is_wf_equiv input).2 hwellFormed
    exact ⟨hsourceWf,
      (datetime_satisfies_constraints_equiv input hsourceWf.1).2
        hconstraints⟩

theorem components_of_parts
    (input mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm :
      String)
    (hparts :
      datetimeParts input mm yyyy dd timeHh timeMm ss sss offset offsetHh
        offsetMm) :
    Triptych.component Datetime.grammar input "MM" = mm ∧
      Triptych.component Datetime.grammar input "YYYY" = yyyy ∧
      Triptych.component Datetime.grammar input "DD" = dd ∧
      Triptych.component Datetime.grammar input "Time.hh" = timeHh ∧
      Triptych.component Datetime.grammar input "Time.mm" = timeMm ∧
      Triptych.component Datetime.grammar input "ss" = ss ∧
      Triptych.component Datetime.grammar input "SSS" = sss ∧
      Triptych.component Datetime.grammar input "Offset" = offset ∧
      Triptych.component Datetime.grammar input "Offset.hh" = offsetHh ∧
      Triptych.component Datetime.grammar input "Offset.mm" = offsetMm := by
  obtain ⟨components, hsyntax, hrender, hfields⟩ :=
    components_of_datetime_parts input mm yyyy dd timeHh timeMm ss sss
      offset offsetHh offsetMm hparts
  have hgrammar : Datetime.IsWf.Datetime input :=
    (datetime_parts_exists_equiv input).2
      ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh, offsetMm,
        hparts⟩
  have hengine : Triptych.IsWf Datetime.grammar input :=
    (Datetime.IsWfGrammar_equiv input).mpr hgrammar
  have hsome : (decode Datetime.grammar input).isSome = true :=
    (decodeSome_iff_IsWf Datetime.grammar (by decide) input).mpr hengine
  obtain ⟨captures, hdecode⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨decoded, hcaptures, hdecodedInput, hdecodedSyntax⟩ :=
    Datetime.GrammarView.components_of_decode hdecode
  have heq : components = decoded :=
    Datetime.GrammarView.components_eq_of_asString hsyntax hdecodedSyntax
      (hrender.trans hdecodedInput)
  rw [← heq] at hcaptures
  rw [hcaptures] at hdecode
  rcases hfields with
    ⟨hmm, hyyyy, hdd, htimeHh, htimeMm, hss, hsss, hoffset, hoffsetHh,
      hoffsetMm⟩
  exact
    ⟨(Triptych.component_eq_of_decode hdecode "MM").trans hmm,
      (Triptych.component_eq_of_decode hdecode "YYYY").trans hyyyy,
      (Triptych.component_eq_of_decode hdecode "DD").trans hdd,
      (Triptych.component_eq_of_decode hdecode "Time.hh").trans htimeHh,
      (Triptych.component_eq_of_decode hdecode "Time.mm").trans htimeMm,
      (Triptych.component_eq_of_decode hdecode "ss").trans hss,
      (Triptych.component_eq_of_decode hdecode "SSS").trans hsss,
      (Triptych.component_eq_of_decode hdecode "Offset").trans hoffset,
      (Triptych.component_eq_of_decode hdecode "Offset.hh").trans hoffsetHh,
      (Triptych.component_eq_of_decode hdecode "Offset.mm").trans hoffsetMm⟩

theorem compute_value_of_parts
    (input mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm :
      String)
    (hparts :
      datetimeParts input mm yyyy dd timeHh timeMm ss sss offset offsetHh
        offsetMm) :
    Datetime.computeValue input =
      some (Datetime.value mm yyyy dd timeHh timeMm ss sss offset offsetHh
        offsetMm) := by
  obtain ⟨hmm, hyyyy, hdd, htimeHh, htimeMm, hss, hsss, hoffset,
      hoffsetHh, hoffsetMm⟩ :=
    components_of_parts input mm yyyy dd timeHh timeMm ss sss offset
      offsetHh offsetMm hparts
  have hgrammar : Datetime.IsWf.Datetime input :=
    (datetime_parts_exists_equiv input).2
      ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh, offsetMm,
        hparts⟩
  have hengine : Triptych.IsWf Datetime.grammar input :=
    (Datetime.IsWfGrammar_equiv input).mpr hgrammar
  have hsome : (decode Datetime.grammar input).isSome = true :=
    (decodeSome_iff_IsWf Datetime.grammar (by decide) input).mpr hengine
  obtain ⟨captures, hdecode⟩ := Option.isSome_iff_exists.mp hsome
  rw [Datetime.computeValue_eq, hdecode]
  simpa only [Option.map_some, hmm, hyyyy, hdd, htimeHh, htimeMm, hss,
    hsss, hoffset, hoffsetHh, hoffsetMm]

theorem view_denotation_equiv :
    ∀ input s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : String, Recovered.datetime_view_denotation (Recovered.mkDatetimeView (encodeString input) (encodeString s0) (encodeString s1) (encodeString s2) (encodeString s3) (encodeString s4) (encodeString s5) (encodeString s6) (encodeString s7) (encodeString s8) (encodeString s9)) = Datetime.value s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 := by
  intro input mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm
  exact (datetime_value_equiv mm yyyy dd timeHh timeMm ss sss offset
    offsetHh offsetMm).symm

theorem view_valid_equiv :
    ∀ input s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : String, Recovered.datetime_view_valid (Recovered.mkDatetimeView (encodeString input) (encodeString s0) (encodeString s1) (encodeString s2) (encodeString s3) (encodeString s4) (encodeString s5) (encodeString s6) (encodeString s7) (encodeString s8) (encodeString s9)) ↔ (Datetime.WfConstraints s0 s3 s4 s5 s8 s9 s2 s1 ∧ Datetime.Constraints s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) := by
  intro input mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm
  change
    (triptych_datetime_roundtrip.datetime_wf_constraints
          (encodeString mm) (encodeString timeHh) (encodeString timeMm)
          (encodeString ss) (encodeString offsetHh) (encodeString offsetMm)
          (encodeString dd) (encodeString yyyy) ∧
        triptych_datetime_roundtrip.datetime_constraints
          (encodeString mm) (encodeString yyyy) (encodeString dd)
          (encodeString timeHh) (encodeString timeMm) (encodeString ss)
          (encodeString sss) (encodeString offset) (encodeString offsetHh)
          (encodeString offsetMm)) ↔ _
  rw [← datetime_wf_constraints_equiv mm timeHh timeMm ss offsetHh
    offsetMm dd yyyy,
    ← datetime_constraints_equiv mm yyyy dd timeHh timeMm ss sss offset
      offsetHh offsetMm]

theorem matching_view_normalizes_equiv :
    ∀ input : String, ∀ view : Recovered.DatetimeView,
      Recovered.datetime_matches_view (encodeString input) view →
        ∃ mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm : String,
          view =
            Recovered.mkDatetimeView (encodeString input) (encodeString mm)
              (encodeString yyyy) (encodeString dd) (encodeString timeHh)
              (encodeString timeMm) (encodeString ss) (encodeString sss)
              (encodeString offset) (encodeString offsetHh)
              (encodeString offsetMm) := by
  intro input view hmatch
  obtain ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, _, heq⟩ :=
    (normalize_matching_view input (fun candidate => candidate = view)).1
      ⟨view, hmatch, rfl⟩
  exact ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
    offsetMm, heq.symm⟩

theorem matches_view_exact_equiv :
    ∀ input mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm :
      String,
      Recovered.datetime_matches_view (encodeString input)
          (Recovered.mkDatetimeView (encodeString input) (encodeString mm)
            (encodeString yyyy) (encodeString dd) (encodeString timeHh)
            (encodeString timeMm) (encodeString ss) (encodeString sss)
            (encodeString offset) (encodeString offsetHh)
            (encodeString offsetMm)) ↔
        ((((((((((Datetime.IsWf.Datetime input ∧
                      Triptych.component Datetime.grammar input "MM" = mm) ∧
                    Triptych.component Datetime.grammar input "YYYY" =
                      yyyy) ∧
                  Triptych.component Datetime.grammar input "DD" = dd) ∧
                Triptych.component Datetime.grammar input "Time.hh" =
                  timeHh) ∧
              Triptych.component Datetime.grammar input "Time.mm" =
                timeMm) ∧
            Triptych.component Datetime.grammar input "ss" = ss) ∧
          Triptych.component Datetime.grammar input "SSS" = sss) ∧
        Triptych.component Datetime.grammar input "Offset" = offset) ∧
      Triptych.component Datetime.grammar input "Offset.hh" = offsetHh) ∧
    Triptych.component Datetime.grammar input "Offset.mm" = offsetMm) := by
  intro input mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm
  change
    triptych_datetime_roundtrip.datetime_matches_view (encodeString input)
        (.DatetimeView (encodeString input) (encodeString mm)
          (encodeString yyyy) (encodeString dd) (encodeString timeHh)
          (encodeString timeMm) (encodeString ss) (encodeString sss)
          (encodeString offset) (encodeString offsetHh)
          (encodeString offsetMm)) ↔ _
  rw [matches_view_equiv]
  constructor
  · intro hparts
    obtain ⟨hmm, hyyyy, hdd, hth, htm, hss, hsss, hoff, hoh, hom⟩ :=
      components_of_parts input mm yyyy dd timeHh timeMm ss sss offset
        offsetHh offsetMm hparts
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨(datetime_parts_exists_equiv input).2
      ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh, offsetMm,
        hparts⟩, hmm⟩, hyyyy⟩, hdd⟩, hth⟩, htm⟩, hss⟩, hsss⟩, hoff⟩,
        hoh⟩, hom⟩
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hgrammar, hmm⟩, hyyyy⟩, hdd⟩, hth⟩, htm⟩,
      hss⟩, hsss⟩, hoff⟩, hoh⟩, hom⟩
    obtain ⟨mm', yyyy', dd', timeHh', timeMm', ss', sss', offset',
      offsetHh', offsetMm', hparts⟩ :=
      (datetime_parts_exists_equiv input).1 hgrammar
    obtain ⟨hmm', hyyyy', hdd', hth', htm', hss', hsss', hoff', hoh',
      hom'⟩ :=
      components_of_parts input mm' yyyy' dd' timeHh' timeMm' ss' sss'
        offset' offsetHh' offsetMm' hparts
    have emm : mm' = mm := hmm'.symm.trans hmm
    have eyyyy : yyyy' = yyyy := hyyyy'.symm.trans hyyyy
    have edd : dd' = dd := hdd'.symm.trans hdd
    have eth : timeHh' = timeHh := hth'.symm.trans hth
    have etm : timeMm' = timeMm := htm'.symm.trans htm
    have ess : ss' = ss := hss'.symm.trans hss
    have esss : sss' = sss := hsss'.symm.trans hsss
    have eoff : offset' = offset := hoff'.symm.trans hoff
    have eoh : offsetHh' = offsetHh := hoh'.symm.trans hoh
    have eom : offsetMm' = offsetMm := hom'.symm.trans hom
    simpa only [emm, eyyyy, edd, eth, etm, ess, esss, eoff, eoh, eom]
      using hparts

theorem matches_result_equiv :
    ∀ input : String, ∀ result : Int,
      (Datetime.IsValid input ∧ Datetime.computeValue input = some result) ↔
        Recovered.datetime_matches_result (encodeString input) result := by
  intro input result
  change
    (Datetime.IsValid input ∧ Datetime.computeValue input = some result) ↔
      triptych_datetime_roundtrip.datetime_matches_result
        (encodeString input) result
  unfold triptych_datetime_roundtrip.datetime_matches_result
  constructor
  · rintro
      ⟨⟨⟨hgrammar, hsourceWf⟩, hsourceConstraints⟩, hcompute⟩
    obtain ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, hparts⟩ :=
      (datetime_parts_exists_equiv input).1 hgrammar
    obtain ⟨hmm, hyyyy, hdd, hth, htm, hss, hsss, hoff, hoh, hom⟩ :=
      components_of_parts input mm yyyy dd timeHh timeMm ss sss offset
        offsetHh offsetMm hparts
    have hwfConstraints :
        Datetime.WfConstraints mm timeHh timeMm ss offsetHh offsetMm dd
          yyyy := by
      unfold Datetime.SatisfiesWfConstraints at hsourceWf
      simpa only [hmm, hth, htm, hss, hoh, hom, hdd, hyyyy] using
        hsourceWf
    have hconstraints :
        Datetime.Constraints mm yyyy dd timeHh timeMm ss sss offset offsetHh
          offsetMm := by
      unfold Datetime.SatisfiesConstraints at hsourceConstraints
      simpa only [hmm, hyyyy, hdd, hth, htm, hss, hsss, hoff, hoh, hom]
        using hsourceConstraints
    have hvalue :
        Datetime.value mm yyyy dd timeHh timeMm ss sss offset offsetHh
            offsetMm =
          result := by
      rw [compute_value_of_parts input mm yyyy dd timeHh timeMm ss sss
        offset offsetHh offsetMm hparts] at hcompute
      exact Option.some.inj hcompute
    let view :=
      triptych_datetime_roundtrip.DatetimeView.DatetimeView
        (encodeString input) (encodeString mm) (encodeString yyyy)
        (encodeString dd) (encodeString timeHh) (encodeString timeMm)
        (encodeString ss) (encodeString sss) (encodeString offset)
        (encodeString offsetHh) (encodeString offsetMm)
    refine ⟨view, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · exact (matches_view_equiv input mm yyyy dd timeHh timeMm ss sss
        offset offsetHh offsetMm).2 hparts
    · exact (view_valid_equiv input mm yyyy dd timeHh timeMm ss sss offset
        offsetHh offsetMm).2 ⟨hwfConstraints, hconstraints⟩
    · exact (view_denotation_equiv input mm yyyy dd timeHh timeMm ss sss offset
        offsetHh offsetMm).trans hvalue
  · rintro ⟨view, ⟨⟨hmatch, hviewValid⟩, hdenotation⟩⟩
    obtain ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh,
      offsetMm, heq⟩ :=
      matching_view_normalizes_equiv input view hmatch
    subst view
    have hparts :=
      (matches_view_equiv input mm yyyy dd timeHh timeMm ss sss offset
        offsetHh offsetMm).1 hmatch
    obtain ⟨hmm, hyyyy, hdd, hth, htm, hss, hsss, hoff, hoh, hom⟩ :=
      components_of_parts input mm yyyy dd timeHh timeMm ss sss offset
        offsetHh offsetMm hparts
    obtain ⟨hwfConstraints, hconstraints⟩ :=
      (view_valid_equiv input mm yyyy dd timeHh timeMm ss sss offset offsetHh
        offsetMm).1 hviewValid
    have hgrammar : Datetime.IsWf.Datetime input :=
      (datetime_parts_exists_equiv input).2
        ⟨mm, yyyy, dd, timeHh, timeMm, ss, sss, offset, offsetHh, offsetMm,
          hparts⟩
    have hsatisfiesWf : Datetime.SatisfiesWfConstraints input := by
      unfold Datetime.SatisfiesWfConstraints
      simpa only [hmm, hth, htm, hss, hoh, hom, hdd, hyyyy] using
        hwfConstraints
    have hsatisfies : Datetime.SatisfiesConstraints input := by
      unfold Datetime.SatisfiesConstraints
      simpa only [hmm, hyyyy, hdd, hth, htm, hss, hsss, hoff, hoh, hom]
        using hconstraints
    have hvalue :
        Datetime.value mm yyyy dd timeHh timeMm ss sss offset offsetHh
            offsetMm =
          result :=
      (view_denotation_equiv input mm yyyy dd timeHh timeMm ss sss offset
        offsetHh offsetMm).symm.trans hdenotation
    refine ⟨⟨⟨hgrammar, hsatisfiesWf⟩, hsatisfies⟩, ?_⟩
    rw [compute_value_of_parts input mm yyyy dd timeHh timeMm ss sss
      offset offsetHh offsetMm hparts]
    exact congrArg some hvalue

end Triptych.Vermilion.Proofs.Datetime
