import TriptychVermilionGenerated.Duration
import Triptych.Backend.Verus.AstSemantics
import Proofs.Duration.RuleRegistryProof

namespace Triptych.Vermilion.Proofs.Duration

open Triptych
open Triptych.Vermilion.String
open Triptych.Vermilion.Generated.Duration

theorem digit_run_equiv (source : String) :
    Triptych.IsDigits source ↔
      triptych_duration_roundtrip.duration_is_wf_DDays
        (encodeString source) := by
  simpa [triptych_duration_roundtrip.duration_is_wf_DDays,
    triptych_duration_roundtrip.triptych_is_digit, IsDigitCode] using
      digits_iff_encoded source

theorem digit_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_duration_roundtrip.duration_is_wf_DDays sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  apply digit_witness_sequence_range sequence
    (fun digits => 1 ≤ Vermilion.Seq.len digits)
  simpa [triptych_duration_roundtrip.duration_is_wf_DDays,
    triptych_duration_roundtrip.triptych_is_digit, IsDigitCode] using hwf

theorem sign_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_duration_roundtrip.duration_is_wf_Sign sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  exact optional_minus_sequence_range sequence hwf

theorem sign_equiv (source : String) :
    Duration.IsWf.Sign source ↔
      triptych_duration_roundtrip.duration_is_wf_Sign
        (encodeString source) := by
  constructor
  · intro hsource
    rcases hsource with hsource | hsource
    · subst source
      exact ⟨encodeString "-", rfl, Or.inr rfl⟩
    · subst source
      exact ⟨encodeString "", rfl, Or.inl (by simp)⟩
  · rintro ⟨literal, hsource, hempty | hminus⟩
    · right
      apply encodeString_injective
      rw [hsource]
      exact sequence_eq_empty_of_length_zero literal hempty
    · left
      apply encodeString_injective
      rw [hsource, hminus]
      rfl

theorem suffixed_digits_equiv (source suffix : String) :
    (∃ digits, source = digits ++ suffix ∧ Triptych.IsDigits digits) ↔
      ∃ digits : Vermilion.Seq Int,
        encodeString source =
          Vermilion.Seq.add digits (encodeString suffix) ∧
        triptych_duration_roundtrip.duration_is_wf_DDays digits := by
  constructor
  · rintro ⟨digits, hsource, hdigits⟩
    refine ⟨encodeString digits, ?_, (digit_run_equiv digits).1 hdigits⟩
    simpa [Vermilion.Seq.add] using congrArg encodeString hsource
  · rintro ⟨digits, hsource, hdigits⟩
    have hdigitsRange := digit_sequence_range digits hdigits
    let digitsText := decodeSequence digits
    have hdigitsEncode : encodeString digitsText = digits :=
      encode_decode_sequence digits hdigitsRange
    refine ⟨digitsText, ?_, ?_⟩
    · apply encodeString_injective
      rw [encodeString_append, hdigitsEncode]
      simpa [Vermilion.Seq.add] using hsource
    · apply (digit_run_equiv digitsText).2
      simpa [hdigitsEncode] using hdigits

theorem days_equiv (source : String) :
    Duration.IsWf.Days source ↔
      triptych_duration_roundtrip.duration_is_wf_Days
        (encodeString source) := by
  unfold Duration.IsWf.Days triptych_duration_roundtrip.duration_is_wf_Days
  simpa [Duration.IsWf.DDays, encodeString, Vermilion.Seq.add,
    Vermilion.Seq.push, Vermilion.Seq.empty] using
      suffixed_digits_equiv source "d"

theorem hours_equiv (source : String) :
    Duration.IsWf.Hours source ↔
      triptych_duration_roundtrip.duration_is_wf_Hours
        (encodeString source) := by
  unfold Duration.IsWf.Hours triptych_duration_roundtrip.duration_is_wf_Hours
  simpa [Duration.IsWf.DHours, encodeString, Vermilion.Seq.add,
    Vermilion.Seq.push, Vermilion.Seq.empty,
    triptych_duration_roundtrip.duration_is_wf_DHours,
    triptych_duration_roundtrip.duration_is_wf_DDays] using
      suffixed_digits_equiv source "h"

theorem minutes_equiv (source : String) :
    Duration.IsWf.Minutes source ↔
      triptych_duration_roundtrip.duration_is_wf_Minutes
        (encodeString source) := by
  unfold Duration.IsWf.Minutes triptych_duration_roundtrip.duration_is_wf_Minutes
  simpa [Duration.IsWf.DMinutes, encodeString, Vermilion.Seq.add,
    Vermilion.Seq.push, Vermilion.Seq.empty,
    triptych_duration_roundtrip.duration_is_wf_DMinutes,
    triptych_duration_roundtrip.duration_is_wf_DDays] using
      suffixed_digits_equiv source "m"

theorem seconds_equiv (source : String) :
    Duration.IsWf.Seconds source ↔
      triptych_duration_roundtrip.duration_is_wf_Seconds
        (encodeString source) := by
  unfold Duration.IsWf.Seconds triptych_duration_roundtrip.duration_is_wf_Seconds
  simpa [Duration.IsWf.DSeconds, encodeString, Vermilion.Seq.add,
    Vermilion.Seq.push, Vermilion.Seq.empty,
    triptych_duration_roundtrip.duration_is_wf_DSeconds,
    triptych_duration_roundtrip.duration_is_wf_DDays] using
      suffixed_digits_equiv source "s"

theorem millis_equiv (source : String) :
    Duration.IsWf.Millis source ↔
      triptych_duration_roundtrip.duration_is_wf_Millis
        (encodeString source) := by
  unfold Duration.IsWf.Millis triptych_duration_roundtrip.duration_is_wf_Millis
  simpa [Duration.IsWf.DMillis, encodeString, Vermilion.Seq.add,
    Vermilion.Seq.push, Vermilion.Seq.empty,
    triptych_duration_roundtrip.duration_is_wf_DMillis,
    triptych_duration_roundtrip.duration_is_wf_DDays] using
      suffixed_digits_equiv source "ms"

theorem optional_suffixed_sequence_range
    (sequence : Vermilion.Seq Int) (suffix : String)
    (hwf : Vermilion.Seq.len sequence = 0 ∨
      ∃ digits : Vermilion.Seq Int,
        sequence = Vermilion.Seq.add digits (encodeString suffix) ∧
          triptych_duration_roundtrip.duration_is_wf_DDays digits) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  apply Triptych.Vermilion.String.optional_suffixed_sequence_range sequence suffix
  rcases hwf with hempty | ⟨digits, hsequence, hdigits⟩
  · exact Or.inl hempty
  · exact Or.inr ⟨digits, hsequence, digit_sequence_range digits hdigits⟩

theorem optional_days_sequence_range
    (sequence : Vermilion.Seq Int)
    (hwf : Vermilion.Seq.len sequence = 0 ∨
      triptych_duration_roundtrip.duration_is_wf_Days sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  apply optional_suffixed_sequence_range sequence "d"
  simpa [triptych_duration_roundtrip.duration_is_wf_Days, encodeString,
    Vermilion.Seq.add, Vermilion.Seq.push, Vermilion.Seq.empty] using hwf

theorem optional_hours_sequence_range
    (sequence : Vermilion.Seq Int)
    (hwf : Vermilion.Seq.len sequence = 0 ∨
      triptych_duration_roundtrip.duration_is_wf_Hours sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  apply optional_suffixed_sequence_range sequence "h"
  simpa [triptych_duration_roundtrip.duration_is_wf_Hours,
    triptych_duration_roundtrip.duration_is_wf_DHours,
    triptych_duration_roundtrip.duration_is_wf_DDays, encodeString,
    Vermilion.Seq.add, Vermilion.Seq.push, Vermilion.Seq.empty] using hwf

theorem optional_minutes_sequence_range
    (sequence : Vermilion.Seq Int)
    (hwf : Vermilion.Seq.len sequence = 0 ∨
      triptych_duration_roundtrip.duration_is_wf_Minutes sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  apply optional_suffixed_sequence_range sequence "m"
  simpa [triptych_duration_roundtrip.duration_is_wf_Minutes,
    triptych_duration_roundtrip.duration_is_wf_DMinutes,
    triptych_duration_roundtrip.duration_is_wf_DDays, encodeString,
    Vermilion.Seq.add, Vermilion.Seq.push, Vermilion.Seq.empty] using hwf

theorem optional_seconds_sequence_range
    (sequence : Vermilion.Seq Int)
    (hwf : Vermilion.Seq.len sequence = 0 ∨
      triptych_duration_roundtrip.duration_is_wf_Seconds sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  apply optional_suffixed_sequence_range sequence "s"
  simpa [triptych_duration_roundtrip.duration_is_wf_Seconds,
    triptych_duration_roundtrip.duration_is_wf_DSeconds,
    triptych_duration_roundtrip.duration_is_wf_DDays, encodeString,
    Vermilion.Seq.add, Vermilion.Seq.push, Vermilion.Seq.empty] using hwf

theorem optional_millis_sequence_range
    (sequence : Vermilion.Seq Int)
    (hwf : Vermilion.Seq.len sequence = 0 ∨
      triptych_duration_roundtrip.duration_is_wf_Millis sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  apply optional_suffixed_sequence_range sequence "ms"
  simpa [triptych_duration_roundtrip.duration_is_wf_Millis,
    triptych_duration_roundtrip.duration_is_wf_DMillis,
    triptych_duration_roundtrip.duration_is_wf_DDays, encodeString,
    Vermilion.Seq.add, Vermilion.Seq.push, Vermilion.Seq.empty] using hwf

theorem components_equiv (source : String) :
    Duration.IsWf.Components source ↔
      triptych_duration_roundtrip.duration_is_wf_Components
        (encodeString source) := by
  unfold Duration.IsWf.Components
    triptych_duration_roundtrip.duration_is_wf_Components
  constructor
  · rintro ⟨days, hours, minutes, seconds, millis,
      ⟨⟨⟨⟨⟨hsource, hdays⟩, hhours⟩, hminutes⟩, hseconds⟩, hmillis⟩⟩
    refine ⟨encodeString days, encodeString hours, encodeString minutes,
      encodeString seconds, encodeString millis, ?_⟩
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simpa [Vermilion.Seq.add, List.append_assoc] using
        congrArg encodeString hsource
    · rcases hdays with rfl | hdays
      · left
        simp
      · exact Or.inr ((days_equiv days).1 hdays)
    · rcases hhours with rfl | hhours
      · left
        simp
      · exact Or.inr ((hours_equiv hours).1 hhours)
    · rcases hminutes with rfl | hminutes
      · left
        simp
      · exact Or.inr ((minutes_equiv minutes).1 hminutes)
    · rcases hseconds with rfl | hseconds
      · left
        simp
      · exact Or.inr ((seconds_equiv seconds).1 hseconds)
    · rcases hmillis with rfl | hmillis
      · left
        simp
      · exact Or.inr ((millis_equiv millis).1 hmillis)
  · rintro ⟨days, hours, minutes, seconds, millis,
      ⟨⟨⟨⟨⟨hsource, hdays⟩, hhours⟩, hminutes⟩, hseconds⟩, hmillis⟩⟩
    let daysText := decodeSequence days
    let hoursText := decodeSequence hours
    let minutesText := decodeSequence minutes
    let secondsText := decodeSequence seconds
    let millisText := decodeSequence millis
    have hdaysEncode : encodeString daysText = days :=
      encode_decode_sequence days (optional_days_sequence_range days hdays)
    have hhoursEncode : encodeString hoursText = hours :=
      encode_decode_sequence hours (optional_hours_sequence_range hours hhours)
    have hminutesEncode : encodeString minutesText = minutes :=
      encode_decode_sequence minutes
        (optional_minutes_sequence_range minutes hminutes)
    have hsecondsEncode : encodeString secondsText = seconds :=
      encode_decode_sequence seconds
        (optional_seconds_sequence_range seconds hseconds)
    have hmillisEncode : encodeString millisText = millis :=
      encode_decode_sequence millis
        (optional_millis_sequence_range millis hmillis)
    refine ⟨daysText, hoursText, minutesText, secondsText, millisText, ?_⟩
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · apply encodeString_injective
      rw [encodeString_append, encodeString_append, encodeString_append,
        encodeString_append, hdaysEncode, hhoursEncode, hminutesEncode,
        hsecondsEncode, hmillisEncode]
      simpa [Vermilion.Seq.add, List.append_assoc] using hsource
    · rcases hdays with hempty | hpresent
      · left
        apply encodeString_injective
        rw [hdaysEncode]
        exact sequence_eq_empty_of_length_zero days hempty
      · right
        apply (days_equiv daysText).2
        simpa [hdaysEncode] using hpresent
    · rcases hhours with hempty | hpresent
      · left
        apply encodeString_injective
        rw [hhoursEncode]
        exact sequence_eq_empty_of_length_zero hours hempty
      · right
        apply (hours_equiv hoursText).2
        simpa [hhoursEncode] using hpresent
    · rcases hminutes with hempty | hpresent
      · left
        apply encodeString_injective
        rw [hminutesEncode]
        exact sequence_eq_empty_of_length_zero minutes hempty
      · right
        apply (minutes_equiv minutesText).2
        simpa [hminutesEncode] using hpresent
    · rcases hseconds with hempty | hpresent
      · left
        apply encodeString_injective
        rw [hsecondsEncode]
        exact sequence_eq_empty_of_length_zero seconds hempty
      · right
        apply (seconds_equiv secondsText).2
        simpa [hsecondsEncode] using hpresent
    · rcases hmillis with hempty | hpresent
      · left
        apply encodeString_injective
        rw [hmillisEncode]
        exact sequence_eq_empty_of_length_zero millis hempty
      · right
        apply (millis_equiv millisText).2
        simpa [hmillisEncode] using hpresent

theorem components_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_duration_roundtrip.duration_is_wf_Components sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  rcases hwf with ⟨days, hours, minutes, seconds, millis,
    ⟨⟨⟨⟨⟨rfl, hdays⟩, hhours⟩, hminutes⟩, hseconds⟩, hmillis⟩⟩
  have hdaysRange := optional_days_sequence_range days hdays
  have hhoursRange := optional_hours_sequence_range hours hhours
  have hminutesRange := optional_minutes_sequence_range minutes hminutes
  have hsecondsRange := optional_seconds_sequence_range seconds hseconds
  have hmillisRange := optional_millis_sequence_range millis hmillis
  exact sequence_add_range
    (Vermilion.Seq.add
      (Vermilion.Seq.add (Vermilion.Seq.add days hours) minutes) seconds)
    millis
    (sequence_add_range
      (Vermilion.Seq.add (Vermilion.Seq.add days hours) minutes) seconds
      (sequence_add_range (Vermilion.Seq.add days hours) minutes
        (sequence_add_range days hours hdaysRange hhoursRange)
        hminutesRange)
      hsecondsRange)
    hmillisRange

theorem duration_equiv (source : String) :
    Duration.IsWf.Duration source ↔
      triptych_duration_roundtrip.duration_is_wf_Duration
        (encodeString source) := by
  unfold Duration.IsWf.Duration Duration.Production
    triptych_duration_roundtrip.duration_is_wf_Duration
  constructor
  · rintro ⟨signPart, components, ⟨hsource, hsign⟩, hcomponents⟩
    refine ⟨encodeString signPart, encodeString components, ?_⟩
    refine ⟨⟨?_, (sign_equiv signPart).1 hsign⟩,
      (components_equiv components).1 hcomponents⟩
    simpa [Vermilion.Seq.add] using congrArg encodeString hsource
  · rintro ⟨signSequence, components, ⟨⟨hsource, hsign⟩, hcomponents⟩⟩
    let signText := decodeSequence signSequence
    let componentsText := decodeSequence components
    have hsignEncode : encodeString signText = signSequence :=
      encode_decode_sequence signSequence (sign_sequence_range signSequence hsign)
    have hcomponentsEncode : encodeString componentsText = components :=
      encode_decode_sequence components
        (components_sequence_range components hcomponents)
    refine ⟨signText, componentsText, ?_⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply encodeString_injective
      rw [encodeString_append, hsignEncode, hcomponentsEncode]
      simpa [Vermilion.Seq.add] using hsource
    · apply (sign_equiv signText).2
      simpa [hsignEncode] using hsign
    · apply (components_equiv componentsText).2
      simpa [hcomponentsEncode] using hcomponents

theorem natFrom_eq_fold (bytes : List Int) (index : Nat)
    (accumulator : Int) (hindex : index ≤ bytes.length) :
    triptych_duration_roundtrip.triptych_nat_of_from
        bytes (Int.ofNat index) accumulator =
      (bytes.drop index).foldl
        (fun current byte => current * 10 + recoveredDigit byte)
        accumulator := by
  apply Triptych.Vermilion.String.natFrom_eq_fold
    triptych_duration_roundtrip.triptych_nat_of_from
  · intro stepBytes stepIndex stepAccumulator hrange
    rw [triptych_duration_roundtrip.triptych_nat_of_from, dif_pos hrange]
    rfl
  · exact hindex

theorem natOf_equiv (source : String) :
    triptych_duration_roundtrip.triptych_nat_of (encodeString source) =
      Triptych.natOf source := by
  unfold triptych_duration_roundtrip.triptych_nat_of
  change triptych_duration_roundtrip.triptych_nat_of_from
      (encodeString source) (Int.ofNat 0) 0 = Triptych.natOf source
  rw [natFrom_eq_fold _ 0 0 (Nat.zero_le _)]
  simpa using encodedDigitFold_eq_natOf source

theorem signOf_equiv (source : String) :
    triptych_duration_roundtrip.triptych_sign_of (encodeString source) =
      Triptych.signOf source := by
  simpa [triptych_duration_roundtrip.triptych_sign_of,
    triptych_duration_roundtrip.TRIPTYCH_MINUS, recoveredSignOf] using
      recoveredSignOf_encodeString source

theorem duration_value_equiv
    (signPart dDays dHours dMinutes dSeconds dMillis : String) :
    Duration.value signPart dDays dHours dMinutes dSeconds dMillis =
      triptych_duration_roundtrip.duration_value
        (encodeString signPart) (encodeString dDays) (encodeString dHours)
        (encodeString dMinutes) (encodeString dSeconds)
        (encodeString dMillis) := by
  unfold Duration.value triptych_duration_roundtrip.duration_value
  rw [signOf_equiv, natOf_equiv, natOf_equiv, natOf_equiv, natOf_equiv,
    natOf_equiv]

theorem duration_constraints_equiv
    (signPart dDays dHours dMinutes dSeconds dMillis : String) :
    Duration.Constraints signPart dDays dHours dMinutes dSeconds dMillis ↔
      triptych_duration_roundtrip.duration_constraints
        (encodeString signPart) (encodeString dDays) (encodeString dHours)
        (encodeString dMinutes) (encodeString dSeconds)
        (encodeString dMillis) := by
  unfold Duration.Constraints triptych_duration_roundtrip.duration_constraints
  rw [← duration_value_equiv signPart dDays dHours dMinutes dSeconds dMillis]
  norm_num

theorem duration_wf_constraints_equiv (components : String) :
    Duration.WfConstraints components ↔
      triptych_duration_roundtrip.duration_wf_constraints
        (encodeString components) := by
  unfold Duration.WfConstraints
    triptych_duration_roundtrip.duration_wf_constraints
  rw [encodeString_length]
  by_cases hempty : components = ""
  · simp [hempty, Vermilion.iteP]
  · have hlength : components.length ≠ 0 := by
      intro hzero
      apply hempty
      apply String.ext
      apply List.eq_nil_of_length_eq_zero
      simpa [String.length_toList] using hzero
    simp [hempty, hlength, Vermilion.iteP]

def unitText (digits suffix : String) : String :=
  if digits = "" then "" else digits ++ suffix

def digitSlot (digits : String) : Prop :=
  digits = "" ∨ Triptych.IsDigits digits

def durationParts (input signPart dDays dHours dMinutes dSeconds
    dMillis components : String) : Prop :=
  input = signPart ++ components ∧
    Duration.IsWf.Sign signPart ∧
    components =
      unitText dDays "d" ++ unitText dHours "h" ++
        unitText dMinutes "m" ++ unitText dSeconds "s" ++
          unitText dMillis "ms" ∧
    digitSlot dDays ∧ digitSlot dHours ∧ digitSlot dMinutes ∧
      digitSlot dSeconds ∧ digitSlot dMillis

theorem optional_suffixed_match_equiv
    (sequence : Vermilion.Seq Int) (digits suffix : String) :
    ((Vermilion.Seq.len sequence = 0 ∧
        encodeString digits = Vermilion.Seq.empty) ∨
      ∃ digitSequence : Vermilion.Seq Int,
        sequence = Vermilion.Seq.add digitSequence (encodeString suffix) ∧
          encodeString digits = digitSequence ∧
          triptych_duration_roundtrip.duration_is_wf_DDays digitSequence) ↔
      sequence = encodeString (unitText digits suffix) ∧
        digitSlot digits := by
  constructor
  · rintro (⟨hsequence, hdigits⟩ | ⟨digitSequence, hsequence,
      hdigits, hdigitWf⟩)
    · have hdigitsEmpty : digits = "" := by
        exact encodeString_injective (by
          simpa [encodeString, Vermilion.Seq.empty] using hdigits)
      subst digits
      constructor
      · rw [unitText]
        simp
        exact sequence_eq_empty_of_length_zero sequence hsequence
      · exact Or.inl rfl
    · subst digitSequence
      have hdigitSource : Triptych.IsDigits digits :=
        (digit_run_equiv digits).2 (by simpa using hdigitWf)
      have hdigitsNonempty : digits ≠ "" := by
        intro hempty
        subst digits
        simpa [Triptych.IsDigits] using hdigitSource
      constructor
      · simp [unitText, hdigitsNonempty, encodeString_append,
          Vermilion.Seq.add, hsequence]
      · exact Or.inr hdigitSource
  · rintro ⟨hsequence, hdigitSlot⟩
    by_cases hdigitsEmpty : digits = ""
    · left
      subst digits
      constructor
      · rw [unitText] at hsequence
        simpa [Vermilion.Seq.len, encodeString, Vermilion.Seq.empty]
          using congrArg Vermilion.Seq.len hsequence
      · rfl
    · have hdigitSource : Triptych.IsDigits digits :=
        hdigitSlot.resolve_left hdigitsEmpty
      right
      refine ⟨encodeString digits, ?_, rfl,
        (digit_run_equiv digits).1 hdigitSource⟩
      simpa [unitText, hdigitsEmpty, encodeString_append,
        Vermilion.Seq.add] using hsequence

theorem matches_view_equiv
    (input signPart dDays dHours dMinutes dSeconds dMillis
      components : String) :
    triptych_duration_roundtrip.duration_matches_view
        (encodeString input)
        (.DurationView (encodeString input) (encodeString signPart)
          (encodeString dDays) (encodeString dHours) (encodeString dMinutes)
          (encodeString dSeconds) (encodeString dMillis)
          (encodeString components)) ↔
      durationParts input signPart dDays dHours dMinutes dSeconds dMillis
        components := by
  constructor
  · rintro ⟨_, signSequence, componentsSequence,
      ⟨⟨hinput, ⟨hsignSequence, hsign⟩⟩,
        ⟨hcomponentsSequence, days, hours, minutes, seconds, millis,
          ⟨⟨⟨⟨⟨hcomponents, hdays⟩, hhours⟩, hminutes⟩,
            hseconds⟩, hmillis⟩⟩⟩⟩
    subst signSequence
    subst componentsSequence
    have hsignSource : Duration.IsWf.Sign signPart := by
      apply (sign_equiv signPart).2
      simpa [triptych_duration_roundtrip.duration_matches_Sign,
        triptych_duration_roundtrip.duration_is_wf_Sign] using hsign
    have hdays' :
        days = encodeString (unitText dDays "d") ∧ digitSlot dDays := by
      apply (optional_suffixed_match_equiv days dDays "d").1
      simpa [triptych_duration_roundtrip.duration_matches_Days,
        triptych_duration_roundtrip.duration_matches_DDays,
        triptych_duration_roundtrip.duration_is_wf_DDays, encodeString,
        Vermilion.Seq.add, Vermilion.Seq.push, Vermilion.Seq.empty]
        using hdays
    have hhours' :
        hours = encodeString (unitText dHours "h") ∧ digitSlot dHours := by
      apply (optional_suffixed_match_equiv hours dHours "h").1
      simpa [triptych_duration_roundtrip.duration_matches_Hours,
        triptych_duration_roundtrip.duration_matches_DHours,
        triptych_duration_roundtrip.duration_is_wf_DDays, encodeString,
        Vermilion.Seq.add, Vermilion.Seq.push, Vermilion.Seq.empty]
        using hhours
    have hminutes' :
        minutes = encodeString (unitText dMinutes "m") ∧
          digitSlot dMinutes := by
      apply (optional_suffixed_match_equiv minutes dMinutes "m").1
      simpa [triptych_duration_roundtrip.duration_matches_Minutes,
        triptych_duration_roundtrip.duration_matches_DMinutes,
        triptych_duration_roundtrip.duration_is_wf_DDays, encodeString,
        Vermilion.Seq.add, Vermilion.Seq.push, Vermilion.Seq.empty]
        using hminutes
    have hseconds' :
        seconds = encodeString (unitText dSeconds "s") ∧
          digitSlot dSeconds := by
      apply (optional_suffixed_match_equiv seconds dSeconds "s").1
      simpa [triptych_duration_roundtrip.duration_matches_Seconds,
        triptych_duration_roundtrip.duration_matches_DSeconds,
        triptych_duration_roundtrip.duration_is_wf_DDays, encodeString,
        Vermilion.Seq.add, Vermilion.Seq.push, Vermilion.Seq.empty]
        using hseconds
    have hmillis' :
        millis = encodeString (unitText dMillis "ms") ∧
          digitSlot dMillis := by
      apply (optional_suffixed_match_equiv millis dMillis "ms").1
      simpa [triptych_duration_roundtrip.duration_matches_Millis,
        triptych_duration_roundtrip.duration_matches_DMillis,
        triptych_duration_roundtrip.duration_is_wf_DDays, encodeString,
        Vermilion.Seq.add, Vermilion.Seq.push, Vermilion.Seq.empty]
        using hmillis
    refine ⟨?_, hsignSource, ?_, hdays'.2, hhours'.2, hminutes'.2,
      hseconds'.2, hmillis'.2⟩
    · apply encodeString_injective
      simpa [encodeString_append, Vermilion.Seq.add] using hinput
    · apply encodeString_injective
      rw [encodeString_append, encodeString_append, encodeString_append,
        encodeString_append, ← hdays'.1, ← hhours'.1, ← hminutes'.1,
        ← hseconds'.1, ← hmillis'.1]
      simpa [Vermilion.Seq.add, List.append_assoc] using hcomponents
  · rintro ⟨hinput, hsign, hcomponents, hdays, hhours, hminutes,
      hseconds, hmillis⟩
    refine ⟨rfl, encodeString signPart, encodeString components, ?_⟩
    refine ⟨⟨?_, ⟨rfl, ?_⟩⟩, ⟨rfl, ?_⟩⟩
    · simpa [encodeString_append, Vermilion.Seq.add] using
        congrArg encodeString hinput
    · simpa [triptych_duration_roundtrip.duration_matches_Sign,
        triptych_duration_roundtrip.duration_is_wf_Sign] using
          (sign_equiv signPart).1 hsign
    · refine ⟨encodeString (unitText dDays "d"),
        encodeString (unitText dHours "h"),
        encodeString (unitText dMinutes "m"),
        encodeString (unitText dSeconds "s"),
        encodeString (unitText dMillis "ms"), ?_⟩
      refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · simpa [encodeString_append, Vermilion.Seq.add,
          List.append_assoc] using congrArg encodeString hcomponents
      · apply (optional_suffixed_match_equiv
          (encodeString (unitText dDays "d")) dDays "d").2
        exact ⟨rfl, hdays⟩
      · apply (optional_suffixed_match_equiv
          (encodeString (unitText dHours "h")) dHours "h").2
        exact ⟨rfl, hhours⟩
      · apply (optional_suffixed_match_equiv
          (encodeString (unitText dMinutes "m")) dMinutes "m").2
        exact ⟨rfl, hminutes⟩
      · apply (optional_suffixed_match_equiv
          (encodeString (unitText dSeconds "s")) dSeconds "s").2
        exact ⟨rfl, hseconds⟩
      · apply (optional_suffixed_match_equiv
          (encodeString (unitText dMillis "ms")) dMillis "ms").2
        exact ⟨rfl, hmillis⟩

theorem optional_unit_parts_equiv (whole suffix : String) :
    (whole = "" ∨
      ∃ digits, whole = digits ++ suffix ∧ Triptych.IsDigits digits) ↔
      ∃ digits, whole = unitText digits suffix ∧ digitSlot digits := by
  constructor
  · rintro (rfl | ⟨digits, hwhole, hdigits⟩)
    · exact ⟨"", by simp [unitText], Or.inl rfl⟩
    · have hnonempty : digits ≠ "" := by
        intro hempty
        subst digits
        simpa [Triptych.IsDigits] using hdigits
      exact ⟨digits, by simpa [unitText, hnonempty] using hwhole,
        Or.inr hdigits⟩
  · rintro ⟨digits, hwhole, hdigits⟩
    by_cases hempty : digits = ""
    · left
      subst digits
      simpa [unitText] using hwhole
    · right
      have hdigitWf := hdigits.resolve_left hempty
      exact ⟨digits, by simpa [unitText, hempty] using hwhole, hdigitWf⟩

theorem duration_parts_exists_equiv (input : String) :
    Duration.IsWf.Duration input ↔
      ∃ signPart dDays dHours dMinutes dSeconds dMillis components : String,
        durationParts input signPart dDays dHours dMinutes dSeconds dMillis
          components := by
  constructor
  · rintro ⟨signPart, components, ⟨hinput, hsign⟩,
      days, hours, minutes, seconds, millis,
      ⟨⟨⟨⟨⟨hcomponents, hdays⟩, hhours⟩, hminutes⟩,
        hseconds⟩, hmillis⟩⟩
    obtain ⟨dDays, hdaysText, hdDays⟩ :=
      (optional_unit_parts_equiv days "d").1 (by
        simpa [Duration.IsWf.Days, Duration.IsWf.DDays] using hdays)
    obtain ⟨dHours, hhoursText, hdHours⟩ :=
      (optional_unit_parts_equiv hours "h").1 (by
        simpa [Duration.IsWf.Hours, Duration.IsWf.DHours] using hhours)
    obtain ⟨dMinutes, hminutesText, hdMinutes⟩ :=
      (optional_unit_parts_equiv minutes "m").1 (by
        simpa [Duration.IsWf.Minutes, Duration.IsWf.DMinutes] using hminutes)
    obtain ⟨dSeconds, hsecondsText, hdSeconds⟩ :=
      (optional_unit_parts_equiv seconds "s").1 (by
        simpa [Duration.IsWf.Seconds, Duration.IsWf.DSeconds] using hseconds)
    obtain ⟨dMillis, hmillisText, hdMillis⟩ :=
      (optional_unit_parts_equiv millis "ms").1 (by
        simpa [Duration.IsWf.Millis, Duration.IsWf.DMillis] using hmillis)
    refine ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis,
      components, hinput, hsign, ?_, hdDays, hdHours, hdMinutes, hdSeconds,
      hdMillis⟩
    simpa [hdaysText, hhoursText, hminutesText, hsecondsText, hmillisText]
      using hcomponents
  · rintro ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis,
      components, hinput, hsign, hcomponents, hdDays, hdHours, hdMinutes,
      hdSeconds, hdMillis⟩
    refine ⟨signPart, components, ⟨hinput, hsign⟩,
      unitText dDays "d", unitText dHours "h", unitText dMinutes "m",
      unitText dSeconds "s", unitText dMillis "ms", ?_⟩
    refine ⟨⟨⟨⟨⟨hcomponents, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simpa [Duration.IsWf.Days, Duration.IsWf.DDays] using
        (optional_unit_parts_equiv (unitText dDays "d") "d").2
          ⟨dDays, rfl, hdDays⟩
    · simpa [Duration.IsWf.Hours, Duration.IsWf.DHours] using
        (optional_unit_parts_equiv (unitText dHours "h") "h").2
          ⟨dHours, rfl, hdHours⟩
    · simpa [Duration.IsWf.Minutes, Duration.IsWf.DMinutes] using
        (optional_unit_parts_equiv (unitText dMinutes "m") "m").2
          ⟨dMinutes, rfl, hdMinutes⟩
    · simpa [Duration.IsWf.Seconds, Duration.IsWf.DSeconds] using
        (optional_unit_parts_equiv (unitText dSeconds "s") "s").2
          ⟨dSeconds, rfl, hdSeconds⟩
    · simpa [Duration.IsWf.Millis, Duration.IsWf.DMillis] using
        (optional_unit_parts_equiv (unitText dMillis "ms") "ms").2
          ⟨dMillis, rfl, hdMillis⟩

theorem matching_view_exists_equiv (input : String) :
    Duration.IsWf.Duration input ↔
      ∃ signPart dDays dHours dMinutes dSeconds dMillis components : String,
        triptych_duration_roundtrip.duration_matches_view
          (encodeString input)
          (.DurationView (encodeString input) (encodeString signPart)
            (encodeString dDays) (encodeString dHours)
            (encodeString dMinutes) (encodeString dSeconds)
            (encodeString dMillis) (encodeString components)) := by
  rw [duration_parts_exists_equiv]
  apply exists_congr
  intro signPart
  apply exists_congr
  intro dDays
  apply exists_congr
  intro dHours
  apply exists_congr
  intro dMinutes
  apply exists_congr
  intro dSeconds
  apply exists_congr
  intro dMillis
  apply exists_congr
  intro components
  exact (matches_view_equiv input signPart dDays dHours dMinutes dSeconds
    dMillis components).symm

theorem components_match_is_wf
    (components : Vermilion.Seq Int)
    (view : triptych_duration_roundtrip.DurationView)
    (hmatch :
      triptych_duration_roundtrip.duration_matches_Components components view) :
    triptych_duration_roundtrip.duration_is_wf_Components components := by
  rcases hmatch with ⟨days, hours, minutes, seconds, millis,
    ⟨⟨⟨⟨⟨hcomponents, hdays⟩, hhours⟩, hminutes⟩, hseconds⟩,
      hmillis⟩⟩
  refine ⟨days, hours, minutes, seconds, millis,
    ⟨⟨⟨⟨⟨hcomponents, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩⟩
  · rcases hdays with ⟨hempty, _⟩ | ⟨digits, hwhole, _, hdigits⟩
    · exact Or.inl hempty
    · exact Or.inr ⟨digits, hwhole, by
        simpa [triptych_duration_roundtrip.duration_matches_DDays,
          triptych_duration_roundtrip.duration_is_wf_DDays] using hdigits⟩
  · rcases hhours with ⟨hempty, _⟩ | ⟨digits, hwhole, _, hdigits⟩
    · exact Or.inl hempty
    · exact Or.inr ⟨digits, hwhole, by
        simpa [triptych_duration_roundtrip.duration_matches_DHours,
          triptych_duration_roundtrip.duration_is_wf_DHours] using hdigits⟩
  · rcases hminutes with ⟨hempty, _⟩ | ⟨digits, hwhole, _, hdigits⟩
    · exact Or.inl hempty
    · exact Or.inr ⟨digits, hwhole, by
        simpa [triptych_duration_roundtrip.duration_matches_DMinutes,
          triptych_duration_roundtrip.duration_is_wf_DMinutes] using hdigits⟩
  · rcases hseconds with ⟨hempty, _⟩ | ⟨digits, hwhole, _, hdigits⟩
    · exact Or.inl hempty
    · exact Or.inr ⟨digits, hwhole, by
        simpa [triptych_duration_roundtrip.duration_matches_DSeconds,
          triptych_duration_roundtrip.duration_is_wf_DSeconds] using hdigits⟩
  · rcases hmillis with ⟨hempty, _⟩ | ⟨digits, hwhole, _, hdigits⟩
    · exact Or.inl hempty
    · exact Or.inr ⟨digits, hwhole, by
        simpa [triptych_duration_roundtrip.duration_matches_DMillis,
          triptych_duration_roundtrip.duration_is_wf_DMillis] using hdigits⟩

theorem dDays_range_of_components_match
    (components : Vermilion.Seq Int)
    (view : triptych_duration_roundtrip.DurationView)
    (hmatch :
      triptych_duration_roundtrip.duration_matches_Components components view) :
    ∀ index : Int,
      0 ≤ index ∧
          index < Vermilion.Seq.len
            (triptych_duration_roundtrip.DurationView.get_DurationView_d_days
              view) →
        Vermilion.isUnicodeScalar
          (Vermilion.Seq.index
            (triptych_duration_roundtrip.DurationView.get_DurationView_d_days
              view) index) := by
  rcases hmatch with ⟨days, hours, minutes, seconds, millis,
    ⟨⟨⟨⟨⟨_, hdays⟩, _⟩, _⟩, _⟩, _⟩⟩
  rcases hdays with ⟨_, hfield⟩ | ⟨digits, _, hfield, hdigits⟩
  · rw [hfield]
    intro index hindex
    simp [Vermilion.Seq.len, Vermilion.Seq.empty] at hindex
    omega
  · rw [hfield]
    apply digit_sequence_range
    simpa [triptych_duration_roundtrip.duration_matches_DDays,
      triptych_duration_roundtrip.duration_is_wf_DDays] using hdigits

theorem dHours_range_of_components_match
    (components : Vermilion.Seq Int)
    (view : triptych_duration_roundtrip.DurationView)
    (hmatch :
      triptych_duration_roundtrip.duration_matches_Components components view) :
    ∀ index : Int,
      0 ≤ index ∧
          index < Vermilion.Seq.len
            (triptych_duration_roundtrip.DurationView.get_DurationView_d_hours
              view) →
        Vermilion.isUnicodeScalar
          (Vermilion.Seq.index
            (triptych_duration_roundtrip.DurationView.get_DurationView_d_hours
              view) index) := by
  rcases hmatch with ⟨days, hours, minutes, seconds, millis,
    ⟨⟨⟨⟨⟨_, _⟩, hhours⟩, _⟩, _⟩, _⟩⟩
  rcases hhours with ⟨_, hfield⟩ | ⟨digits, _, hfield, hdigits⟩
  · rw [hfield]
    intro index hindex
    simp [Vermilion.Seq.len, Vermilion.Seq.empty] at hindex
    omega
  · rw [hfield]
    apply digit_sequence_range
    simpa [triptych_duration_roundtrip.duration_matches_DHours,
      triptych_duration_roundtrip.duration_is_wf_DDays] using hdigits

theorem dMinutes_range_of_components_match
    (components : Vermilion.Seq Int)
    (view : triptych_duration_roundtrip.DurationView)
    (hmatch :
      triptych_duration_roundtrip.duration_matches_Components components view) :
    ∀ index : Int,
      0 ≤ index ∧
          index < Vermilion.Seq.len
            (triptych_duration_roundtrip.DurationView.get_DurationView_d_minutes
              view) →
        Vermilion.isUnicodeScalar
          (Vermilion.Seq.index
            (triptych_duration_roundtrip.DurationView.get_DurationView_d_minutes
              view) index) := by
  rcases hmatch with ⟨days, hours, minutes, seconds, millis,
    ⟨⟨⟨⟨⟨_, _⟩, _⟩, hminutes⟩, _⟩, _⟩⟩
  rcases hminutes with ⟨_, hfield⟩ | ⟨digits, _, hfield, hdigits⟩
  · rw [hfield]
    intro index hindex
    simp [Vermilion.Seq.len, Vermilion.Seq.empty] at hindex
    omega
  · rw [hfield]
    apply digit_sequence_range
    simpa [triptych_duration_roundtrip.duration_matches_DMinutes,
      triptych_duration_roundtrip.duration_is_wf_DDays] using hdigits

theorem dSeconds_range_of_components_match
    (components : Vermilion.Seq Int)
    (view : triptych_duration_roundtrip.DurationView)
    (hmatch :
      triptych_duration_roundtrip.duration_matches_Components components view) :
    ∀ index : Int,
      0 ≤ index ∧
          index < Vermilion.Seq.len
            (triptych_duration_roundtrip.DurationView.get_DurationView_d_seconds
              view) →
        Vermilion.isUnicodeScalar
          (Vermilion.Seq.index
            (triptych_duration_roundtrip.DurationView.get_DurationView_d_seconds
              view) index) := by
  rcases hmatch with ⟨days, hours, minutes, seconds, millis,
    ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hseconds⟩, _⟩⟩
  rcases hseconds with ⟨_, hfield⟩ | ⟨digits, _, hfield, hdigits⟩
  · rw [hfield]
    intro index hindex
    simp [Vermilion.Seq.len, Vermilion.Seq.empty] at hindex
    omega
  · rw [hfield]
    apply digit_sequence_range
    simpa [triptych_duration_roundtrip.duration_matches_DSeconds,
      triptych_duration_roundtrip.duration_is_wf_DDays] using hdigits

theorem dMillis_range_of_components_match
    (components : Vermilion.Seq Int)
    (view : triptych_duration_roundtrip.DurationView)
    (hmatch :
      triptych_duration_roundtrip.duration_matches_Components components view) :
    ∀ index : Int,
      0 ≤ index ∧
          index < Vermilion.Seq.len
            (triptych_duration_roundtrip.DurationView.get_DurationView_d_millis
              view) →
        Vermilion.isUnicodeScalar
          (Vermilion.Seq.index
            (triptych_duration_roundtrip.DurationView.get_DurationView_d_millis
              view) index) := by
  rcases hmatch with ⟨days, hours, minutes, seconds, millis,
    ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, hmillis⟩⟩
  rcases hmillis with ⟨_, hfield⟩ | ⟨digits, _, hfield, hdigits⟩
  · rw [hfield]
    intro index hindex
    simp [Vermilion.Seq.len, Vermilion.Seq.empty] at hindex
    omega
  · rw [hfield]
    apply digit_sequence_range
    simpa [triptych_duration_roundtrip.duration_matches_DMillis,
      triptych_duration_roundtrip.duration_is_wf_DDays] using hdigits

theorem normalize_matching_view (input : String)
    (condition : triptych_duration_roundtrip.DurationView → Prop) :
    (∃ view : triptych_duration_roundtrip.DurationView,
      triptych_duration_roundtrip.duration_matches_view
          (encodeString input) view ∧
        condition view) ↔
      ∃ signPart dDays dHours dMinutes dSeconds dMillis components : String,
        triptych_duration_roundtrip.duration_matches_view
            (encodeString input)
            (.DurationView (encodeString input) (encodeString signPart)
              (encodeString dDays) (encodeString dHours)
              (encodeString dMinutes) (encodeString dSeconds)
              (encodeString dMillis) (encodeString components)) ∧
          condition
            (.DurationView (encodeString input) (encodeString signPart)
              (encodeString dDays) (encodeString dHours)
              (encodeString dMinutes) (encodeString dSeconds)
              (encodeString dMillis) (encodeString components)) := by
  constructor
  · rintro ⟨view, hmatch, hcondition⟩
    cases view with
    | DurationView viewInput signSequence dDaysSequence dHoursSequence
        dMinutesSequence dSecondsSequence dMillisSequence componentsSequence =>
      rcases hmatch with ⟨hviewInput, signWitness, componentsWitness,
        ⟨⟨hinput, ⟨hsignField, hsignMatch⟩⟩,
          ⟨hcomponentsField, hcomponentsMatch⟩⟩⟩
      simp only [
        triptych_duration_roundtrip.DurationView.get_DurationView_input]
          at hviewInput
      simp only [
        triptych_duration_roundtrip.DurationView.get_DurationView_sign]
          at hsignField
      simp only [
        triptych_duration_roundtrip.DurationView.get_DurationView_components]
          at hcomponentsField
      subst viewInput
      subst signWitness
      subst componentsWitness
      have hsignSpec :
          triptych_duration_roundtrip.duration_is_wf_Sign signSequence := by
        simpa [triptych_duration_roundtrip.duration_matches_Sign,
          triptych_duration_roundtrip.duration_is_wf_Sign] using hsignMatch
      have hcomponentsSpec :
          triptych_duration_roundtrip.duration_is_wf_Components
            componentsSequence :=
        components_match_is_wf componentsSequence
          (.DurationView (encodeString input) signSequence dDaysSequence
            dHoursSequence dMinutesSequence dSecondsSequence dMillisSequence
            componentsSequence)
          hcomponentsMatch
      let signPart := decodeSequence signSequence
      let dDays := decodeSequence dDaysSequence
      let dHours := decodeSequence dHoursSequence
      let dMinutes := decodeSequence dMinutesSequence
      let dSeconds := decodeSequence dSecondsSequence
      let dMillis := decodeSequence dMillisSequence
      let components := decodeSequence componentsSequence
      have hsignEncode : encodeString signPart = signSequence :=
        encode_decode_sequence signSequence
          (sign_sequence_range signSequence hsignSpec)
      have hdDaysEncode : encodeString dDays = dDaysSequence :=
        encode_decode_sequence dDaysSequence
          (dDays_range_of_components_match componentsSequence
            (.DurationView (encodeString input) signSequence dDaysSequence
              dHoursSequence dMinutesSequence dSecondsSequence dMillisSequence
              componentsSequence)
            hcomponentsMatch)
      have hdHoursEncode : encodeString dHours = dHoursSequence :=
        encode_decode_sequence dHoursSequence
          (dHours_range_of_components_match componentsSequence
            (.DurationView (encodeString input) signSequence dDaysSequence
              dHoursSequence dMinutesSequence dSecondsSequence dMillisSequence
              componentsSequence)
            hcomponentsMatch)
      have hdMinutesEncode : encodeString dMinutes = dMinutesSequence :=
        encode_decode_sequence dMinutesSequence
          (dMinutes_range_of_components_match componentsSequence
            (.DurationView (encodeString input) signSequence dDaysSequence
              dHoursSequence dMinutesSequence dSecondsSequence dMillisSequence
              componentsSequence)
            hcomponentsMatch)
      have hdSecondsEncode : encodeString dSeconds = dSecondsSequence :=
        encode_decode_sequence dSecondsSequence
          (dSeconds_range_of_components_match componentsSequence
            (.DurationView (encodeString input) signSequence dDaysSequence
              dHoursSequence dMinutesSequence dSecondsSequence dMillisSequence
              componentsSequence)
            hcomponentsMatch)
      have hdMillisEncode : encodeString dMillis = dMillisSequence :=
        encode_decode_sequence dMillisSequence
          (dMillis_range_of_components_match componentsSequence
            (.DurationView (encodeString input) signSequence dDaysSequence
              dHoursSequence dMinutesSequence dSecondsSequence dMillisSequence
              componentsSequence)
            hcomponentsMatch)
      have hcomponentsEncode : encodeString components = componentsSequence :=
        encode_decode_sequence componentsSequence
          (components_sequence_range componentsSequence hcomponentsSpec)
      refine ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis,
        components, ?_, ?_⟩
      · simpa [hsignEncode, hdDaysEncode, hdHoursEncode, hdMinutesEncode,
          hdSecondsEncode, hdMillisEncode, hcomponentsEncode] using
            ⟨rfl, signSequence, componentsSequence,
              ⟨⟨hinput, ⟨rfl, hsignMatch⟩⟩,
                ⟨rfl, hcomponentsMatch⟩⟩⟩
      · simpa [hsignEncode, hdDaysEncode, hdHoursEncode, hdMinutesEncode,
          hdSecondsEncode, hdMillisEncode, hcomponentsEncode] using hcondition
  · rintro ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis,
      components, hmatch, hcondition⟩
    exact ⟨.DurationView (encodeString input) (encodeString signPart)
      (encodeString dDays) (encodeString dHours) (encodeString dMinutes)
      (encodeString dSeconds) (encodeString dMillis)
      (encodeString components), hmatch, hcondition⟩

def cedarComponents (dDays dHours dMinutes dSeconds dMillis : String) :
    Cedar.Thm.Duration.Components :=
  { days := if dDays = "" then none else some dDays
    hours := if dHours = "" then none else some dHours
    minutes := if dMinutes = "" then none else some dMinutes
    seconds := if dSeconds = "" then none else some dSeconds
    milliseconds := if dMillis = "" then none else some dMillis }

theorem cedarComponents_wf
    (dDays dHours dMinutes dSeconds dMillis : String)
    (hdDays : digitSlot dDays) (hdHours : digitSlot dHours)
    (hdMinutes : digitSlot dMinutes) (hdSeconds : digitSlot dSeconds)
    (hdMillis : digitSlot dMillis) :
    Duration.GrammarView.ComponentsWf
      (cedarComponents dDays dHours dMinutes dSeconds dMillis) := by
  by_cases hDays : dDays = "" <;>
    by_cases hHours : dHours = "" <;>
      by_cases hMinutes : dMinutes = "" <;>
        by_cases hSeconds : dSeconds = "" <;>
          by_cases hMillis : dMillis = "" <;>
            simp_all [cedarComponents, Duration.GrammarView.ComponentsWf,
              Duration.GrammarView.OptionalDigitsWf, digitSlot]

theorem cedarComponents_asString
    (dDays dHours dMinutes dSeconds dMillis : String)
    (hdDays : digitSlot dDays) (hdHours : digitSlot dHours)
    (hdMinutes : digitSlot dMinutes) (hdSeconds : digitSlot dSeconds)
    (hdMillis : digitSlot dMillis) :
    (cedarComponents dDays dHours dMinutes dSeconds dMillis).asString =
      unitText dDays "d" ++ unitText dHours "h" ++
        unitText dMinutes "m" ++ unitText dSeconds "s" ++
          unitText dMillis "ms" := by
  by_cases hDays : dDays = "" <;>
    by_cases hHours : dHours = "" <;>
      by_cases hMinutes : dMinutes = "" <;>
        by_cases hSeconds : dSeconds = "" <;>
          by_cases hMillis : dMillis = "" <;>
            simp_all [cedarComponents, Cedar.Thm.Duration.Components.asString,
              Cedar.Thm.Duration.durationChunk, unitText]

theorem cedarComponents_value
    (signPart dDays dHours dMinutes dSeconds dMillis : String) :
    Duration.GrammarView.formatValue signPart
        (cedarComponents dDays dHours dMinutes dSeconds dMillis) =
      Duration.value signPart dDays dHours dMinutes dSeconds dMillis := by
  by_cases hDays : dDays = "" <;>
    by_cases hHours : dHours = "" <;>
      by_cases hMinutes : dMinutes = "" <;>
        by_cases hSeconds : dSeconds = "" <;>
          by_cases hMillis : dMillis = "" <;>
            simp_all [cedarComponents, Duration.GrammarView.formatValue,
              Duration.GrammarView.formatQuantity, Duration.value,
              Triptych.natOf, Triptych.readNat]

theorem optional_cedar_unitText (digits : Option String)
    (suffix : String)
    (hwf : Duration.GrammarView.OptionalDigitsWf digits) :
    Cedar.Thm.Duration.durationChunk digits suffix =
      unitText (digits.getD "") suffix := by
  cases digits with
  | none => simp [Cedar.Thm.Duration.durationChunk, unitText]
  | some digits =>
      change Triptych.IsDigits digits at hwf
      have hnonempty : digits ≠ "" := by
        intro hempty
        subst digits
        simpa [Triptych.IsDigits] using hwf
      simp [Cedar.Thm.Duration.durationChunk, unitText, hnonempty]

theorem optional_cedar_digitSlot (digits : Option String)
    (hwf : Duration.GrammarView.OptionalDigitsWf digits) :
    digitSlot (digits.getD "") := by
  cases digits with
  | none => exact Or.inl rfl
  | some digits => exact Or.inr hwf

theorem cedarOption_roundtrip (digits : Option String)
    (hwf : Duration.GrammarView.OptionalDigitsWf digits) :
    (if digits.getD "" = "" then none else some (digits.getD "")) = digits := by
  cases digits with
  | none => simp
  | some digits =>
      change Triptych.IsDigits digits at hwf
      have hnonempty : digits ≠ "" := by
        intro hempty
        subst digits
        simpa [Triptych.IsDigits] using hwf
      simp [hnonempty]

theorem cedarComponents_roundtrip
    (components : Cedar.Thm.Duration.Components)
    (hwf : Duration.GrammarView.ComponentsWf components) :
    cedarComponents (components.days.getD "") (components.hours.getD "")
        (components.minutes.getD "") (components.seconds.getD "")
        (components.milliseconds.getD "") =
      components := by
  rcases components with ⟨days, hours, minutes, seconds, milliseconds⟩
  rcases hwf with ⟨hDays, hHours, hMinutes, hSeconds, hMillis⟩
  simp only [cedarComponents]
  rw [cedarOption_roundtrip days hDays, cedarOption_roundtrip hours hHours,
    cedarOption_roundtrip minutes hMinutes,
    cedarOption_roundtrip seconds hSeconds,
    cedarOption_roundtrip milliseconds hMillis]

theorem durationParts_of_cedar
    (input signPart : String) (components : Cedar.Thm.Duration.Components)
    (hinput : input = signPart ++ components.asString)
    (hsign : signPart = "-" ∨ signPart = "")
    (hwf : Duration.GrammarView.ComponentsWf components) :
    durationParts input signPart (components.days.getD "")
      (components.hours.getD "") (components.minutes.getD "")
      (components.seconds.getD "") (components.milliseconds.getD "")
      components.asString := by
  rcases hwf with ⟨hDays, hHours, hMinutes, hSeconds, hMillis⟩
  refine ⟨hinput, hsign, ?_,
    optional_cedar_digitSlot components.days hDays,
    optional_cedar_digitSlot components.hours hHours,
    optional_cedar_digitSlot components.minutes hMinutes,
    optional_cedar_digitSlot components.seconds hSeconds,
    optional_cedar_digitSlot components.milliseconds hMillis⟩
  rw [Cedar.Thm.Duration.Components.asString,
    optional_cedar_unitText components.days "d" hDays,
    optional_cedar_unitText components.hours "h" hHours,
    optional_cedar_unitText components.minutes "m" hMinutes,
    optional_cedar_unitText components.seconds "s" hSeconds,
    optional_cedar_unitText components.milliseconds "ms" hMillis]

theorem source_satisfies_wf_constraints_parts (input : String)
    (hwf : Duration.IsWf.Duration input) :
    Duration.SatisfiesWfConstraints input ↔
      ∃ signPart dDays dHours dMinutes dSeconds dMillis components : String,
        durationParts input signPart dDays dHours dMinutes dSeconds dMillis
            components ∧
          Duration.WfConstraints components := by
  obtain ⟨decodedSign, decodedComponents, hdecode, hdecodedSign,
    hdecodedInput, hdecodedWf⟩ :=
      Duration.GrammarView.decode_parts_of_surface_wf hwf
  constructor
  · intro hconstraints
    have hnonempty : decodedComponents.asString ≠ "" :=
      (Duration.GrammarView.wf_constraints_of_decode input decodedSign
        decodedComponents hdecode).1 hconstraints
    exact ⟨decodedSign, decodedComponents.days.getD "",
      decodedComponents.hours.getD "", decodedComponents.minutes.getD "",
      decodedComponents.seconds.getD "",
      decodedComponents.milliseconds.getD "", decodedComponents.asString,
      durationParts_of_cedar input decodedSign decodedComponents
        hdecodedInput hdecodedSign hdecodedWf, hnonempty⟩
  · rintro ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis,
      components, hparts, hnonempty⟩
    rcases hparts with ⟨hinput, hsign, hcomponents, hdDays, hdHours,
      hdMinutes, hdSeconds, hdMillis⟩
    let supplied :=
      cedarComponents dDays dHours dMinutes dSeconds dMillis
    have hsuppliedWf : Duration.GrammarView.ComponentsWf supplied :=
      cedarComponents_wf dDays dHours dMinutes dSeconds dMillis
        hdDays hdHours hdMinutes hdSeconds hdMillis
    have hsuppliedString : supplied.asString = components := by
      rw [cedarComponents_asString dDays dHours dMinutes dSeconds dMillis
        hdDays hdHours hdMinutes hdSeconds hdMillis]
      exact hcomponents.symm
    have hsuppliedInput : input = signPart ++ supplied.asString := by
      rw [hsuppliedString]
      exact hinput
    have hunique :=
      Duration.RuleRegistryProof.rendered_parts_unique
        hsign hdecodedSign hsuppliedInput hdecodedInput
        hsuppliedWf hdecodedWf
    apply (Duration.GrammarView.wf_constraints_of_decode input decodedSign
      decodedComponents hdecode).2
    rw [← hunique.2, hsuppliedString]
    exact hnonempty

theorem source_satisfies_constraints_parts (input : String)
    (hwf : Duration.IsWf.Duration input) :
    Duration.SatisfiesConstraints input ↔
      ∃ signPart dDays dHours dMinutes dSeconds dMillis components : String,
        durationParts input signPart dDays dHours dMinutes dSeconds dMillis
            components ∧
          Duration.Constraints signPart dDays dHours dMinutes dSeconds
            dMillis := by
  obtain ⟨decodedSign, decodedComponents, hdecode, hdecodedSign,
    hdecodedInput, hdecodedWf⟩ :=
      Duration.GrammarView.decode_parts_of_surface_wf hwf
  constructor
  · intro hconstraints
    have hbounds :=
      (Duration.GrammarView.constraints_of_decode input decodedSign
        decodedComponents hdecode).1 hconstraints
    refine ⟨decodedSign, decodedComponents.days.getD "",
      decodedComponents.hours.getD "", decodedComponents.minutes.getD "",
      decodedComponents.seconds.getD "",
      decodedComponents.milliseconds.getD "", decodedComponents.asString,
      durationParts_of_cedar input decodedSign decodedComponents
        hdecodedInput hdecodedSign hdecodedWf, ?_⟩
    unfold Duration.Constraints
    rw [← cedarComponents_value decodedSign
      (decodedComponents.days.getD "") (decodedComponents.hours.getD "")
      (decodedComponents.minutes.getD "")
      (decodedComponents.seconds.getD "")
      (decodedComponents.milliseconds.getD "")]
    rw [cedarComponents_roundtrip decodedComponents hdecodedWf]
    exact hbounds
  · rintro ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis,
      components, hparts, hconstraints⟩
    rcases hparts with ⟨hinput, hsign, hcomponents, hdDays, hdHours,
      hdMinutes, hdSeconds, hdMillis⟩
    let supplied :=
      cedarComponents dDays dHours dMinutes dSeconds dMillis
    have hsuppliedWf : Duration.GrammarView.ComponentsWf supplied :=
      cedarComponents_wf dDays dHours dMinutes dSeconds dMillis
        hdDays hdHours hdMinutes hdSeconds hdMillis
    have hsuppliedString : supplied.asString = components := by
      rw [cedarComponents_asString dDays dHours dMinutes dSeconds dMillis
        hdDays hdHours hdMinutes hdSeconds hdMillis]
      exact hcomponents.symm
    have hsuppliedInput : input = signPart ++ supplied.asString := by
      rw [hsuppliedString]
      exact hinput
    have hunique :=
      Duration.RuleRegistryProof.rendered_parts_unique
        hsign hdecodedSign hsuppliedInput hdecodedInput
        hsuppliedWf hdecodedWf
    apply (Duration.GrammarView.constraints_of_decode input decodedSign
      decodedComponents hdecode).2
    rw [← hunique.1, ← hunique.2]
    unfold Duration.Constraints at hconstraints
    rw [← cedarComponents_value signPart dDays dHours dMinutes dSeconds
      dMillis] at hconstraints
    exact hconstraints

theorem duration_satisfies_wf_constraints_equiv (input : String)
    (hwf : Duration.IsWf.Duration input) :
    Duration.SatisfiesWfConstraints input ↔
      triptych_duration_roundtrip.duration_satisfies_wf_constraints
        (encodeString input) := by
  rw [source_satisfies_wf_constraints_parts input hwf]
  unfold triptych_duration_roundtrip.duration_satisfies_wf_constraints
  rw [normalize_matching_view input
    triptych_duration_roundtrip.duration_view_wf_constraints]
  constructor
  · rintro ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis,
      components, hparts, hconstraints⟩
    refine ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis,
      components, (matches_view_equiv input signPart dDays dHours dMinutes
        dSeconds dMillis components).2 hparts, ?_⟩
    change
      triptych_duration_roundtrip.duration_wf_constraints
        (encodeString components)
    exact (duration_wf_constraints_equiv components).1 hconstraints
  · rintro ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis,
      components, hmatch, hconstraints⟩
    refine ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis,
      components, (matches_view_equiv input signPart dDays dHours dMinutes
        dSeconds dMillis components).1 hmatch, ?_⟩
    change
      triptych_duration_roundtrip.duration_wf_constraints
        (encodeString components) at hconstraints
    exact (duration_wf_constraints_equiv components).2 hconstraints

theorem duration_satisfies_constraints_equiv (input : String)
    (hwf : Duration.IsWf.Duration input) :
    Duration.SatisfiesConstraints input ↔
      triptych_duration_roundtrip.duration_satisfies_constraints
        (encodeString input) := by
  rw [source_satisfies_constraints_parts input hwf]
  unfold triptych_duration_roundtrip.duration_satisfies_constraints
  rw [normalize_matching_view input
    triptych_duration_roundtrip.duration_view_constraints]
  constructor
  · rintro ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis,
      components, hparts, hconstraints⟩
    refine ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis,
      components, (matches_view_equiv input signPart dDays dHours dMinutes
        dSeconds dMillis components).2 hparts, ?_⟩
    change
      triptych_duration_roundtrip.duration_constraints
        (encodeString signPart) (encodeString dDays) (encodeString dHours)
        (encodeString dMinutes) (encodeString dSeconds)
        (encodeString dMillis)
    exact
      (duration_constraints_equiv signPart dDays dHours dMinutes dSeconds
        dMillis).1 hconstraints
  · rintro ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis,
      components, hmatch, hconstraints⟩
    refine ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis,
      components, (matches_view_equiv input signPart dDays dHours dMinutes
        dSeconds dMillis components).1 hmatch, ?_⟩
    change
      triptych_duration_roundtrip.duration_constraints
        (encodeString signPart) (encodeString dDays) (encodeString dHours)
        (encodeString dMinutes) (encodeString dSeconds)
        (encodeString dMillis) at hconstraints
    exact
      (duration_constraints_equiv signPart dDays dHours dMinutes dSeconds
        dMillis).2 hconstraints

theorem duration_is_wf_equiv (input : String) :
    Duration.IsWf input ↔
      triptych_duration_roundtrip.duration_is_wf (encodeString input) := by
  change
    (Duration.IsWf.Duration input ∧
        Duration.SatisfiesWfConstraints input) ↔
      (triptych_duration_roundtrip.duration_is_wf_Duration
          (encodeString input) ∧
        triptych_duration_roundtrip.duration_satisfies_wf_constraints
          (encodeString input))
  constructor
  · rintro ⟨hgrammar, hconstraints⟩
    exact ⟨(duration_equiv input).1 hgrammar,
      (duration_satisfies_wf_constraints_equiv input hgrammar).1
        hconstraints⟩
  · rintro ⟨hgrammar, hconstraints⟩
    have hsourceGrammar := (duration_equiv input).2 hgrammar
    exact ⟨hsourceGrammar,
      (duration_satisfies_wf_constraints_equiv input hsourceGrammar).2
        hconstraints⟩

theorem duration_is_valid_equiv (input : String) :
    Duration.IsValid input ↔
      triptych_duration_roundtrip.duration_is_valid
        (encodeString input) := by
  change
    (Duration.IsWf input ∧ Duration.SatisfiesConstraints input) ↔
      (triptych_duration_roundtrip.duration_is_wf (encodeString input) ∧
        triptych_duration_roundtrip.duration_satisfies_constraints
          (encodeString input))
  constructor
  · rintro ⟨hwellFormed, hconstraints⟩
    exact ⟨(duration_is_wf_equiv input).1 hwellFormed,
      (duration_satisfies_constraints_equiv input hwellFormed.1).1
        hconstraints⟩
  · rintro ⟨hwellFormed, hconstraints⟩
    have hsourceWf := (duration_is_wf_equiv input).2 hwellFormed
    exact ⟨hsourceWf,
      (duration_satisfies_constraints_equiv input hsourceWf.1).2
        hconstraints⟩

theorem components_of_parts
    (input signPart dDays dHours dMinutes dSeconds dMillis components :
      String)
    (hparts :
      durationParts input signPart dDays dHours dMinutes dSeconds dMillis
        components) :
    Triptych.component Duration.grammar input "Sign" = signPart ∧
      Triptych.component Duration.grammar input "DDays" = dDays ∧
      Triptych.component Duration.grammar input "DHours" = dHours ∧
      Triptych.component Duration.grammar input "DMinutes" = dMinutes ∧
      Triptych.component Duration.grammar input "DSeconds" = dSeconds ∧
      Triptych.component Duration.grammar input "DMillis" = dMillis ∧
      Triptych.component Duration.grammar input "Components" = components := by
  rcases hparts with ⟨hinput, hsign, hcomponents, hdDays, hdHours,
    hdMinutes, hdSeconds, hdMillis⟩
  let supplied := cedarComponents dDays dHours dMinutes dSeconds dMillis
  have hsuppliedWf : Duration.GrammarView.ComponentsWf supplied :=
    cedarComponents_wf dDays dHours dMinutes dSeconds dMillis hdDays hdHours
      hdMinutes hdSeconds hdMillis
  have hsuppliedString : supplied.asString = components := by
    rw [cedarComponents_asString dDays dHours dMinutes dSeconds dMillis
      hdDays hdHours hdMinutes hdSeconds hdMillis]
    exact hcomponents.symm
  have hsuppliedInput : input = signPart ++ supplied.asString := by
    rw [hsuppliedString]
    exact hinput
  have hgrammar : Duration.IsWf.Duration input :=
    (duration_parts_exists_equiv input).2
      ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis, components,
        hinput, hsign, hcomponents, hdDays, hdHours, hdMinutes, hdSeconds,
        hdMillis⟩
  obtain ⟨decodedSign, decodedComponents, hdecode, hdecodedSign,
      hdecodedInput, hdecodedWf⟩ :=
    Duration.GrammarView.decode_parts_of_surface_wf hgrammar
  have hunique :=
    Duration.RuleRegistryProof.rendered_parts_unique hsign hdecodedSign
      hsuppliedInput hdecodedInput hsuppliedWf hdecodedWf
  rcases hunique with ⟨rfl, rfl⟩
  simp only [Triptych.component_eq_of_decode hdecode]
  by_cases hDays : dDays = "" <;>
    by_cases hHours : dHours = "" <;>
      by_cases hMinutes : dMinutes = "" <;>
        by_cases hSeconds : dSeconds = "" <;>
          by_cases hMillis : dMillis = "" <;>
            simp_all [supplied, cedarComponents,
              Duration.GrammarView.componentsCaptures,
              Duration.GrammarView.unitCaptures, CaptureMap.toEnv, digitSlot]

theorem compute_value_of_parts
    (input signPart dDays dHours dMinutes dSeconds dMillis components :
      String)
    (hparts :
      durationParts input signPart dDays dHours dMinutes dSeconds dMillis
        components) :
    Duration.computeValue input =
      some
        (Duration.value signPart dDays dHours dMinutes dSeconds dMillis) := by
  obtain ⟨hs, hd, hh, hm, hsec, hms, hc⟩ :=
    components_of_parts input signPart dDays dHours dMinutes dSeconds dMillis
      components hparts
  have hgrammar : Duration.IsWf.Duration input :=
    (duration_parts_exists_equiv input).2
      ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis, components,
        hparts⟩
  have hengine : Triptych.IsWf Duration.grammar input :=
    (Duration.IsWfGrammar_equiv input).mpr hgrammar
  have hsome : (decode Duration.grammar input).isSome = true :=
    (decodeSome_iff_IsWf Duration.grammar (by decide) input).mpr hengine
  obtain ⟨captures, hdecode⟩ := Option.isSome_iff_exists.mp hsome
  rw [Duration.computeValue_eq, hdecode]
  simpa only [Option.map_some, hs, hd, hh, hm, hsec, hms]

theorem duration_is_wf_DHours_equiv :
    ∀ source : String,
      Duration.IsWf.DHours source ↔
        Recovered.duration_is_wf_DHours (encodeString source) := by
  intro source
  simpa [Duration.IsWf.DHours,
    triptych_duration_roundtrip.duration_is_wf_DHours,
    triptych_duration_roundtrip.duration_is_wf_DDays] using
      digit_run_equiv source

theorem duration_is_wf_DMinutes_equiv :
    ∀ source : String,
      Duration.IsWf.DMinutes source ↔
        Recovered.duration_is_wf_DMinutes (encodeString source) := by
  intro source
  simpa [Duration.IsWf.DMinutes,
    triptych_duration_roundtrip.duration_is_wf_DMinutes,
    triptych_duration_roundtrip.duration_is_wf_DDays] using
      digit_run_equiv source

theorem duration_is_wf_DSeconds_equiv :
    ∀ source : String,
      Duration.IsWf.DSeconds source ↔
        Recovered.duration_is_wf_DSeconds (encodeString source) := by
  intro source
  simpa [Duration.IsWf.DSeconds,
    triptych_duration_roundtrip.duration_is_wf_DSeconds,
    triptych_duration_roundtrip.duration_is_wf_DDays] using
      digit_run_equiv source

theorem duration_is_wf_DMillis_equiv :
    ∀ source : String,
      Duration.IsWf.DMillis source ↔
        Recovered.duration_is_wf_DMillis (encodeString source) := by
  intro source
  simpa [Duration.IsWf.DMillis,
    triptych_duration_roundtrip.duration_is_wf_DMillis,
    triptych_duration_roundtrip.duration_is_wf_DDays] using
      digit_run_equiv source

theorem view_denotation_equiv :
    ∀ input signPart dDays dHours dMinutes dSeconds dMillis components : String,
      Recovered.duration_view_denotation
          (Recovered.mkDurationView (encodeString input)
            (encodeString signPart) (encodeString dDays) (encodeString dHours)
            (encodeString dMinutes) (encodeString dSeconds)
            (encodeString dMillis) (encodeString components)) =
        Duration.value signPart dDays dHours dMinutes dSeconds dMillis := by
  intro input signPart dDays dHours dMinutes dSeconds dMillis components
  simpa [triptych_duration_roundtrip.duration_view_denotation] using
    (duration_value_equiv signPart dDays dHours dMinutes dSeconds
      dMillis).symm

theorem view_valid_equiv :
    ∀ input signPart dDays dHours dMinutes dSeconds dMillis components : String,
      Recovered.duration_view_valid
          (Recovered.mkDurationView (encodeString input)
            (encodeString signPart) (encodeString dDays) (encodeString dHours)
            (encodeString dMinutes) (encodeString dSeconds)
            (encodeString dMillis) (encodeString components)) ↔
        (Duration.WfConstraints components ∧
          Duration.Constraints signPart dDays dHours dMinutes dSeconds
            dMillis) := by
  intro input signPart dDays dHours dMinutes dSeconds dMillis components
  change
    (triptych_duration_roundtrip.duration_wf_constraints
        (encodeString components) ∧
      triptych_duration_roundtrip.duration_constraints
        (encodeString signPart) (encodeString dDays) (encodeString dHours)
        (encodeString dMinutes) (encodeString dSeconds)
        (encodeString dMillis)) ↔
      Duration.WfConstraints components ∧
        Duration.Constraints signPart dDays dHours dMinutes dSeconds dMillis
  rw [← duration_wf_constraints_equiv,
    ← duration_constraints_equiv]

theorem matching_view_normalizes_equiv :
    ∀ input : String, ∀ view : Recovered.DurationView,
      Recovered.duration_matches_view (encodeString input) view →
        ∃ signPart dDays dHours dMinutes dSeconds dMillis components : String,
          view =
            Recovered.mkDurationView (encodeString input)
              (encodeString signPart) (encodeString dDays)
              (encodeString dHours) (encodeString dMinutes)
              (encodeString dSeconds) (encodeString dMillis)
              (encodeString components) := by
  intro input view hmatch
  obtain ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis, components,
      _, heq⟩ :=
    (normalize_matching_view input (fun candidate => candidate = view)).1
      ⟨view, hmatch, rfl⟩
  exact ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis, components,
    heq.symm⟩

theorem matches_view_exact_equiv :
    ∀ input signPart dDays dHours dMinutes dSeconds dMillis components :
      String,
      Recovered.duration_matches_view (encodeString input)
          (Recovered.mkDurationView (encodeString input)
            (encodeString signPart) (encodeString dDays)
            (encodeString dHours) (encodeString dMinutes)
            (encodeString dSeconds) (encodeString dMillis)
            (encodeString components)) ↔
        (((((((Duration.IsWf.Duration input ∧
                    Triptych.component Duration.grammar input "Sign" =
                      signPart) ∧
                  Triptych.component Duration.grammar input "DDays" =
                    dDays) ∧
                Triptych.component Duration.grammar input "DHours" =
                  dHours) ∧
              Triptych.component Duration.grammar input "DMinutes" =
                dMinutes) ∧
            Triptych.component Duration.grammar input "DSeconds" =
              dSeconds) ∧
          Triptych.component Duration.grammar input "DMillis" = dMillis) ∧
        Triptych.component Duration.grammar input "Components" = components) := by
  intro input signPart dDays dHours dMinutes dSeconds dMillis components
  change
    triptych_duration_roundtrip.duration_matches_view (encodeString input)
        (.DurationView (encodeString input) (encodeString signPart)
          (encodeString dDays) (encodeString dHours) (encodeString dMinutes)
          (encodeString dSeconds) (encodeString dMillis)
          (encodeString components)) ↔ _
  rw [matches_view_equiv]
  constructor
  · intro hparts
    obtain ⟨hs, hd, hh, hm, hsec, hms, hc⟩ :=
      components_of_parts input signPart dDays dHours dMinutes dSeconds
        dMillis components hparts
    exact ⟨⟨⟨⟨⟨⟨⟨(duration_parts_exists_equiv input).2
      ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis, components,
        hparts⟩, hs⟩, hd⟩, hh⟩, hm⟩, hsec⟩, hms⟩, hc⟩
  · rintro ⟨⟨⟨⟨⟨⟨⟨hgrammar, hs⟩, hd⟩, hh⟩, hm⟩, hsec⟩, hms⟩, hc⟩
    obtain ⟨sign', days', hours', minutes', seconds', millis', components',
      hparts⟩ := (duration_parts_exists_equiv input).1 hgrammar
    obtain ⟨hs', hd', hh', hm', hsec', hms', hc'⟩ :=
      components_of_parts input sign' days' hours' minutes' seconds' millis'
        components' hparts
    have es : sign' = signPart := hs'.symm.trans hs
    have ed : days' = dDays := hd'.symm.trans hd
    have eh : hours' = dHours := hh'.symm.trans hh
    have em : minutes' = dMinutes := hm'.symm.trans hm
    have esec : seconds' = dSeconds := hsec'.symm.trans hsec
    have ems : millis' = dMillis := hms'.symm.trans hms
    have ec : components' = components := hc'.symm.trans hc
    simpa only [es, ed, eh, em, esec, ems, ec] using hparts

theorem matches_result_equiv :
    ∀ input : String, ∀ result : Int,
      (Duration.IsValid input ∧
          Duration.computeValue input = some result) ↔
        Recovered.duration_matches_result (encodeString input) result := by
  intro input result
  change
    (Duration.IsValid input ∧ Duration.computeValue input = some result) ↔
      triptych_duration_roundtrip.duration_matches_result
        (encodeString input) result
  unfold triptych_duration_roundtrip.duration_matches_result
  constructor
  · rintro
      ⟨⟨⟨hgrammar, hsourceWf⟩, hsourceConstraints⟩, hcompute⟩
    obtain ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis, components,
      hparts⟩ := (duration_parts_exists_equiv input).1 hgrammar
    obtain ⟨hs, hd, hh, hm, hsec, hms, hc⟩ :=
      components_of_parts input signPart dDays dHours dMinutes dSeconds
        dMillis components hparts
    have hwfConstraints : Duration.WfConstraints components := by
      unfold Duration.SatisfiesWfConstraints at hsourceWf
      simpa only [hc] using hsourceWf
    have hconstraints :
        Duration.Constraints signPart dDays dHours dMinutes dSeconds
          dMillis := by
      unfold Duration.SatisfiesConstraints at hsourceConstraints
      simpa only [hs, hd, hh, hm, hsec, hms] using hsourceConstraints
    have hvalue :
        Duration.value signPart dDays dHours dMinutes dSeconds dMillis =
          result := by
      rw [compute_value_of_parts input signPart dDays dHours dMinutes
        dSeconds dMillis components hparts] at hcompute
      exact Option.some.inj hcompute
    let view :=
      triptych_duration_roundtrip.DurationView.DurationView
        (encodeString input) (encodeString signPart) (encodeString dDays)
        (encodeString dHours) (encodeString dMinutes) (encodeString dSeconds)
        (encodeString dMillis) (encodeString components)
    refine ⟨view, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · exact (matches_view_equiv input signPart dDays dHours dMinutes
        dSeconds dMillis components).2 hparts
    · exact (view_valid_equiv input signPart dDays dHours dMinutes dSeconds dMillis
        components).2 ⟨hwfConstraints, hconstraints⟩
    · exact (view_denotation_equiv input signPart dDays dHours dMinutes dSeconds
        dMillis components).trans hvalue
  · rintro ⟨view, ⟨⟨hmatch, hviewValid⟩, hdenotation⟩⟩
    obtain ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis, components,
      heq⟩ := matching_view_normalizes_equiv input view hmatch
    subst view
    have hparts :=
      (matches_view_equiv input signPart dDays dHours dMinutes dSeconds
        dMillis components).1 hmatch
    obtain ⟨hs, hd, hh, hm, hsec, hms, hc⟩ :=
      components_of_parts input signPart dDays dHours dMinutes dSeconds
        dMillis components hparts
    obtain ⟨hwfConstraints, hconstraints⟩ :=
      (view_valid_equiv input signPart dDays dHours dMinutes dSeconds dMillis
        components).1 hviewValid
    have hgrammar : Duration.IsWf.Duration input :=
      (duration_parts_exists_equiv input).2
        ⟨signPart, dDays, dHours, dMinutes, dSeconds, dMillis, components,
          hparts⟩
    have hsatisfiesWf : Duration.SatisfiesWfConstraints input := by
      unfold Duration.SatisfiesWfConstraints
      simpa only [hc] using hwfConstraints
    have hsatisfies : Duration.SatisfiesConstraints input := by
      unfold Duration.SatisfiesConstraints
      simpa only [hs, hd, hh, hm, hsec, hms] using hconstraints
    have hvalue :
        Duration.value signPart dDays dHours dMinutes dSeconds dMillis =
          result :=
      (view_denotation_equiv input signPart dDays dHours dMinutes dSeconds dMillis
        components).symm.trans hdenotation
    refine ⟨⟨⟨hgrammar, hsatisfiesWf⟩, hsatisfies⟩, ?_⟩
    rw [compute_value_of_parts input signPart dDays dHours dMinutes dSeconds
      dMillis components hparts]
    exact congrArg some hvalue

end Triptych.Vermilion.Proofs.Duration
