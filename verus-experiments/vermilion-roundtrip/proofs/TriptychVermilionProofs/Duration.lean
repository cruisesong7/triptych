import TriptychVermilionGenerated.Duration
import TriptychVermilionProofs.Duration.Lemmas

namespace Triptych.Vermilion.Proofs.Duration

open Triptych
open Triptych.Vermilion.String
open Triptych.Vermilion.Generated.Duration

theorem duration_is_wf_Duration :
    ∀ source : String,
      Duration.IsWf.Duration source ↔
        Recovered.duration_is_wf_Duration (encodeString source) :=
  duration_equiv

theorem duration_is_wf_Sign :
    ∀ source : String,
      Duration.IsWf.Sign source ↔
        Recovered.duration_is_wf_Sign (encodeString source) :=
  sign_equiv

theorem duration_is_wf_Components :
    ∀ source : String,
      Duration.IsWf.Components source ↔
        Recovered.duration_is_wf_Components (encodeString source) :=
  components_equiv

theorem duration_is_wf_Days :
    ∀ source : String,
      Duration.IsWf.Days source ↔
        Recovered.duration_is_wf_Days (encodeString source) :=
  days_equiv

theorem duration_is_wf_Hours :
    ∀ source : String,
      Duration.IsWf.Hours source ↔
        Recovered.duration_is_wf_Hours (encodeString source) :=
  hours_equiv

theorem duration_is_wf_Minutes :
    ∀ source : String,
      Duration.IsWf.Minutes source ↔
        Recovered.duration_is_wf_Minutes (encodeString source) :=
  minutes_equiv

theorem duration_is_wf_Seconds :
    ∀ source : String,
      Duration.IsWf.Seconds source ↔
        Recovered.duration_is_wf_Seconds (encodeString source) :=
  seconds_equiv

theorem duration_is_wf_Millis :
    ∀ source : String,
      Duration.IsWf.Millis source ↔
        Recovered.duration_is_wf_Millis (encodeString source) :=
  millis_equiv

theorem duration_is_wf_DDays :
    ∀ source : String,
      Duration.IsWf.DDays source ↔
        Recovered.duration_is_wf_DDays (encodeString source) :=
  digit_run_equiv

theorem duration_is_wf_DHours :
    ∀ source : String,
      Duration.IsWf.DHours source ↔
        Recovered.duration_is_wf_DHours (encodeString source) :=
  duration_is_wf_DHours_equiv

theorem duration_is_wf_DMinutes :
    ∀ source : String,
      Duration.IsWf.DMinutes source ↔
        Recovered.duration_is_wf_DMinutes (encodeString source) :=
  duration_is_wf_DMinutes_equiv

theorem duration_is_wf_DSeconds :
    ∀ source : String,
      Duration.IsWf.DSeconds source ↔
        Recovered.duration_is_wf_DSeconds (encodeString source) :=
  duration_is_wf_DSeconds_equiv

theorem duration_is_wf_DMillis :
    ∀ source : String,
      Duration.IsWf.DMillis source ↔
        Recovered.duration_is_wf_DMillis (encodeString source) :=
  duration_is_wf_DMillis_equiv

theorem duration_value :
    ∀ signPart dDays dHours dMinutes dSeconds dMillis : String,
      Duration.value signPart dDays dHours dMinutes dSeconds dMillis =
        Recovered.duration_value (encodeString signPart) (encodeString dDays)
          (encodeString dHours) (encodeString dMinutes)
          (encodeString dSeconds) (encodeString dMillis) :=
  duration_value_equiv

theorem duration_wf_constraints :
    ∀ components : String,
      Duration.WfConstraints components ↔
        Recovered.duration_wf_constraints (encodeString components) :=
  duration_wf_constraints_equiv

theorem duration_satisfies_wf_constraints :
    ∀ source : String,
      Duration.IsWf.Duration source →
        (Duration.SatisfiesWfConstraints source ↔
          Recovered.duration_satisfies_wf_constraints (encodeString source)) :=
  duration_satisfies_wf_constraints_equiv

theorem duration_constraints :
    ∀ signPart dDays dHours dMinutes dSeconds dMillis : String,
      Duration.Constraints signPart dDays dHours dMinutes dSeconds dMillis ↔
        Recovered.duration_constraints (encodeString signPart)
          (encodeString dDays) (encodeString dHours) (encodeString dMinutes)
          (encodeString dSeconds) (encodeString dMillis) :=
  duration_constraints_equiv

theorem duration_satisfies_constraints :
    ∀ source : String,
      Duration.IsWf.Duration source →
        (Duration.SatisfiesConstraints source ↔
          Recovered.duration_satisfies_constraints (encodeString source)) :=
  duration_satisfies_constraints_equiv

theorem duration_is_wf :
    ∀ source : String,
      Duration.IsWf source ↔
        Recovered.duration_is_wf (encodeString source) :=
  duration_is_wf_equiv

theorem duration_is_valid :
    ∀ source : String,
      Duration.IsValid source ↔
        Recovered.duration_is_valid (encodeString source) :=
  duration_is_valid_equiv

theorem view_denotation :
    ∀ input signPart dDays dHours dMinutes dSeconds dMillis components : String,
      Recovered.duration_view_denotation
          (Recovered.mkDurationView (encodeString input)
            (encodeString signPart) (encodeString dDays) (encodeString dHours)
            (encodeString dMinutes) (encodeString dSeconds)
            (encodeString dMillis) (encodeString components)) =
        Duration.value signPart dDays dHours dMinutes dSeconds dMillis :=
  view_denotation_equiv

theorem view_valid :
    ∀ input signPart dDays dHours dMinutes dSeconds dMillis components : String,
      Recovered.duration_view_valid
          (Recovered.mkDurationView (encodeString input)
            (encodeString signPart) (encodeString dDays) (encodeString dHours)
            (encodeString dMinutes) (encodeString dSeconds)
            (encodeString dMillis) (encodeString components)) ↔
        (Duration.WfConstraints components ∧
          Duration.Constraints signPart dDays dHours dMinutes dSeconds
            dMillis) :=
  view_valid_equiv

theorem matching_view_normalizes :
    ∀ input : String, ∀ view : Recovered.DurationView,
      Recovered.duration_matches_view (encodeString input) view →
        ∃ signPart dDays dHours dMinutes dSeconds dMillis components : String,
          view =
            Recovered.mkDurationView (encodeString input)
              (encodeString signPart) (encodeString dDays)
              (encodeString dHours) (encodeString dMinutes)
              (encodeString dSeconds) (encodeString dMillis)
              (encodeString components) :=
  matching_view_normalizes_equiv

theorem matches_view_exact :
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
        Triptych.component Duration.grammar input "Components" = components) :=
  matches_view_exact_equiv

theorem matching_view_exists :
    ∀ input : String,
      Duration.IsWf.Duration input ↔
        ∃ signPart dDays dHours dMinutes dSeconds dMillis components : String,
          Recovered.duration_matches_view (encodeString input)
            (Recovered.mkDurationView (encodeString input)
              (encodeString signPart) (encodeString dDays)
              (encodeString dHours) (encodeString dMinutes)
              (encodeString dSeconds) (encodeString dMillis)
              (encodeString components)) :=
  matching_view_exists_equiv

theorem matches_result :
    ∀ input : String, ∀ result : Int,
      (Duration.IsValid input ∧
          Duration.computeValue input = some result) ↔
        Recovered.duration_matches_result (encodeString input) result :=
  matches_result_equiv

end Triptych.Vermilion.Proofs.Duration
