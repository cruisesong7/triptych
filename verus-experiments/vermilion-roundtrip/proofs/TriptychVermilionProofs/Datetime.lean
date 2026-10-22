import TriptychVermilionGenerated.Datetime
import TriptychVermilionProofs.Datetime.Lemmas

namespace Triptych.Vermilion.Proofs.Datetime

open Triptych
open Triptych.Vermilion.String
open Triptych.Vermilion.Generated.Datetime
open Datetime.GrammarView

theorem datetime_is_wf_Datetime :
    ∀ s0 : String, Datetime.IsWf.Datetime s0 ↔ Recovered.datetime_is_wf_Datetime (encodeString s0) :=
  datetime_equiv

theorem datetime_is_wf_Date :
    ∀ s0 : String, Datetime.IsWf.Date s0 ↔ Recovered.datetime_is_wf_Date (encodeString s0) :=
  date_equiv

theorem datetime_is_wf_Time :
    ∀ s0 : String, Datetime.IsWf.Time s0 ↔ Recovered.datetime_is_wf_Time (encodeString s0) :=
  time_equiv

theorem datetime_is_wf_Offset :
    ∀ s0 : String, Datetime.IsWf.Offset s0 ↔ Recovered.datetime_is_wf_Offset (encodeString s0) :=
  offset_equiv

theorem datetime_is_wf_SSS :
    ∀ s0 : String, Datetime.IsWf.SSS s0 ↔ Recovered.datetime_is_wf_SSS (encodeString s0) :=
  sss_equiv

theorem datetime_is_wf_YYYY :
    ∀ s0 : String, Datetime.IsWf.YYYY s0 ↔ Recovered.datetime_is_wf_YYYY (encodeString s0) :=
  yyyy_equiv

theorem datetime_is_wf_MM :
    ∀ s0 : String, Datetime.IsWf.MM s0 ↔ Recovered.datetime_is_wf_MM (encodeString s0) :=
  mm_equiv

theorem datetime_is_wf_DD :
    ∀ s0 : String, Datetime.IsWf.DD s0 ↔ Recovered.datetime_is_wf_DD (encodeString s0) :=
  dd_equiv

theorem datetime_is_wf_hh :
    ∀ s0 : String, Datetime.IsWf.hh s0 ↔ Recovered.datetime_is_wf_hh (encodeString s0) :=
  hh_equiv

theorem datetime_is_wf_mm :
    ∀ s0 : String, Datetime.IsWf.mm s0 ↔ Recovered.datetime_is_wf_mm (encodeString s0) :=
  minute_equiv

theorem datetime_is_wf_ss :
    ∀ s0 : String, Datetime.IsWf.ss s0 ↔ Recovered.datetime_is_wf_ss (encodeString s0) :=
  ss_equiv

theorem datetime_value :
    ∀ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : String, Datetime.value s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 = Recovered.datetime_value (encodeString s0) (encodeString s1) (encodeString s2) (encodeString s3) (encodeString s4) (encodeString s5) (encodeString s6) (encodeString s7) (encodeString s8) (encodeString s9) :=
  datetime_value_equiv

theorem datetime_wf_constraints :
    ∀ s0 s1 s2 s3 s4 s5 s6 s7 : String, Datetime.WfConstraints s0 s1 s2 s3 s4 s5 s6 s7 ↔ Recovered.datetime_wf_constraints (encodeString s0) (encodeString s1) (encodeString s2) (encodeString s3) (encodeString s4) (encodeString s5) (encodeString s6) (encodeString s7) :=
  datetime_wf_constraints_equiv

theorem datetime_satisfies_wf_constraints :
    ∀ s0 : String, Datetime.IsWf.Datetime s0 → (Datetime.SatisfiesWfConstraints s0 ↔ Recovered.datetime_satisfies_wf_constraints (encodeString s0)) :=
  datetime_satisfies_wf_constraints_equiv

theorem datetime_constraints :
    ∀ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : String, Datetime.Constraints s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ↔ Recovered.datetime_constraints (encodeString s0) (encodeString s1) (encodeString s2) (encodeString s3) (encodeString s4) (encodeString s5) (encodeString s6) (encodeString s7) (encodeString s8) (encodeString s9) :=
  datetime_constraints_equiv

theorem datetime_satisfies_constraints :
    ∀ s0 : String, Datetime.IsWf.Datetime s0 → (Datetime.SatisfiesConstraints s0 ↔ Recovered.datetime_satisfies_constraints (encodeString s0)) :=
  datetime_satisfies_constraints_equiv

theorem datetime_is_wf :
    ∀ s0 : String, Datetime.IsWf s0 ↔ Recovered.datetime_is_wf (encodeString s0) :=
  datetime_is_wf_equiv

theorem datetime_is_valid :
    ∀ s0 : String, Datetime.IsValid s0 ↔ Recovered.datetime_is_valid (encodeString s0) :=
  datetime_is_valid_equiv

theorem view_denotation :
    ∀ input s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : String, Recovered.datetime_view_denotation (Recovered.mkDatetimeView (encodeString input) (encodeString s0) (encodeString s1) (encodeString s2) (encodeString s3) (encodeString s4) (encodeString s5) (encodeString s6) (encodeString s7) (encodeString s8) (encodeString s9)) = Datetime.value s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 :=
  view_denotation_equiv

theorem view_valid :
    ∀ input s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : String, Recovered.datetime_view_valid (Recovered.mkDatetimeView (encodeString input) (encodeString s0) (encodeString s1) (encodeString s2) (encodeString s3) (encodeString s4) (encodeString s5) (encodeString s6) (encodeString s7) (encodeString s8) (encodeString s9)) ↔ (Datetime.WfConstraints s0 s3 s4 s5 s8 s9 s2 s1 ∧ Datetime.Constraints s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) :=
  view_valid_equiv

theorem matching_view_normalizes :
    ∀ input : String, ∀ view : Recovered.DatetimeView,
      Recovered.datetime_matches_view (encodeString input) view →
        ∃ mm yyyy dd timeHh timeMm ss sss offset offsetHh offsetMm : String,
          view =
            Recovered.mkDatetimeView (encodeString input) (encodeString mm)
              (encodeString yyyy) (encodeString dd) (encodeString timeHh)
              (encodeString timeMm) (encodeString ss) (encodeString sss)
              (encodeString offset) (encodeString offsetHh)
              (encodeString offsetMm) :=
  matching_view_normalizes_equiv

theorem matches_view_exact :
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
    Triptych.component Datetime.grammar input "Offset.mm" = offsetMm) :=
  matches_view_exact_equiv

theorem matching_view_exists :
    ∀ input : String, Datetime.IsWf.Datetime input ↔ ∃ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : String, Recovered.datetime_matches_view (encodeString input) (Recovered.mkDatetimeView (encodeString input) (encodeString s0) (encodeString s1) (encodeString s2) (encodeString s3) (encodeString s4) (encodeString s5) (encodeString s6) (encodeString s7) (encodeString s8) (encodeString s9)) :=
  matching_view_exists_equiv

theorem matches_result :
    ∀ input : String, ∀ result : Int,
      (Datetime.IsValid input ∧ Datetime.computeValue input = some result) ↔
        Recovered.datetime_matches_result (encodeString input) result :=
  matches_result_equiv

end Triptych.Vermilion.Proofs.Datetime
