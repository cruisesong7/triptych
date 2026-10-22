import TriptychVermilionGenerated.IPv4
import TriptychVermilionProofs.IPv4.Lemmas

namespace Triptych.Vermilion.Proofs.IPv4

open Triptych
open Triptych.Vermilion.String
open Triptych.Vermilion.Generated.IPv4
open IPv4.GrammarView

theorem ipv4_is_wf_V4Net :
    ∀ source : String,
      IPv4.IsWf.V4Net source ↔
        Recovered.ipv4_is_wf_V4Net (encodeString source) :=
  v4net_equiv

theorem ipv4_is_wf_V4Addr :
    ∀ source : String,
      IPv4.IsWf.V4Addr source ↔
        Recovered.ipv4_is_wf_V4Addr (encodeString source) :=
  v4addr_equiv

theorem ipv4_is_wf_Oct1 :
    ∀ source : String,
      IPv4.IsWf.Oct1 source ↔
        Recovered.ipv4_is_wf_Oct1 (encodeString source) :=
  oct1_equiv

theorem ipv4_is_wf_Oct2 :
    ∀ source : String,
      IPv4.IsWf.Oct2 source ↔
        Recovered.ipv4_is_wf_Oct2 (encodeString source) :=
  oct2_equiv

theorem ipv4_is_wf_Oct3 :
    ∀ source : String,
      IPv4.IsWf.Oct3 source ↔
        Recovered.ipv4_is_wf_Oct3 (encodeString source) :=
  oct3_equiv

theorem ipv4_is_wf_Oct4 :
    ∀ source : String,
      IPv4.IsWf.Oct4 source ↔
        Recovered.ipv4_is_wf_Oct4 (encodeString source) :=
  oct4_equiv

theorem ipv4_is_wf_Prefix :
    ∀ source : String,
      IPv4.IsWf.Prefix source ↔
        Recovered.ipv4_is_wf_Prefix (encodeString source) :=
  prefix_equiv

theorem ipv4_value :
    ∀ oct1 oct2 oct3 oct4 pre : String,
      IPv4.value oct1 oct2 oct3 oct4 pre =
        Recovered.ipv4_value (encodeString oct1) (encodeString oct2)
          (encodeString oct3) (encodeString oct4) (encodeString pre) :=
  ipv4_value_equiv

theorem ipv4_wf_constraints :
    ∀ oct1 oct2 oct3 oct4 pre : String,
      IPv4.WfConstraints oct1 oct2 oct3 oct4 pre ↔
        Recovered.ipv4_wf_constraints (encodeString oct1) (encodeString oct2)
          (encodeString oct3) (encodeString oct4) (encodeString pre) :=
  ipv4_wf_constraints_equiv

theorem ipv4_satisfies_wf_constraints :
    ∀ source : String,
      IPv4.IsWf.V4Net source →
        (IPv4.SatisfiesWfConstraints source ↔
          Recovered.ipv4_satisfies_wf_constraints (encodeString source)) :=
  ipv4_satisfies_wf_constraints_equiv

theorem ipv4_constraints :
    ∀ oct1 oct2 oct3 oct4 pre : String,
      IPv4.Constraints oct1 oct2 oct3 oct4 pre ↔
        Recovered.ipv4_constraints (encodeString oct1) (encodeString oct2)
          (encodeString oct3) (encodeString oct4) (encodeString pre) :=
  ipv4_constraints_equiv

theorem ipv4_satisfies_constraints :
    ∀ source : String,
      IPv4.IsWf.V4Net source →
        (IPv4.SatisfiesConstraints source ↔
          Recovered.ipv4_satisfies_constraints (encodeString source)) :=
  ipv4_satisfies_constraints_equiv

theorem ipv4_is_wf :
    ∀ source : String,
      IPv4.IsWf source ↔
        Recovered.ipv4_is_wf (encodeString source) :=
  ipv4_is_wf_equiv

theorem ipv4_is_valid :
    ∀ source : String,
      IPv4.IsValid source ↔
        Recovered.ipv4_is_valid (encodeString source) :=
  ipv4_is_valid_equiv

theorem view_denotation :
    ∀ input oct1 oct2 oct3 oct4 pre : String,
      Recovered.ipv4_view_denotation
          (Recovered.mkIPv4View (encodeString input) (encodeString oct1)
            (encodeString oct2) (encodeString oct3) (encodeString oct4)
            (encodeString pre)) =
        IPv4.value oct1 oct2 oct3 oct4 pre :=
  view_denotation_equiv

theorem view_valid :
    ∀ input oct1 oct2 oct3 oct4 pre : String,
      Recovered.ipv4_view_valid
          (Recovered.mkIPv4View (encodeString input) (encodeString oct1)
            (encodeString oct2) (encodeString oct3) (encodeString oct4)
            (encodeString pre)) ↔
        (IPv4.WfConstraints oct1 oct2 oct3 oct4 pre ∧
          IPv4.Constraints oct1 oct2 oct3 oct4 pre) :=
  view_valid_equiv

theorem matching_view_normalizes :
    ∀ input : String, ∀ view : Recovered.IPv4View,
      Recovered.ipv4_matches_view (encodeString input) view →
        ∃ oct1 oct2 oct3 oct4 pre : String,
          view =
            Recovered.mkIPv4View (encodeString input) (encodeString oct1)
              (encodeString oct2) (encodeString oct3) (encodeString oct4)
              (encodeString pre) :=
  matching_view_normalizes_equiv

theorem matches_view_exact :
    ∀ input oct1 oct2 oct3 oct4 pre : String,
      Recovered.ipv4_matches_view (encodeString input)
          (Recovered.mkIPv4View (encodeString input) (encodeString oct1)
            (encodeString oct2) (encodeString oct3) (encodeString oct4)
            (encodeString pre)) ↔
        (((((IPv4.IsWf.V4Net input ∧
                Triptych.component IPv4.grammar input "Oct1" = oct1) ∧
              Triptych.component IPv4.grammar input "Oct2" = oct2) ∧
            Triptych.component IPv4.grammar input "Oct3" = oct3) ∧
          Triptych.component IPv4.grammar input "Oct4" = oct4) ∧
        Triptych.component IPv4.grammar input "Prefix" = pre) :=
  matches_view_exact_equiv

theorem matching_view_exists :
    ∀ input : String,
      IPv4.IsWf.V4Net input ↔
        ∃ oct1 oct2 oct3 oct4 pre : String,
          Recovered.ipv4_matches_view (encodeString input)
            (Recovered.mkIPv4View (encodeString input) (encodeString oct1)
              (encodeString oct2) (encodeString oct3) (encodeString oct4)
              (encodeString pre)) :=
  matching_view_exists_equiv

theorem matches_result :
    ∀ input : String, ∀ result : Int,
      (IPv4.IsValid input ∧ IPv4.computeValue input = some result) ↔
        Recovered.ipv4_matches_result (encodeString input) result :=
  matches_result_equiv

end Triptych.Vermilion.Proofs.IPv4
