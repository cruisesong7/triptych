import TriptychVermilionGenerated.IPv6
import TriptychVermilionProofs.IPv6.Lemmas

namespace Triptych.Vermilion.Proofs.IPv6

open Triptych
open Triptych.Vermilion.String
open Triptych.Vermilion.Generated.IPv6
open IPv6.GrammarView

theorem ipv6_is_wf_V6Net :
    ∀ s0 : String, IPv6.IsWf.V6Net s0 ↔ Recovered.ipv6_is_wf_V6Net (encodeString s0) :=
  v6net_equiv

theorem ipv6_is_wf_V6Addr :
    ∀ s0 : String, IPv6.IsWf.V6Addr s0 ↔ Recovered.ipv6_is_wf_V6Addr (encodeString s0) :=
  v6addr_equiv

theorem ipv6_is_wf_Full :
    ∀ s0 : String, IPv6.IsWf.Full s0 ↔ Recovered.ipv6_is_wf_Full (encodeString s0) :=
  full_equiv

theorem ipv6_is_wf_Compressed :
    ∀ s0 : String, IPv6.IsWf.Compressed s0 ↔ Recovered.ipv6_is_wf_Compressed (encodeString s0) :=
  compressed_equiv

theorem ipv6_is_wf_Left :
    ∀ s0 : String, IPv6.IsWf.Left s0 ↔ Recovered.ipv6_is_wf_Left (encodeString s0) :=
  left_equiv

theorem ipv6_is_wf_Right :
    ∀ s0 : String, IPv6.IsWf.Right s0 ↔ Recovered.ipv6_is_wf_Right (encodeString s0) :=
  right_equiv

theorem ipv6_is_wf_H16 :
    ∀ s0 : String, IPv6.IsWf.H16 s0 ↔ Recovered.ipv6_is_wf_H16 (encodeString s0) :=
  h16_equiv

theorem ipv6_is_wf_H16L :
    ∀ s0 : String, IPv6.IsWf.H16L s0 ↔ Recovered.ipv6_is_wf_H16L (encodeString s0) :=
  h16L_equiv

theorem ipv6_is_wf_H16R :
    ∀ s0 : String, IPv6.IsWf.H16R s0 ↔ Recovered.ipv6_is_wf_H16R (encodeString s0) :=
  h16R_equiv

theorem ipv6_is_wf_Prefix :
    ∀ s0 : String, IPv6.IsWf.Prefix s0 ↔ Recovered.ipv6_is_wf_Prefix (encodeString s0) :=
  prefix_equiv

theorem ipv6_value :
    ∀ s0 s1 s2 s3 : String, IPv6.value s0 s1 s2 s3 = Recovered.ipv6_value (encodeString s0) (encodeString s1) (encodeString s2) (encodeString s3) :=
  ipv6_value_equiv

theorem ipv6_wf_constraints :
    ∀ s0 s1 s2 : String, IPv6.WfConstraints s0 s1 s2 ↔ Recovered.ipv6_wf_constraints (encodeString s0) (encodeString s1) (encodeString s2) :=
  ipv6_wf_constraints_equiv

theorem ipv6_satisfies_wf_constraints :
    ∀ s0 : String, IPv6.IsWf.V6Net s0 → (IPv6.SatisfiesWfConstraints s0 ↔ Recovered.ipv6_satisfies_wf_constraints (encodeString s0)) :=
  ipv6_satisfies_wf_constraints_equiv

theorem ipv6_constraints :
    ∀ s0 s1 s2 s3 : String, IPv6.Constraints s0 s1 s2 s3 ↔ Recovered.ipv6_constraints (encodeString s0) (encodeString s1) (encodeString s2) (encodeString s3) :=
  ipv6_constraints_equiv

theorem ipv6_satisfies_constraints :
    ∀ s0 : String, IPv6.IsWf.V6Net s0 → (IPv6.SatisfiesConstraints s0 ↔ Recovered.ipv6_satisfies_constraints (encodeString s0)) :=
  ipv6_satisfies_constraints_equiv

theorem ipv6_is_wf :
    ∀ s0 : String, IPv6.IsWf s0 ↔ Recovered.ipv6_is_wf (encodeString s0) :=
  ipv6_is_wf_equiv

theorem ipv6_is_valid :
    ∀ s0 : String, IPv6.IsValid s0 ↔ Recovered.ipv6_is_valid (encodeString s0) :=
  ipv6_is_valid_equiv

theorem view_denotation :
    ∀ input s0 s1 s2 s3 : String, Recovered.ipv6_view_denotation (Recovered.mkIPv6View (encodeString input) (encodeString s0) (encodeString s1) (encodeString s2) (encodeString s3)) = IPv6.value s0 s1 s2 s3 :=
  view_denotation_equiv

theorem view_valid :
    ∀ input s0 s1 s2 s3 : String, Recovered.ipv6_view_valid (Recovered.mkIPv6View (encodeString input) (encodeString s0) (encodeString s1) (encodeString s2) (encodeString s3)) ↔ (IPv6.WfConstraints s1 s2 s3 ∧ IPv6.Constraints s0 s1 s2 s3) :=
  view_valid_equiv

theorem matching_view_normalizes :
    ∀ input : String, ∀ view : Recovered.IPv6View,
      Recovered.ipv6_matches_view (encodeString input) view →
        ∃ full left right pre : String,
          view =
            Recovered.mkIPv6View (encodeString input) (encodeString full)
              (encodeString left) (encodeString right) (encodeString pre) :=
  matching_view_normalizes_equiv

theorem matches_view_exact :
    ∀ input full left right pre : String,
      Recovered.ipv6_matches_view (encodeString input)
          (Recovered.mkIPv6View (encodeString input) (encodeString full)
            (encodeString left) (encodeString right) (encodeString pre)) ↔
        ((((IPv6.IsWf.V6Net input ∧
                Triptych.component IPv6.grammar input "Full" = full) ∧
              Triptych.component IPv6.grammar input "Left" = left) ∧
            Triptych.component IPv6.grammar input "Right" = right) ∧
          Triptych.component IPv6.grammar input "Prefix" = pre) :=
  matches_view_exact_equiv

theorem matching_view_exists :
    ∀ input : String, IPv6.IsWf.V6Net input ↔ ∃ s0 s1 s2 s3 : String, Recovered.ipv6_matches_view (encodeString input) (Recovered.mkIPv6View (encodeString input) (encodeString s0) (encodeString s1) (encodeString s2) (encodeString s3)) :=
  matching_view_exists_equiv

theorem matches_result :
    ∀ input : String, ∀ result : Int,
      (IPv6.IsValid input ∧ IPv6.computeValue input = some result) ↔
        Recovered.ipv6_matches_result (encodeString input) result :=
  matches_result_equiv

end Triptych.Vermilion.Proofs.IPv6
