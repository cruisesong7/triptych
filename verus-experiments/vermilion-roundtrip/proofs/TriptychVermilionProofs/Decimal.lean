import TriptychVermilionGenerated.Decimal
import TriptychVermilionProofs.Decimal.Lemmas

namespace Triptych.Vermilion.Proofs.Decimal

open Triptych
open Triptych.Vermilion.String
open Triptych.Vermilion.Generated.Decimal

theorem decimal_is_wf_Decimal :
    ∀ source : String,
      Decimal.IsWf.Decimal source ↔
        Recovered.decimal_is_wf_Decimal (encodeString source) :=
  decimal_equiv

theorem decimal_is_wf_Sign :
    ∀ source : String,
      Decimal.IsWf.Sign source ↔
        Recovered.decimal_is_wf_Sign (encodeString source) :=
  sign_equiv

theorem decimal_is_wf_Natural :
    ∀ source : String,
      Decimal.IsWf.Natural source ↔
        Recovered.decimal_is_wf_Natural (encodeString source) :=
  natural_equiv

theorem decimal_is_wf_Fraction :
    ∀ source : String,
      Decimal.IsWf.Fraction source ↔
        Recovered.decimal_is_wf_Fraction (encodeString source) :=
  fraction_equiv

theorem decimal_value :
    ∀ signPart natural fraction : String,
      Decimal.value signPart natural fraction =
        Recovered.decimal_value (encodeString signPart)
          (encodeString natural) (encodeString fraction) :=
  decimal_value_equiv

theorem decimal_constraints :
    ∀ signPart natural fraction : String,
      Decimal.Constraints signPart natural fraction ↔
        Recovered.decimal_constraints (encodeString signPart)
          (encodeString natural) (encodeString fraction) :=
  decimal_constraints_equiv

theorem decimal_satisfies_constraints :
    ∀ source : String,
      Decimal.IsWf.Decimal source →
        (Decimal.SatisfiesConstraints source ↔
          Recovered.decimal_satisfies_constraints (encodeString source)) :=
  satisfies_constraints_equiv

theorem decimal_is_wf :
    ∀ source : String,
      Decimal.IsWf source ↔
        Recovered.decimal_is_wf (encodeString source) :=
  decimal_equiv

theorem decimal_is_valid :
    ∀ source : String,
      Decimal.IsValid source ↔
        Recovered.decimal_is_valid (encodeString source) :=
  is_valid_equiv

theorem view_denotation :
    ∀ input signPart natural fraction : String,
      Recovered.decimal_view_denotation
          (Recovered.mkDecimalView (encodeString input)
            (encodeString signPart) (encodeString natural)
            (encodeString fraction)) =
        Decimal.value signPart natural fraction :=
  view_denotation_equiv

theorem view_valid :
    ∀ input signPart natural fraction : String,
      Recovered.decimal_view_valid
          (Recovered.mkDecimalView (encodeString input)
            (encodeString signPart) (encodeString natural)
            (encodeString fraction)) ↔
        Decimal.Constraints signPart natural fraction :=
  view_valid_equiv

theorem matching_view_normalizes :
    ∀ input : String, ∀ view : Recovered.DecimalView,
      Recovered.decimal_matches_view (encodeString input) view →
        ∃ signPart natural fraction : String,
          view =
            Recovered.mkDecimalView (encodeString input)
              (encodeString signPart) (encodeString natural)
              (encodeString fraction) :=
  matching_view_normalizes_equiv

theorem matches_view_exact :
    ∀ input signPart natural fraction : String,
      Recovered.decimal_matches_view (encodeString input)
          (Recovered.mkDecimalView (encodeString input)
            (encodeString signPart) (encodeString natural)
            (encodeString fraction)) ↔
        (((Decimal.IsWf.Decimal input ∧
              Triptych.component Decimal.grammar input "Sign" = signPart) ∧
            Triptych.component Decimal.grammar input "Natural" = natural) ∧
          Triptych.component Decimal.grammar input "Fraction" = fraction) :=
  matches_view_exact_equiv

theorem matching_view_exists :
    ∀ input : String,
      Decimal.IsWf.Decimal input ↔
        ∃ signPart natural fraction : String,
          Recovered.decimal_matches_view (encodeString input)
            (Recovered.mkDecimalView (encodeString input)
              (encodeString signPart) (encodeString natural)
              (encodeString fraction)) :=
  matching_view_exists_equiv

theorem matches_result :
    ∀ input : String, ∀ result : Int,
      (Decimal.IsValid input ∧
          Decimal.computeValue input = some result) ↔
        Recovered.decimal_matches_result (encodeString input) result :=
  matches_result_equiv

end Triptych.Vermilion.Proofs.Decimal
