import Outputs.Decimal.parser

/-! Executable smoke test for generated optional and terminal derivations. -/

open Triptych

namespace CedarExamples.Decimal

def decimalDerivation : Decimal.Derivation.Decimal :=
  .alt0 (.alt0 (some ())) (.alt0 "12") (.alt0 "34")

#guard Decimal.Derivation.Decimal.render decimalDerivation = "-12.34"

example : Decimal.Derivation.Decimal.Valid decimalDerivation := by
  decide

example :
    decode Decimal.grammar (Decimal.Derivation.Decimal.render decimalDerivation) =
      some (Decimal.Derivation.Decimal.capturesWith "" decimalDerivation) :=
  Decimal.Derivation.Decimal.decode_render decimalDerivation (by decide)

example :
    Decimal.decodeView (Decimal.Derivation.Decimal.render decimalDerivation) =
      some (Decimal.Derivation.Decimal.toView decimalDerivation) :=
  Decimal.Derivation.Decimal.decodeView_render decimalDerivation (by decide)

end CedarExamples.Decimal
