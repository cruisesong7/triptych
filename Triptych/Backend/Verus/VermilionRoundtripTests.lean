/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Triptych.Backend.Verus.VermilionRoundtrip

namespace Triptych.Backend.Verus.VermilionRoundtrip.Tests

private def decimalGrammar : Grammar :=
  { start := "Decimal"
    prods :=
      [ { name := "Decimal"
          alts :=
            [[SymItem.mk (.ref "Sign") false, SymItem.mk (.ref "Natural") false,
              SymItem.mk (.lit ".") false, SymItem.mk (.ref "Fraction") false]] },
        { name := "Sign", alts := [[SymItem.mk (.lit "-") true]] },
        { name := "Natural", alts := [[SymItem.mk (.term .digit .atLeastOne) false]] },
        { name := "Fraction", alts := [[SymItem.mk (.term .digit (.between 1 4)) false]] } ] }

private def decimalValue : ValExpr :=
  .mul (.signOf "Sign")
    (.add
      (.mul (.nat "Natural") (.pow (.lit 10) (.lit 4)))
      (.mul (.nat "Fraction") (.pow (.lit 10) (.sub (.lit 4) (.len "Fraction")))))

private def decimalConstraints : List Constraint :=
  [.and
    (.le (.lit (-9223372036854775808)) decimalValue)
    (.le decimalValue (.lit 9223372036854775807))]

private def decimalFormat : FormatInput :=
  .mk "Decimal" decimalGrammar decimalValue [] decimalConstraints
    "Int64.ofInt" "Int64.toInt" true

private def caseSensitiveGrammar : Grammar :=
  { start := "CaseSensitive"
    prods :=
      [ { name := "CaseSensitive"
          alts :=
            [[SymItem.mk (.ref "MM") false, SymItem.mk (.ref "mm") false]] },
        { name := "MM"
          alts := [[SymItem.mk (.term .digit (.exactly 2)) false]] },
        { name := "mm"
          alts := [[SymItem.mk (.term .digit (.exactly 2)) false]] } ] }

private def caseSensitiveFormat : FormatInput :=
  .mk "CaseSensitive" caseSensitiveGrammar
    (.add (.nat "MM") (.nat "mm")) [] [] "id" "id" false

private def qualifiedCaptureGrammar : Grammar :=
  { start := "Qualified"
    prods :=
      [ { name := "Qualified"
          alts :=
            [[SymItem.mk (.ref "Time") false,
              SymItem.mk (.ref "Offset") false]] },
        { name := "Time"
          alts :=
            [[SymItem.mk (.ref "hh") false,
              SymItem.mk (.lit ":") false,
              SymItem.mk (.ref "mm") false]] },
        { name := "Offset"
          alts :=
            [[SymItem.mk (.ref "hh") false,
              SymItem.mk (.lit ":") false,
              SymItem.mk (.ref "mm") false]] },
        { name := "hh"
          alts := [[SymItem.mk (.term .digit (.exactly 2)) false]] },
        { name := "mm"
          alts := [[SymItem.mk (.term .digit (.exactly 2)) false]] } ] }

private def qualifiedCaptureFormat : FormatInput :=
  .mk "Qualified" qualifiedCaptureGrammar
    (.add
      (.add (.nat "Time.hh") (.nat "Time.mm"))
      (.add (.nat "Offset.hh") (.nat "Offset.mm")))
    [] [] "id" "id" false

private def contains (source needle : String) : Bool :=
  (source.splitOn needle).length > 1

#guard crateStem "Decimal" == "triptych_decimal_roundtrip"

#guard
  match emitAnchor decimalFormat with
  | .error _ => false
  | .ok source =>
      contains source "pub proof fn triptych_vermilion_anchor()" &&
        contains source "ensures true," &&
        contains source "reveal(decimal_is_valid);" &&
        contains source "reveal(decimal_view_denotation);"

#guard
  match emitContract decimalFormat "Outputs.Decimal.parser" with
  | .error _ => false
  | .ok source =>
      contains source "import Outputs.Decimal.parser" &&
        contains source "import TriptychVermilionRecovered.Decimal" &&
        contains source "import TriptychVermilionProofs.Utils" &&
        contains source "noncomputable section" &&
        !contains source "abbrev encodeString :=" &&
        contains source "namespace Recovered" &&
        contains source
          "abbrev decimal_is_wf_Sign := \
            triptych_decimal_roundtrip.decimal_is_wf_Sign" &&
        contains source
          "abbrev DecimalView := triptych_decimal_roundtrip.DecimalView" &&
        contains source
          "abbrev mkDecimalView := \
            triptych_decimal_roundtrip.DecimalView.DecimalView" &&
        !contains source "namespace Obligations" &&
        !contains source "def decimal_is_wf_Decimal : Prop :=" &&
        contains source "abbrev decimal_value :=" &&
        contains source "abbrev decimal_constraints :=" &&
        contains source "abbrev decimal_is_valid :=" &&
        contains source "abbrev decimal_view_denotation :=" &&
        contains source "abbrev decimal_view_valid :=" &&
        contains source "abbrev decimal_matches_view :=" &&
        contains source "abbrev decimal_matches_result :="

#guard
  match emitProofScaffold decimalFormat with
  | .error _ => false
  | .ok source =>
      contains source "open Triptych.Vermilion.String" &&
        contains source "open Triptych.Vermilion.Generated.Decimal" &&
        contains source "theorem decimal_is_wf_Decimal :" &&
        contains source
          "∀ s0 : String, Decimal.IsWf.Decimal s0 ↔ \
            Recovered.decimal_is_wf_Decimal" &&
        contains source "theorem decimal_value :" &&
        contains source "theorem decimal_constraints :" &&
        contains source
          "Decimal.IsWf.Decimal s0 → (Decimal.SatisfiesConstraints s0 ↔" &&
        contains source "theorem decimal_is_valid :" &&
        contains source
          "Recovered.mkDecimalView" &&
        contains source "Recovered.decimal_is_wf_Sign" &&
        contains source "Recovered.decimal_value" &&
        contains source "theorem view_denotation :" &&
        contains source "theorem view_valid :" &&
        contains source "theorem matching_view_normalizes :" &&
        contains source
          "∀ view : Recovered.DecimalView, \
            Recovered.decimal_matches_view (encodeString input) view → ∃" &&
        contains source
          "view = (Recovered.mkDecimalView (encodeString input)" &&
        contains source "theorem matches_view_exact :" &&
        contains source
          "Triptych.component Decimal.grammar input \"Sign\" = s0" &&
        contains source "theorem matching_view_exists :" &&
        contains source "Decimal.IsWf.Decimal input ↔ ∃" &&
        contains source "theorem matches_result :" &&
        contains source
          "(Decimal.IsValid input ∧ Decimal.computeValue input = some result) ↔" &&
        contains source "Recovered.decimal_matches_result (encodeString input) result" &&
        !contains source "Decimal.IsWf input ↔ ∃" &&
        !contains source ".Obligations."

#guard
  match emitCheckModule decimalFormat with
  | .error _ => false
  | .ok source =>
      contains source "import TriptychVermilionProofs.Decimal" &&
        contains source "open Triptych.Vermilion.String" &&
        contains source "open Triptych.Vermilion.Generated.Decimal" &&
        contains source
          "example : Triptych.Vermilion.String.encodeString =\n    fun source => \
            source.toList.map (fun character => Int.ofNat character.toNat) := rfl" &&
        contains source
          "example : ∀ s0 : String, Decimal.IsWf.Decimal s0 ↔ \
            Recovered.decimal_is_wf_Decimal" &&
        contains source
          ":= Triptych.Vermilion.Proofs.Decimal.decimal_is_wf_Decimal" &&
        contains source
          "#print axioms Triptych.Vermilion.Proofs.Decimal.matching_view_normalizes" &&
        contains source
          "#print axioms Triptych.Vermilion.Proofs.Decimal.matches_view_exact" &&
        contains source
          "#print axioms Triptych.Vermilion.Proofs.Decimal.matches_result" &&
        !contains source ".Obligations."

#guard
  (emitContract decimalFormat "Outputs.Decimal.parser").toOption ==
    (emitContract decimalFormat "Outputs.Decimal.parser").toOption

#guard
  match emitProofScaffold caseSensitiveFormat with
  | .error _ => false
  | .ok source =>
      contains source "theorem case_sensitive_is_wf_MM :" &&
        contains source "theorem case_sensitive_is_wf_mm :"

#guard
  match emitProofScaffold qualifiedCaptureFormat with
  | .error _ => false
  | .ok source =>
      contains source "theorem matches_view_exact :" &&
        contains source
          "Triptych.component Qualified.grammar input \"Time.hh\" =" &&
        contains source
          "Triptych.component Qualified.grammar input \"Time.mm\" =" &&
        contains source
          "Triptych.component Qualified.grammar input \"Offset.hh\" =" &&
        contains source
          "Triptych.component Qualified.grammar input \"Offset.mm\" =" &&
        contains source "theorem matches_result :"

end Triptych.Backend.Verus.VermilionRoundtrip.Tests
