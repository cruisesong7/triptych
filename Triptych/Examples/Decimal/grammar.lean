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

import Triptych.Architecture.Syntax
import Triptych.Architecture.Decode
import Triptych.Theorems.Roundtrip
import Cedar.Spec.Ext.Decimal

/-!
# Decimal example: the grammar input

Transcribes `doc/CedarDoc/Decimal.lean` into one `format_spec` block, exercises the
generated spec end-to-end, and writes the generated modules next to this file:
`spec.lean` (the citable, proof-free surface), `parser.lean` (the engine + auto-discharged
proofs + the generated verified parser), and `soundness.lean` (the `sorry`d obligations,
emitted because of the `parser` + `printer` clauses: the generated-parser section — encode
obligations, `lift_section`, `lift_faithful` — and the external section for the REAL Cedar
parser `Cedar.Spec.Ext.Decimal.parse` — the `extparse_*` trio).
-/

namespace Triptych.Examples.Decimal
open Triptych

/- Not sure what the value / constraint DSL can express? Print the full vocabulary
(and the `opaque` escape hatches) before reaching for raw Lean: -/
#format_spec_help

/- The `parser` clause below names the REAL external parser — Cedar's own
`Decimal.parse : String → Option Decimal` (where `Decimal := Int64`) — with projection
`Int64.toInt` reading its value's `Int` denotation. The emitted `soundness.lean` states the
`sorry`d obligations relating that parser to the surface spec. -/

/-- The ONE canonical serializer for the `printer` clause, over the DOMAIN type `Decimal`
    (= `Int64`). Two parsers are in play — the generated `Decimal.parse` (returning
    `Option Decimal` via the `lift Int64.ofInt` below) and Cedar's real parse (returning
    `Option Decimal` natively) — and since they agree on the return type, this single
    serializer drives the printer theorems for each: `parse_toString_*` (generated) and
    `extparse_toString_*` (external), in the clean δ-VIEW `parse (toStr d) = some d`.
    Rather than hand-roll the formatting, reuse Cedar's own `ToString Decimal` — so the
    string form is Cedar's canonical decimal notation by definition. -/
def decimalToStr (d : Cedar.Spec.Ext.Decimal) : String := toString d

format_spec Decimal where
  grammar
    Decimal  ::= Sign Integer "." Fraction
    Sign     ::= sign
    Integer  ::= digit+
    Fraction ::= digit{1,4}
  value
    Sign * (nat Integer * 10 ^ 4 + nat Fraction * 10 ^ (4 - len Fraction))
    -- `lift` (sub-clause of `value`): upgrade the GENERATED parser's output from the spec value
    -- `Int` (×10⁴ fixed point) to the domain type `Decimal` (= `Int64`) via `Int64.ofInt`, a
    -- section of the projection below (`Int64.ofInt_toInt`). So `Decimal.parse : String → Option
    -- Decimal`, type-identical to Cedar's.
    lift Int64.ofInt
  constraints
    value ∈ [Int64.MIN, Int64.MAX]
  parser Cedar.Spec.Ext.Decimal.parse projection Int64.toInt
  printer decimalToStr
  -- Write the generated modules `spec.lean` / `parser.lean` / `soundness.lean` into this dir.
  to "Triptych/Examples/Decimal"

-- The generated declarations, run on sample strings:

#eval decode Decimal.grammar "1.5"          -- some [("Sign",""),("Integer","1"),("Fraction","5")]
#eval Decimal.computeValue "1.5"             -- some 15000  (the spec value: ×10⁴ fixed point)
#eval Decimal.parse "1.5"                    -- some 15000  (as a Decimal, via `lift Int64.ofInt`)
#eval Decimal.parse "1.x"                    -- none  (rejected)
#eval Decimal.parse "-0.15"                  -- some (-1500)  (the sign corner case)

-- Reconciliation (standard axioms only):
#check (Decimal.IsWf_equiv : ∀ s, IsWf Decimal.grammar s ↔ Decimal.IsWf.Decimal s)
example : DecidablePred Decimal.IsValid := inferInstance

/- The GENERATED verified parser (LIFTED to `Option Decimal` by `lift Int64.ofInt`) + its printer
theorems, δ-view via the single domain serializer `decimalToStr`. `parse_sound_proj` is the
π-view soundness (`parse s = some d → isValid s ∧ computeValue s = some (Int64.toInt d)`),
discharged from the `lift_faithful` obligation (π∘σ = id on accepted values — what the
`value ∈ [Int64.MIN, Int64.MAX]` constraint exists to guarantee; without that constraint
`Int64.ofInt` would wrap out-of-range inputs and the obligation is unprovable). -/
#check (Decimal.parse : String → Option Cedar.Spec.Ext.Decimal)
#check @Decimal.parse_sound       -- ∀ s d, parse s = some d → isValid s ∧ (computeValue s).map Int64.ofInt = some d
#check @Decimal.parse_sound_proj
#check @Decimal.parse_toString_roundtrip   -- ∀ d, parse (decimalToStr d) = some d
#check @Decimal.toString_injective
#check @Decimal.normalize_eq_iff_parse_eq

-- The EXTERNAL parser (Cedar's real parse) obligations + printer theorems, same serializer:
#check @Decimal.extparse_sound
#check @Decimal.extparse_complete
#check @Decimal.extparse_reject
#check @Decimal.extparse_toString_roundtrip -- ∀ d, Cedar…Decimal.parse (decimalToStr d) = some d
#check @Decimal.extparse_toString_injective
#check @Decimal.extparse_normalize_eq_iff_parse_eq

end Triptych.Examples.Decimal
