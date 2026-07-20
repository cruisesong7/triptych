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

import FormatSpec.Syntax
import FormatSpec.Decode
import FormatSpec.Roundtrip
import Cedar.Spec.Ext.Decimal

/-!
# Decimal example: the grammar input

Transcribes `doc/CedarDoc/Decimal.lean` into one `format_spec` block, exercises the
generated spec end-to-end, and writes the generated modules next to this file:
`spec.lean` (the citable, proof-free surface), `parser.lean` (the engine + auto-discharged
proofs + the generated verified parser), and `soundness.lean` (the `sorry`d obligations for
the REAL Cedar parser `Cedar.Spec.Ext.Decimal.parse`, emitted because of the `parser` clause).
-/

namespace FormatSpec.Examples.Decimal
open FormatSpec

-- Not sure what the value / constraint DSL can express? Print the full vocabulary
-- (and the `opaque` escape hatches) before reaching for raw Lean:
#format_spec_help

-- ════════════════════════════════════════════════════════════════════════════
--  INPUT — the doc's Decimal grammar + constraint + value, transcribed
-- ════════════════════════════════════════════════════════════════════════════
--   Decimal  ::= Integer '.' Fraction
--   Integer  ::= ['-'] Digit⁺
--   Fraction ::= Digit{1,4}
--   value(Decimal) = int(Integer)·10⁴ + sign·nat(Fraction)·10^(4 − |Fraction|)
--   Constraint: value ∈ [Int64.MIN, Int64.MAX]   (Int64 range; -2^63 .. 2^63-1)

-- The REAL external parser: Cedar's own `Decimal.parse : String → Option Decimal` (where
-- `Decimal := Int64`), projected to its `Int` denotation by `Int64.toInt`. The emitted
-- `soundness.lean` states the `sorry`d obligations relating THIS parser to the surface spec.

-- ONE canonical serializer for the `printer` clause, over the SPEC value type (fixed-point ×10⁴
-- `Int`). Both the generated parser and Cedar's parser project to this `Int` (Cedar via
-- `Int64.toInt`), so a single serializer drives the printer theorems for BOTH, stated in
-- β-view. Renders the ×10⁴ integer as a 4-decimal string (Cedar's format shape).
def intToDecimalString (i : Int) : String :=
  let neg   := if i < 0 then "-" else ""
  let n     := i.natAbs
  let left  := n / 10000
  let right := n % 10000
  let frac  :=
    if right < 10 then s!".000{right}"
    else if right < 100 then s!".00{right}"
    else if right < 1000 then s!".0{right}"
    else s!".{right}"
  s!"{neg}{left}{frac}"

format_spec Decimal where
  grammar
    Decimal  ::= Integer "." Fraction
    Integer  ::= ["-"] digit+
    Fraction ::= digit{1,4}
  value
    int Integer * 10 ^ 4 + sign Integer * nat Fraction * 10 ^ (4 - len Fraction)
  constraints
    value ∈ [Int64.MIN, Int64.MAX]
  parser Cedar.Spec.Ext.Decimal.parse projection Int64.toInt
  printer intToDecimalString
  -- Write the generated modules `spec.lean` / `parser.lean` / `soundness.lean` into this dir.
  to "FormatSpec/Examples/Decimal"

-- ════════════════════════════════════════════════════════════════════════════
--  OUTPUT — the generated declarations, run on sample strings
-- ════════════════════════════════════════════════════════════════════════════

#eval decode Decimal.grammar "1.5"          -- some [("Integer","1"),("Fraction","5")]
#eval Decimal.parse "1.5"                    -- some 15000
#eval Decimal.parse "1.x"                    -- none  (rejected)
#eval Decimal.parse "-0.15"                  -- some (-1500)  (the sign corner case)

-- Reconciliation (standard axioms only):
#check (Decimal.IsWf_equiv : ∀ s, IsWf Decimal.grammar s ↔ Decimal.IsWf.Decimal s)
example : DecidablePred Decimal.IsValid := inferInstance

-- The GENERATED verified parser + its printer theorems (spec value type Int, `intToDecimalString`):
#check @Decimal.parse_sound       -- ∀ s i, parse s = some i → isValid s ∧ computeValue s = some i
#check @Decimal.parse_toString_roundtrip   -- ∀ i, parse (intToDecimalString i) = some i
#check @Decimal.toString_injective
#check @Decimal.normalize_eq_iff_parse_eq

-- The EXTERNAL parser (Cedar's real parse) obligations + printer theorems, β-view via the same
-- `intToDecimalString` and the projection `Int64.toInt`:
#check @Decimal.extparse_sound
#check @Decimal.extparse_complete
#check @Decimal.extparse_reject
#check @Decimal.extparse_toString_roundtrip -- ∀ i, (Cedar…parse (intToDecimalString i)).map Int64.toInt = some i
#check @Decimal.extparse_toString_injective
#check @Decimal.extparse_normalize_eq_iff_parse_eq

end FormatSpec.Examples.Decimal
