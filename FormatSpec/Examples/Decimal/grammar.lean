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

-- The canonical value serializer for the `printer` clause. The generated value type is `Int`
-- (fixed-point ×10⁴), so its DEFAULT `ToString` (`"15000"`) is NOT the decimal format — the
-- canonical form must be supplied. This mirrors Cedar's `ToString Decimal` (4-digit fraction,
-- zero-padded) but on the `Int` value. The `printer` clause emits the two encode obligations
-- (that this round-trips) as `sorry`s, and auto-derives roundtrip/injective/normalize.
def decimalToString (i : Int) : String :=
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
  printer decimalToString
  -- Write the generated modules `spec.lean` / `parser.lean` / `soundness.lean` into this dir.
  to "FormatSpec/Examples/Decimal"

-- ════════════════════════════════════════════════════════════════════════════
--  OUTPUT — the generated spec, run on sample strings
-- ════════════════════════════════════════════════════════════════════════════

-- The generated declarations — the readable surface + the engine bundle:
#check (Decimal.grammar     : Grammar)
#check (Decimal.IsWf.Decimal         : String → Prop)
#check (Decimal.SatisfiesConstraints : String → Prop)
#check (Decimal.IsValid           : String → Prop)
#check (Decimal.isValid           : String → Prop)   -- engine bundle

-- `decode` extracts the captures:  "1.5" ↦ Integer="1", Fraction="5"
#eval decode Decimal.grammar "1.5"       -- some [("Integer","1"), ("Fraction","5")]
#eval decode Decimal.grammar "-12.34"    -- some [("Integer","-12"), ("Fraction","34")]

-- `computeValue` = eval the value formula on the decoded captures (fixed-point ×10⁴):
#eval computeValue Decimal.grammar Decimal.valueExpr "1.2345"   -- some 12345
#eval computeValue Decimal.grammar Decimal.valueExpr "-1.5"     -- some (-15000)

-- The RECONCILIATION: the readable surface `IsWf.Decimal` is proven equal to the engine
-- interpreter `IsWf grammar`, and via that equivalence is DECIDABLE (standard axioms only).
#check (Decimal.IsWf_equiv : ∀ s, IsWf Decimal.grammar s ↔ Decimal.IsWf.Decimal s)
example : DecidablePred Decimal.IsWf.Decimal := inferInstance
#eval decide (Decimal.IsWf.Decimal "1.5")   -- true
#eval decide (Decimal.IsWf.Decimal "1.x")   -- false

-- The GENERATED verified parser (`parser.lean`): `parse` gated on the decidable engine
-- `isValid`, with its three contracts AUTO-DISCHARGED (no `sorry`, standard axioms only).
#check (Decimal.parse : String → Option Int)
#check @Decimal.parse_sound      -- ∀ s i, parse s = some i → isValid s ∧ computeValue s = some i
#check @Decimal.parse_complete   -- ∀ s i, isValid s → computeValue s = some i → parse s = some i
#check @Decimal.parse_reject     -- ∀ s, parse s = none ↔ ¬ isValid s
#eval Decimal.parse "1.5"     -- some 15000
#eval Decimal.parse "1.x"     -- none  (rejected)

-- The external-parser obligations (`soundness.lean`), stated over the SURFACE spec against the
-- REAL Cedar parser (`sorry`d — the ONLY proofs left to the human).
#check @Decimal.extparse_sound
#check @Decimal.extparse_complete
#check @Decimal.extparse_reject

-- The PRINTER theorems (`soundness.lean`, from the `printer decimalToString` clause). The two
-- encode obligations (`encode_accepted`/`encode_value`) are `sorry`d; the three printer results
-- Cedar proves are AUTO-DERIVED from them (fully proven once the obligations are discharged).
#check @Decimal.encode_accepted           -- ∀ i, isValid (decimalToString i)          [sorry]
#check @Decimal.encode_value              -- ∀ i, computeValue (decimalToString i) = some i [sorry]
#check @Decimal.parse_toString_roundtrip  -- ∀ i, parse (decimalToString i) = some i
#check @Decimal.toString_injective        -- ∀ i i', decimalToString i = decimalToString i' → i = i'
#check @Decimal.normalize_eq_iff_parse_eq

end FormatSpec.Examples.Decimal
