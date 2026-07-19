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
-- `Decimal := Int64`), projected to its `Int` denotation via `Int64.toInt`. The emitted
-- `soundness.lean` states the `sorry`d obligations relating THIS parser to the surface spec.
def cedarProj (d : Cedar.Spec.Ext.Decimal) : Int := d.toInt

format_spec Decimal where
  grammar
    Decimal  ::= Integer "." Fraction
    Integer  ::= ["-"] digit+
    Fraction ::= digit{1,4}
  value
    int Integer * 10 ^ 4 + sign Integer * nat Fraction * 10 ^ (4 - len Fraction)
  constraints
    value ∈ [Int64.MIN, Int64.MAX]
  parser Cedar.Spec.Ext.Decimal.parse projection cedarProj
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
#check (Decimal.parse         : String → Option Int)
#check (Decimal.parse_sound   : SoundStmt    Decimal.isValid Decimal.computeValue Decimal.parse id)
#check (Decimal.parse_complete : CompleteStmt Decimal.isValid Decimal.computeValue Decimal.parse id)
#check (Decimal.parse_reject  : RejectStmt   Decimal.isValid Decimal.parse)
#eval Decimal.parse "1.5"     -- some 15000
#eval Decimal.parse "1.x"     -- none  (rejected)

-- The external-parser obligations (`soundness.lean`), stated over the SURFACE spec against the
-- REAL Cedar parser (`sorry`d — the ONLY proofs left to the human).
#check (Decimal.sound_ext    : SoundStmt    Decimal.IsValid Decimal.computeValue Cedar.Spec.Ext.Decimal.parse cedarProj)
#check (Decimal.complete_ext : CompleteStmt Decimal.IsValid Decimal.computeValue Cedar.Spec.Ext.Decimal.parse cedarProj)
#check (Decimal.reject_ext   : RejectStmt   Decimal.IsValid Cedar.Spec.Ext.Decimal.parse)

end FormatSpec.Examples.Decimal
