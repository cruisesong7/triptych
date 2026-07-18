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

/-!
# Decimal example: the grammar input

Transcribes `doc/CedarDoc/Decimal.lean` into one `format_spec` block, exercises the
generated spec end-to-end, and writes the two generated modules next to this file:
`engine.lean` (foundation + proofs) and `spec.lean` (the citable, proof-free interface).
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

-- A stand-in "external" parser + projection, to exercise the `parser` clause (the emitted
-- contract obligations are stated over the SURFACE `Decimal.IsValid`/`computeValue`).
-- In real use these name the hand-written Cedar parser and its `Int` projection; here it is
-- an opaque stub (the `format_spec` command needs it in scope, so it precedes generation).
structure DemoDec where val : Int
opaque demoParse (s : String) : Option DemoDec
def demoProj (d : DemoDec) : Int := d.val

format_spec Decimal where
  grammar
    Decimal  ::= Integer "." Fraction
    Integer  ::= ["-"] digit+
    Fraction ::= digit{1,4}
  value
    int Integer * 10 ^ 4 + sign Integer * nat Fraction * 10 ^ (4 - len Fraction)
  constraints
    value ∈ [Int64.MIN, Int64.MAX]
  parser demoParse projection demoProj
  -- Write the single generated module `spec.lean` (spec / engine / soundness / contracts
  -- sections) into this example's directory.
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

-- The emitted contract obligations, stated over the SURFACE spec (`sorry`d — the
-- proof-facing deliverable a later pass discharges by bridging `IsValid` to `decode`).
#check (Decimal.sound    : SoundStmt    Decimal.IsValid Decimal.computeValue demoParse demoProj)
#check (Decimal.complete : CompleteStmt Decimal.IsValid Decimal.computeValue demoParse demoProj)
#check (Decimal.reject   : RejectStmt   Decimal.IsValid demoParse)

end FormatSpec.Examples.Decimal
