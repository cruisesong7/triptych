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
import Triptych.Theorems.Coherence
import Cedar.Spec.Ext.Decimal

/-!
# Decimal example — external `parser` + `printer` against Cedar's real `Decimal.parse`

Transcribes `doc/CedarDoc/Decimal.lean`. The `parser` clause names Cedar's own
`Decimal.parse` (`Decimal := Int64`) and the `printer` clause a single canonical serializer,
so the generated `soundness.lean` carries obligations for both the generated verified parser
and the external one. See the docs for the `ofSpec`/`toSpec` conversion story.
-/

namespace CedarExamples.Decimal
open Triptych

-- Print the full value/constraint DSL vocabulary (and the `opaque` escape hatches):
#triptych_help

/-- Canonical serializer for the `printer` clause, over the domain type `Decimal` (= `Int64`);
    reuses Cedar's own `ToString Decimal`. -/
def decimalToStr (d : Cedar.Spec.Ext.Decimal) : String := toString d

-- ANCHOR: decimalTriptychSource
triptych Decimal where
  grammar
    Decimal  ::= Sign Natural "." Fraction
    Sign     ::= sign
    Natural  ::= digit+
    Fraction ::= digit{1,4}
  value
    Sign * (nat Natural * 10 ^ 4 + nat Fraction * 10 ^ (4 - len Fraction))
    ofSpec Int64.ofInt
    toSpec Int64.toInt
  constraints
    value ∈ [Int64.MIN, Int64.MAX]
  parser Cedar.Spec.Ext.Decimal.parse
  printer decimalToStr
  to "Outputs/Decimal"
-- ANCHOR_END: decimalTriptychSource

-- The generated verified parser (returning `Option Decimal` via `ofSpec Int64.ofInt`), run on
-- sample strings:
#eval Decimal.parse "1.5"                    -- some 15000  (as a Decimal)
#eval Decimal.parse "1.x"                    -- none  (rejected)
#eval Decimal.parse "-0.15"                  -- some (-1500)  (the sign corner case)

-- The optional sign and digit-run/decimal-point boundary are statically unique for all inputs.
#guard Decimal.grammar.staticUnique = true

example : GrammarDecodeUnique Decimal.grammar :=
  Decimal.grammarDecodeUnique

example : GrammarCaptureFunctional Decimal.grammar :=
  Decimal.grammarCaptureFunctional

example :
    GrammarValueCoherent Decimal.grammar
      (fun m : CaptureMap => Decimal.valueFn m.toEnv) :=
  Decimal.grammarValueCoherent

-- Per-string diagnostics remain executable witnesses for representative inputs.
#eval (Triptych.fullParses Decimal.grammar "-12.34").length    -- 1  (unique here)
#eval decide (Triptych.DecodeUnique Decimal.grammar "-12.34") -- true

end CedarExamples.Decimal
