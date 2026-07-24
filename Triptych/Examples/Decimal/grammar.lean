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
# Decimal example — external `parser` + `printer` against Cedar's real `Decimal.parse`

Transcribes `doc/CedarDoc/Decimal.lean`. The `parser` clause names Cedar's own
`Decimal.parse` (`Decimal := Int64`) and the `printer` clause a single canonical serializer,
so the generated `soundness.lean` carries obligations for both the generated verified parser
and the external one. See the docs for the `lift`/`projection`/δ-view story.
-/

namespace Triptych.Examples.Decimal
open Triptych

-- Print the full value/constraint DSL vocabulary (and the `opaque` escape hatches):
#triptych_help

/-- Canonical serializer for the `printer` clause, over the domain type `Decimal` (= `Int64`);
    reuses Cedar's own `ToString Decimal`. -/
def decimalToStr (d : Cedar.Spec.Ext.Decimal) : String := toString d

triptych Decimal where
  grammar
    Decimal  ::= Sign Natural "." Fraction
    Sign     ::= sign
    Natural  ::= digit+
    Fraction ::= digit{1,4}
  value
    Sign * (nat Natural * 10 ^ 4 + nat Fraction * 10 ^ (4 - len Fraction))
    -- `lift`: upgrade the generated parser's spec value (`Int`, ×10⁴ fixed point) to the
    -- domain type `Decimal` (= `Int64`) via `Int64.ofInt`, a section of the projection below.
    lift Int64.ofInt
  constraints
    value ∈ [Int64.MIN, Int64.MAX]
  parser Cedar.Spec.Ext.Decimal.parse projection Int64.toInt
  printer decimalToStr
  to "Triptych/Examples/Decimal"

-- The generated verified parser (lifted to `Option Decimal` by `lift Int64.ofInt`), run on
-- sample strings:
#eval Decimal.parse "1.5"                    -- some 15000  (as a Decimal, via `lift Int64.ofInt`)
#eval Decimal.parse "1.x"                    -- none  (rejected)
#eval Decimal.parse "-0.15"                  -- some (-1500)  (the sign corner case)

end Triptych.Examples.Decimal
