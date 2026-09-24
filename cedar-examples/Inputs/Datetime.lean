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
import Cedar.Spec.Ext.Datetime

/-!
# Datetime example — the hard case: 5-way alternation + calendar arithmetic

Transcribes the parser-independent specification in `Cedar.Thm.Ext.Datetime.Grammar` — the
generality stress test, exercising top-level alternation, qualified captures (`Time.hh` vs
`Offset.hh`), conditional calendar bounds, truncating division, and modulo. The calendar
combinators expand into Triptych's inspectable `ValExpr`; no opaque `value'` or `constraints'`
escape remains. Cedar's canonical `toString?` is partial because not every `Int64` datetime has a
four-digit year, while Triptych's current `printer` clause requires a total serializer.
-/

namespace CedarExamples.Datetime
open Triptych

/-- The value/domain `toSpec` conversion: Cedar's `Datetime` stores epoch millis in
    `val : Int64`, matching the DSL's epoch-millisecond value. -/
def datetimeMillis (d : Cedar.Spec.Ext.Datetime) : Int := d.val.toInt

/-- Convert epoch milliseconds to Cedar's Datetime domain type. The generated
    `toSpec_ofSpec` obligation proves that accepted grammar values are inside Int64's faithful
    range, so this conversion cannot wrap for valid input. -/
def millisToDatetime (i : Int) : Cedar.Spec.Ext.Datetime :=
  ⟨Int64.ofInt i⟩

theorem millisToDatetime_datetimeMillis (d : Cedar.Spec.Ext.Datetime) :
    millisToDatetime (datetimeMillis d) = d := by
  cases d
  simp [millisToDatetime, datetimeMillis, Int64.ofInt_toInt]

triptych Datetime where
  grammar
    Datetime ::= Date
               | Date "T" Time "Z"
               | Date "T" Time "." SSS "Z"
               | Date "T" Time Offset
               | Date "T" Time "." SSS Offset
    Date     ::= YYYY "-" MM "-" DD
    Time     ::= hh ":" mm ":" ss
    Offset   ::= "+" hh mm
               | "-" hh mm
    SSS      ::= digit{3}
    YYYY     ::= digit{4}
    MM       ::= digit{2}
    DD       ::= digit{2}
    hh       ::= digit{2}
    mm       ::= digit{2}
    ss       ::= digit{2}
  value
    (daysFromCivil(nat YYYY, nat MM, nat DD) * 86400
      + nat Time.hh * 3600 + nat Time.mm * 60 + nat ss) * 1000 + nat SSS
      - prefixSign Offset * (nat Offset.hh * 3600000 + nat Offset.mm * 60000)
    ofSpec millisToDatetime
    toSpec datetimeMillis
  constraints
    -- Numeric field bounds. `hh`/`mm` are reused in `Time` and `Offset`, so they are addressed
    -- by qualified capture names (`Time.hh` vs `Offset.hh`).
    nat MM ∈ [1, 12]
    nat Time.hh ∈ [0, 23]
    nat Time.mm ∈ [0, 59]
    nat ss ∈ [0, 59]
    nat Offset.hh ∈ [0, 23]
    nat Offset.mm ∈ [0, 59]
    nat DD ∈ [1, daysInMonth(nat YYYY, nat MM)]
    value ∈ [Int64.MIN, Int64.MAX]
  parser Cedar.Spec.Ext.Datetime.parse
  verus "../verus-experiments/cedar-ext/datetime/src/spec.rs"
  to "Outputs/Datetime"

-- The generated parser returns Cedar's Datetime type. Map to epoch milliseconds for readable
-- sample output:
#eval (Datetime.parse "1970-01-01T00:00:00Z").map datetimeMillis
#eval (Datetime.parse "2024-01-15T10:30:45.123Z").map datetimeMillis
#eval (Datetime.parse "2024-01-15T10:30:45+0530").map datetimeMillis
#eval (Datetime.parse "2024-02-30T00:00:00Z").map datetimeMillis

end CedarExamples.Datetime
