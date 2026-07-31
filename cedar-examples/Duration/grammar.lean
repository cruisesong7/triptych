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
import Cedar.Spec.Ext.Datetime

/-!
# Duration example — five optional unit components (peel/all-optional stress test)

Transcribes `doc/CedarDoc/Duration.lean`. Exercises the all-optional `Components`
reconciliation (the O(2⁵) present/absent tree ⟺ flat form) and the sub-capture pattern (each
unit's digit run is its own nonterminal `DDays ::= digit+`, so `value` reads `nat DDays`).
Names Cedar's own `Duration.parse` in the `parser` clause; see the docs for the
`ofSpec`/`toSpec` conversion story.
-/

namespace CedarExamples.Duration
open Triptych

/-- Conversions for the millisecond `Int` value, plus the canonical serializer
    (reusing Cedar's `ToString Duration`) for the `printer` clause. -/
def durationMillis  (d : Cedar.Spec.Ext.Datetime.Duration) : Int := d.toMilliseconds.toInt
def millisToDuration (i : Int) : Cedar.Spec.Ext.Datetime.Duration :=
  Cedar.Spec.Ext.Datetime.Duration.mk (Int64.ofInt i)
def durationToStr (d : Cedar.Spec.Ext.Datetime.Duration) : String := toString d

triptych Duration where
  grammar
    Duration   ::= Sign Components
    Sign       ::= sign
    Components ::= [Days] [Hours] [Minutes] [Seconds] [Millis]
    Days       ::= DDays "d"
    Hours      ::= DHours "h"
    Minutes    ::= DMinutes "m"
    Seconds    ::= DSeconds "s"
    Millis     ::= DMillis "ms"
    DDays      ::= digit+
    DHours     ::= digit+
    DMinutes   ::= digit+
    DSeconds   ::= digit+
    DMillis    ::= digit+
  value
    Sign * (nat DDays * 86400000 + nat DHours * 3600000 + nat DMinutes * 60000
      + nat DSeconds * 1000 + nat DMillis)
    ofSpec millisToDuration
  constraints
    -- Reject "" and "-": every component is optional, so the grammar alone accepts them.
    -- `Components` captures the whole run, so `nonempty Components` = "≥1 component present".
    nonempty Components
    value ∈ [Int64.MIN, Int64.MAX]
  parser Cedar.Spec.Ext.Datetime.Duration.parse toSpec durationMillis
  printer durationToStr
  to "Duration"

#eval Duration.computeValue "1d2h30m"   -- some 95400000
#eval Duration.computeValue "2h"        -- some 7200000 (other units absent → 0)
#eval Duration.computeValue "-4s200ms"  -- some (-4200)  (leading `-` via the `Sign` capture)

end CedarExamples.Duration
