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

Transcribes `doc/CedarDoc/Duration.lean`:
```
Duration   ::= ['-'] Components
Components ::= [Days] [Hours] [Minutes] [Seconds] [Millis]
Days       ::= Digit⁺ 'd'   (etc.)
```
Exercises the peel-form binder naming (optional refs → `days`/`hours`/…) and the
all-optional `Components` reconciliation (the O(2⁵) present/absent tree ⟺ flat form).
Writes the generated modules `spec.lean` / `parser.lean` / `soundness.lean` next to this file
(`soundness.lean` because of the `parser` + `printer` clauses).
-/

namespace Triptych.Examples.Duration
open Triptych

/- External parser + printer: Cedar's own `Duration.parse : String → Option Duration`, projected
to its millisecond `Int` value (`Duration.val : Int64`, via `toMilliseconds.toInt`) — matching
our `computeValue` (also milliseconds). The `lift millisToDuration` upgrades the GENERATED
parser's output from the spec value `Int` (millis) to the DOMAIN type `Duration`, a section of
the projection `durationMillis`. So the generated parser and Cedar's both return
`Option Duration`, and the ONE domain serializer `durationToStr` (reusing Cedar's
`ToString Duration`) drives each side's printer theorems — `parse_toString_*` (generated) and
`extparse_toString_*` (external) — in the clean δ-VIEW `parse (durationToStr d) = some d`. -/
def durationMillis  (d : Cedar.Spec.Ext.Datetime.Duration) : Int := d.toMilliseconds.toInt
def millisToDuration (i : Int) : Cedar.Spec.Ext.Datetime.Duration :=
  Cedar.Spec.Ext.Datetime.Duration.mk (Int64.ofInt i)
def durationToStr (d : Cedar.Spec.Ext.Datetime.Duration) : String := toString d

/- SUB-CAPTURE PATTERN: each unit's digit-run is its own nonterminal (`DDays ::= digit+`),
so `value` can read the number via `nat DDays` — `Days ::= DDays "d"` captures both the
full `"1d"` (as `Days`) AND the digits `"1"` (as `DDays`), since `decode` records nested
refs. This resolves the "`nat Days` on `"1d"` is garbage" problem with no new machinery. -/
format_spec Duration where
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
    lift millisToDuration
  constraints
    -- At least one component present. Every component is optional, so the grammar alone
    -- accepts "" and "-"; this rejects them. `Components` captures the whole `[Days][Hours]…`
    -- run as one string, so `nonempty Components` says exactly "≥1 component present" — no
    -- need to list them. (For a grammar with no wrapping nonterminal, use the SAT-style
    -- `atLeast 1 {Days, Hours, …}`.) (Component *ordering* is NOT a constraint — the fixed
    -- positional `Components ::= [Days][Hours]…` grammar rule already enforces it.)
    nonempty Components
    value ∈ [Int64.MIN, Int64.MAX]
  parser Cedar.Spec.Ext.Datetime.Duration.parse projection durationMillis
  printer durationToStr
  -- Write the generated modules `spec.lean` / `parser.lean` / `soundness.lean` into this dir.
  to "Triptych/Examples/Duration"

-- Inspect the generated per-production predicates + their binder names.
#check (Duration.IsWf.Duration   : String → Prop)
#check (Duration.IsWf.Components : String → Prop)

/- The value function reads the sub-captured digit runs (not the "1d" strings):
`"1d2h30m"` = 1·86400000 + 2·3600000 + 30·60000 = 95400000 -/
#eval Duration.computeValue "1d2h30m"   -- some 95400000
#eval Duration.computeValue "500ms"     -- some 500
#eval Duration.computeValue "2h"        -- some 7200000 (other units absent → 0)
#eval Duration.computeValue "-4s200ms"  -- some (-4200)  (leading `-` via the `Sign` capture)

-- Reconciliation + decidability of the all-optional `Components` shape (standard axioms).
#check (Duration.IsWf_equiv : ∀ s, IsWf Duration.grammar s ↔ Duration.IsWf.Duration s)
example : DecidablePred Duration.IsWf.Duration := inferInstance

/- The generated verified parser (LIFTED to the domain type by `lift millisToDuration`) + printer
theorems for BOTH parsers, δ-view via the single domain serializer `durationToStr`.
`parse_sound_proj` is the π-view soundness, from the `lift_faithful` obligation (provable
thanks to the Int64 range constraint). -/
#check (Duration.parse : String → Option Cedar.Spec.Ext.Datetime.Duration)
#check @Duration.parse_sound
#check @Duration.parse_sound_proj
-- INTERNAL printer (generated lifted parser):
#check @Duration.parse_toString_roundtrip  -- ∀ d, Duration.parse (durationToStr d) = some d
#check @Duration.toString_injective
#check @Duration.normalize_eq_iff_parse_eq
-- EXTERNAL parser (Cedar's real Duration.parse) + its printer theorems, same serializer:
#check @Duration.extparse_sound
#check @Duration.extparse_toString_roundtrip  -- ∀ d, Cedar…Duration.parse (durationToStr d) = some d
#check @Duration.extparse_toString_injective
#check @Duration.extparse_normalize_eq_iff_parse_eq

end Triptych.Examples.Duration
