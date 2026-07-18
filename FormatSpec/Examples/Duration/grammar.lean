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
# Duration example — five optional unit components (peel/all-optional stress test)

Transcribes `doc/CedarDoc/Duration.lean`:
```
Duration   ::= ['-'] Components
Components ::= [Days] [Hours] [Minutes] [Seconds] [Millis]
Days       ::= Digit⁺ 'd'   (etc.)
```
Exercises the peel-form binder naming (optional refs → `days`/`hours`/…) and the
all-optional `Components` reconciliation (the O(2⁵) present/absent tree ⟺ flat form).
Writes `engine.lean` + `spec.lean` next to this file.
-/

namespace FormatSpec.Examples.Duration
open FormatSpec

-- SUB-CAPTURE PATTERN: each unit's digit-run is its own nonterminal (`DDays ::= digit+`),
-- so `value` can read the number via `nat DDays` — `Days ::= DDays "d"` captures both the
-- full `"1d"` (as `Days`) AND the digits `"1"` (as `DDays`), since `decode` records nested
-- refs. This resolves the "`nat Days` on `"1d"` is garbage" problem with no new machinery.
format_spec Duration where
  grammar
    Duration   ::= ["-"] Components
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
    nat DDays * 86400000 + nat DHours * 3600000 + nat DMinutes * 60000
      + nat DSeconds * 1000 + nat DMillis
  constraints
    -- At least one component present. Every component is optional, so the grammar alone
    -- accepts "" and "-"; this rejects them. `Components` captures the whole `[Days][Hours]…`
    -- run as one string, so `nonempty Components` says exactly "≥1 component present" — no
    -- need to list them. (For a grammar with no wrapping nonterminal, use the SAT-style
    -- `atLeast 1 {Days, Hours, …}`.) (Component *ordering* is NOT a constraint — the fixed
    -- positional `Components ::= [Days][Hours]…` grammar rule already enforces it.)
    nonempty Components
    value ∈ [Int64.MIN, Int64.MAX]
  -- Write the single generated module `spec.lean` into this example's directory.
  to "FormatSpec/Examples/Duration"

-- Inspect the generated per-production predicates + their binder names.
#check (Duration.IsWf.Duration   : String → Prop)
#check (Duration.IsWf.Components : String → Prop)

-- The value function reads the sub-captured digit runs (not the "1d" strings):
--   "1d2h30m" = 1·86400000 + 2·3600000 + 30·60000 = 95400000
#eval Duration.computeValue "1d2h30m"   -- some 95400000
#eval Duration.computeValue "500ms"     -- some 500
#eval Duration.computeValue "2h"        -- some 7200000 (other units absent → 0)

-- Reconciliation + decidability of the all-optional `Components` shape (standard axioms).
#check (Duration.IsWf_equiv : ∀ s, IsWf Duration.grammar s ↔ Duration.IsWf.Duration s)
example : DecidablePred Duration.IsWf.Duration := inferInstance

end FormatSpec.Examples.Duration
