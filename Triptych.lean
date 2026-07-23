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

import Triptych.Architecture.Grammar
import Triptych.Architecture.Classify
import Triptych.Architecture.Denote
import Triptych.Architecture.Value
import Triptych.Architecture.Constraint
import Triptych.Architecture.Decode
import Triptych.Architecture.Assemble
import Triptych.Theorems.Roundtrip
import Triptych.Theorems.Reconcile
import Triptych.Architecture.Syntax
import Triptych.Examples
-- Worked examples: each `grammar.lean` inputs a `triptych` and writes the generated
-- modules beside it — `spec.lean` (readable surface), `parser.lean` (engine + auto-discharged
-- proofs + the generated verified parser), and, when the `triptych` has a `parser` clause,
-- `soundness.lean` (the `sorry`d external-parser obligations). Importing the `grammar` files
-- (re)generates; importing the generated modules builds them standalone (so they can't
-- silently drift from the generator).
import Triptych.Examples.Decimal.grammar
import Triptych.Examples.Decimal.spec
import Triptych.Examples.Decimal.parser
import Triptych.Examples.Decimal.soundness
import Triptych.Examples.Duration.grammar
import Triptych.Examples.Duration.spec
import Triptych.Examples.Duration.parser
import Triptych.Examples.Duration.soundness
import Triptych.Examples.Datetime.grammar
import Triptych.Examples.Datetime.spec
import Triptych.Examples.Datetime.parser
import Triptych.Examples.Datetime.soundness
import Triptych.Examples.IPv4.grammar
import Triptych.Examples.IPv4.spec
import Triptych.Examples.IPv4.parser
import Triptych.Examples.IPv6.grammar
import Triptych.Examples.IPv6.spec
import Triptych.Examples.IPv6.parser
import Triptych.Examples.Graph.grammar
import Triptych.Examples.Graph.spec
import Triptych.Examples.Graph.parser

/-!
# Triptych

A (work-in-progress) reusable Lean library for **specifying and verifying flat
non-recursive string-format parsers** — the "verified textual scalar parsing" niche.

Given a grammar for a flat regular attribute-grammar format (dates, decimals,
durations, IP addresses, UUIDs, semver, ...), generate the Lean *specification*
(`IsWf`, `computeValue`) and the parser *contract theorem* surface, auto-discharging
the grammar-generic obligations and delegating the non-affine parts via typed holes.

See `Docs/DESIGN.md` for the full design.

Module layout:
* `Triptych.Architecture.*` — grammar, classifier, denotation, decoder, value/constraint
                                DSLs, assembly, emission, and `triptych` syntax
* `Triptych.Theorems.*`     — reusable decoder, roundtrip, reconciliation, and external
                                parser bridge theorems
* `Triptych.Examples`   — hand-written `Grammar` values (Decimal, IPv4) for validation
* `Triptych.Examples.<Name>.grammar` — worked example: a `triptych` input that writes
                            the single generated module `spec.lean` (spec / engine /
                            soundness / contracts banner sections) beside it
-/
