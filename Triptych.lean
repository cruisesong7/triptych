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
import Triptych.Architecture.Derivation
import Triptych.Architecture.Unambiguity
import Triptych.Architecture.Assemble
import Triptych.Theorems.Roundtrip
import Triptych.Theorems.Coherence
import Triptych.Theorems.Derivation
import Triptych.Theorems.RelationalParser
import Triptych.Theorems.Unambiguity
import Triptych.Theorems.Reconcile
import Triptych.Theorems.DecodeLemmas
import Triptych.Theorems.String
import Triptych.Theorems.Value
import Triptych.Automation.ExternalParser
import Triptych.Architecture.Syntax

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
* `Triptych.Theorems.*`     — reusable decoder, roundtrip, coherence, unambiguity, and
                                reconciliation theorems
* `Triptych.Automation.*`   — extensible static external-parser proof rules and tactics

The Cedar-free Graph example lives in the separate `other-examples` package. Cedar-backed examples
and validation proofs live in `cedar-examples`. The core library has no dependency on either.
-/
