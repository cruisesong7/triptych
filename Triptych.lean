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

import Triptych.Core.Grammar
import Triptych.Core.Classify
import Triptych.Core.Denote
import Triptych.Core.Value
import Triptych.Core.Constraint
import Triptych.Runtime.Scanner
import Triptych.Plan.ScanPlan
import Triptych.Plan.CursorProgram
import Triptych.Plan.SearchPlan
import Triptych.Plan.SearchProgram
import Triptych.Plan.SearchMachine
import Triptych.Runtime.LeanCursor
import Triptych.Runtime.LeanSpanCursor
import Triptych.Plan.ParsePlan
import Triptych.Plan.ScanPlan.Proofs
import Triptych.Plan.SearchPlan.Proofs
import Triptych.Plan.SearchProgram.Proofs
import Triptych.Plan.SearchMachine.Proofs
import Triptych.Plan.ParsePlan.Proofs
import Triptych.Core.Derivation
import Triptych.Runtime.Dependent
import Triptych.Reference.Unambiguity
import Triptych.Elab.Assemble
import Triptych.Reference.Roundtrip
import Triptych.Runtime.Scanner.Proofs
import Triptych.Reference.Coherence
import Triptych.Core.Derivation.Proofs
import Triptych.Runtime.Dependent.Proofs
import Triptych.Reference.RelationalParser
import Triptych.Reference.Unambiguity.Proofs
import Triptych.Elab.Reconcile
import Triptych.Reference.DecodeLemmas
import Triptych.Core.String
import Triptych.Core.Value.Proofs
import Triptych.Automation.ExternalParser
import Triptych.Elab.Syntax

/-!
# Triptych

A (work-in-progress) reusable Lean library for **specifying and verifying flat
non-recursive string-format parsers** — the "verified textual scalar parsing" niche.

Given a grammar for a flat regular attribute-grammar format (dates, decimals,
durations, IP addresses, UUIDs, semver, ...), generate the Lean *specification*
(`IsWf`, `computeValue`) and the parser *contract theorem* surface, auto-discharging
the grammar-generic obligations and delegating the non-affine parts via typed holes.

See `Docs/DESIGN.md` for the full design.

Module layout, by pipeline stage. A stage's theorems sit beside its definitions, as
`<Module>.Proofs`:
* `Triptych.Core.*`       — grammar AST, classifier, denotation, value and constraint DSLs,
                              typed derivations, and consumption analysis
* `Triptych.Reference.*`  — the reference decoder all parser theorems target, the decoder/denotation
                              round trip, coherence, static unambiguity, and relational parsers
* `Triptych.Runtime.*`    — the continuation scanner, dependent formats, and Lean cursor runtimes
* `Triptych.Plan.*`       — `ParsePlan` and its cursor and ordered-search IRs, with lowering proofs
* `Triptych.Elab.*`       — the `triptych` command: syntax, emission, assembly, and the
                              reconciliation lemmas generated proofs use
* `Triptych.Automation.*` — extensible static external-parser proof rules and tactics
* `Triptych.Backend.*`    — the experimental Verus backend
* `Triptych.Tests.*`      — elaboration and backend tests

The Cedar-free Graph example lives in the separate `other-examples` package. Cedar-backed examples
and validation proofs live in `cedar-examples`. The core library has no dependency on either.
-/
