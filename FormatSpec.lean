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

import FormatSpec.Grammar
import FormatSpec.Classify
import FormatSpec.Denote
import FormatSpec.Value
import FormatSpec.Constraint
import FormatSpec.Decode
import FormatSpec.Assemble
import FormatSpec.Roundtrip
import FormatSpec.Reconcile
import FormatSpec.Syntax
import FormatSpec.Examples
-- Worked examples: each `grammar.lean` inputs a `format_spec` and writes ONE generated
-- module beside it (`spec.lean`, in spec/engine/soundness banner sections). Importing the
-- `grammar` files (re)generates; importing the generated `spec` modules builds them
-- standalone, so they can't silently drift from the generator.
import FormatSpec.Examples.Decimal.grammar
import FormatSpec.Examples.Decimal.spec
import FormatSpec.Examples.Duration.grammar
import FormatSpec.Examples.Duration.spec
import FormatSpec.Examples.Datetime.grammar
import FormatSpec.Examples.Datetime.spec
import FormatSpec.Examples.IPv4.grammar
import FormatSpec.Examples.IPv4.spec
import FormatSpec.Examples.IPv6.grammar
import FormatSpec.Examples.IPv6.spec
import FormatSpec.Examples.Graph.grammar
import FormatSpec.Examples.Graph.spec

/-!
# FormatSpec

A (work-in-progress) reusable Lean library for **specifying and verifying flat
non-recursive string-format parsers** — the "verified textual scalar parsing" niche.

Given a grammar for a flat regular attribute-grammar format (dates, decimals,
durations, IP addresses, UUIDs, semver, ...), generate the Lean *specification*
(`IsWf`, `computeValue`) and the parser *contract theorem* surface, auto-discharging
the grammar-generic obligations and delegating the non-affine parts via typed holes.

See `FormatSpec/DESIGN.md` for the full design.

Module layout:
* `FormatSpec.Grammar`  — core grammar data type (what the DSL elaborates into)
* `FormatSpec.Classify` — decidable syntactic classifier (acyclicity, ref resolution)
* `FormatSpec.Denote`     — grammar denotation → `IsWf` (well-formedness predicate)
* `FormatSpec.Value`      — the value-DSL: deep `ValExpr` AST + `eval` denotation
* `FormatSpec.Constraint` — the constraint-DSL: deep `Constraint` AST, auto-classified
                            into `IsWf` (string) / `SatisfiesConstraints` (value) parts
* `FormatSpec.Decode`     — executable capture extractor `decode` + `computeValue`
* `FormatSpec.Roundtrip`  — `decodeSome_iff_IsWf` (`decode` succeeds iff `IsWf`) + the
                            `DecidablePred (IsWf g)` instance derived directly from it
* `FormatSpec.Reconcile`  — reusable lemmas for the auto-emitted proof that the readable
                            surface `IsWf.<start>` equals the engine interpreter `IsWf g`
* `FormatSpec.Assemble`   — bundles ingredients into `isWf`/`satisfiesConstraints`/
                            `isAccepted` (the generated command's top-level predicates)
* `FormatSpec.Syntax`     — the `format_spec` DSL (surface → core `Grammar`; elaborate,
                            and with a `to "<dir>"` clause write the generated `spec.lean`)
* `FormatSpec.Examples`   — hand-written `Grammar` values (Decimal, IPv4) for validation
* `FormatSpec.Examples.<Name>.grammar` — worked example: a `format_spec` input that writes
                            the single generated module `spec.lean` (spec / engine /
                            soundness / contracts banner sections) beside it
-/
