# Verus backend experiment

Triptych can emit three Rust/Verus artifacts from the same elaborated declaration used by the
Lean backend:

- `spec.rs`: readable grammar, view, value, constraint, and validity specifications;
- `parser.rs`: an executable proof-carrying grammar parser;
- `soundness.rs`: a write-once contract for an optional external parser.

The `verus` clause emits `spec.rs` and `parser.rs` as one fail-closed result. Triptych validates
both output paths before writing either file, never exposes a separate uncertified parser emitter,
and never asks for a format-specific proof of the generated scanner.

## Generated parser

The Rust backend follows the three shared `ParsePlan` cases.

`Architecture/ParsePlan.lean` makes one backend-neutral strategy decision for each elaborated
grammar. For eligible deterministic formats, its cursor case carries the certified
`Architecture/ScanPlan.lean`; that plan is lowered to a linear `CursorProgram` and compiled away.
`parser.rs` then contains direct branches and loops, capture start/end indices, and no grammar
tables or runtime interpreter. Decimal currently uses this path.

A search case lowers the resolved acyclic branching plan through `SearchProgram` and
`SearchMachine`, hash-conses shared suffixes, and emits one Verus specification/executable pair
per machine state. Ordered alternatives and optionals remain direct choices. Finite separated
repetitions are unrolled at generation time, including their count captures and
stop-before-continue policy. Executable states mutate one bounded state transactionally: failure
restores the cursor, captures, and marker stack exactly, so ordered choice needs no whole-state
clone. Duration, Datetime, IPv4, and IPv6 use this path. If direct state emission cannot represent
a search plan, generation fails with that unsupported shape. The scanner case records why neither
specialized plan compiled; it is a diagnostic, not an emitted runtime fallback.

The specialized fragment covers every grammar accepted by the shared `ScanPlan` compiler:

- acyclic productions with one alternative each;
- nested named captures;
- single-character ASCII literals and optional literals;
- fixed, bounded, or nonempty token runs over digit, hexadecimal, bit, or ASCII-range classes;
- deterministic local boundaries between variable-width fields.

The emitted proof is compositional rather than format-shaped. On success it reconstructs each
production predicate bottom-up from source spans. For completeness it unpacks the same witnesses
top-down, derives every cursor boundary, and proves that the plan cannot reject a well-formed
input. Decimal, Quantity, and the nested `direct-coverage` grammar all use this path.

The search-state path extends direct emission to:

- arbitrary Unicode literals and Lean-style quoted string literals;
- production references, source-ordered alternatives, and optional items;
- `digit`, `hexDigit`, `bit`, and `asciiRange` token classes;
- exact, bounded, and nonempty-unbounded token lengths;
- finite bounded separated repetition, including nested named repetitions.

Unbounded repetition and any direct shape rejected by the state compiler fail generation with a
specific diagnostic.

Recursive production graphs remain unsupported. Triptych rejects unresolved references, cycles,
duplicate production names, and malformed repetition before emitting Rust.

All cases expose the same grammar entry point:

```rust
pub fn decimal_parse_candidate(input: &str) -> Option<DecimalParseResult>
```

`DecimalParseResult` contains the complete match position and capture spans. The specialized
parser uses ASCII byte access after a checked `is_ascii` guard, so each cursor access is constant
time. Search-state parsers call verified literal/token helpers and carry capture spans through
generated control flow without grammar-table traversal.

Search-machine entry points compute Unicode length and ASCII classification once. Literal helpers
use byte matching for ASCII inputs and a Unicode-correct fallback otherwise. Variable-width token
states scan the maximal accepted prefix once, then test only the widths allowed by the grammar in
their original order. Capture keys map to fixed slots, and capture/marker capacities are computed
at generation time. These are optimizations of the proof-carrying state machine, not a second
unchecked implementation.

For supported semantics, `parser.rs` additionally exposes the final domain parser. The Cedar
examples now generate:

```rust
pub fn decimal_parse(input: &str) -> Option<i64>
pub fn duration_parse(input: &str) -> Option<i64>
pub fn datetime_parse(input: &str) -> Option<i64>
pub fn ipv4_parse(input: &str) -> Option<IPv4ParseResult>
pub fn ipv6_parse(input: &str) -> Option<IPv6ParseResult>
```

These functions execute the generated `value`, check the declared constraints, and implement the
registered `ofSpec` conversion. Verus proves that every returned value comes from a matching
grammar candidate, satisfies the generated validity conditions, and equals the generated
denotation. The capture parser remains separately available because grammar recognition can
accept a syntactically well-formed value that semantic constraints reject.

The executable semantic plan supports the operations used by the five Cedar formats: natural,
signed, hexadecimal, hexadecimal-sequence, segment-count, length, and repetition-count readers;
integer arithmetic, truncating division and remainder, conditions, and exponentiation; cardinality,
string, leading-zero, and arithmetic constraints; checked `i64` conversion; and structured IPv4
and IPv6 results. IPv6 multiplication by a power is fused so the runtime does not first construct
the out-of-range intermediate value `2^128`.

Unsupported conversion or constraint combinations do not prevent grammar-parser generation. They
omit the final-value entry point and retain the certified candidate parser.

The retired bytecode-style `RuntimeProgram` interpreter and the generic table-driven runtime
parser were removed after commit `597381b`; consult that commit for their design history.

## Readable specification

The Verus surface follows the generated Lean specification:

| Lean | Verus |
| --- | --- |
| `Decimal.IsWf.Sign` | `decimal_is_wf_sign` |
| `Decimal.IsWf.Decimal` | `decimal_is_wf_decimal` |
| `Decimal.View` | `DecimalView` |
| `Decimal.value` | `decimal_value` |
| `Decimal.SatisfiesConstraints` | `decimal_satisfies_constraints` |
| `Decimal.IsValid` | `decimal_is_valid` |

Text is represented as `Seq<char>`, matching Lean strings by Unicode code point rather than
silently narrowing them to bytes. Grammar predicates support the same shared grammar constructors
as the scanner.

The readable specification supports the first-order `ValExpr`/`Constraint` fragment, qualified
and nested scalar captures, and separated-repetition counts. Generated View relations connect
those fields back to the grammar rather than treating them as unconstrained inputs. Opaque
`value'` and `constraints'` escapes remain unsupported. Executable conversions are generated for
the checked signed values and structured IP values used by the Cedar extension examples.

## External parser contract

When a declaration has a `parser` clause, Triptych creates `soundness.rs` once. Its generated trait
states soundness, completeness, and exact rejection for an adapter connected to that parser.
Triptych does not overwrite this file because the adapter and its proofs are user-owned.

This contract is separate from the generated scanner certificate:

- `parser.rs` is regenerated and requires no per-format proof;
- `soundness.rs` verifies another implementation, such as Cedar's existing regex parser.

## Translation and checking

The DSL is parsed once into `Grammar`, `ValExpr`, and `Constraint` values shared with Lean
generation.

1. `Architecture/ParsePlan.lean` selects a cursor plan or the complete scanner once. Lean and
   Verus consume this same value rather than repeating grammar capability analysis.
2. `Architecture/ScanPlan.lean` attempts a fail-closed deterministic compilation. Capture nesting
   is retained in `ScanPattern`; `ScanPlan.decode_eq_decodePattern` proves that flattening it into
   operations preserves the complete captured result. Before lowering, an independent executable
   certificate checks source-grammar shape, unique capture slots, and deterministic local
   boundaries; `compileScanPlan_certifiedFor` proves every successful compilation passed it.
3. `Architecture/SearchPlan.lean` resolves references and capture keys for the remaining
   supported acyclic grammar surface. It retains source-ordered alternatives, optionals, and
   repetitions, and its continuation executor avoids candidate-list construction.
4. `Architecture/SearchProgram.lean` fuses sequence tails and ordered alternatives into explicit
   continuation control flow, then removes dead arms and shares certified literal, fixed-width
   token, and committed capture prefixes. `SearchCode.nodeCount_reduce_le` proves that this
   reduction cannot enlarge the staged control-flow tree, while
   `SearchProgram.lowerSearchPlan_decode` proves exact preservation of the selected capture map.
5. `Architecture/SearchMachine.lean` totally lowers every search program into explicit capture,
   choice, and repetition states. `SearchMachine.lowerSearchPlan_decode_eq_scan` proves exact
   agreement with the complete scanner.
6. `Architecture/CursorProgram.lean` lowers deterministic plans into fixed-width and greedy cursor
   instructions. `CursorProgram.lowerScanPlan_run` and `lowerScanPlan_decodePattern` prove that
   the composed lowering preserves complete results and captured strings for every input.
7. `ScanPlan.decode_eq_decode`, `SearchPlan.decode_eq_scanSearch`,
   `SearchProgram.lowerSearchPlan_decode`, and
   `CursorProgram.decode_eq_decode` prove generic soundness,
   completeness, and exact rejection for every plan that passes `certifiedFor`; the direct
   cursor or ordered-search result is final on both success and rejection.
8. Lean emits certified cursor programs and continuation-fused search programs directly. Verus
   compiles cursor operations and callback-free search-machine states into direct generated code.
   Shared state suffixes are hash-consed. Finite repetitions are unrolled into item, separator,
   ordered-stop, and count-capture states. Failed states prove exact transactional rollback, so
   alternatives reuse one mutable state without copying capture vectors. Unsupported direct shapes
   fail generation instead of silently selecting another runtime.
9. The specification translator maps the same grammar, value, and constraints into typed Verus IR.
10. `Lowering.lean` converts specification operations into the Verus AST and selects only required
   helpers.
11. `PrettyPrint.lean` renders the AST to Verus source.
12. Verus checks the scanner implementation and all emitted proof contracts with
   `--no-cheating`.

The strategy, search-program, search-machine, and cursor IRs are backend-neutral. Lean and Verus
specialize both parser-plan tiers. The generated Verus state functions are checked
compositionally against their matching state specifications.

Triptych's generator and pretty-printer are not formally verified. The safety model is
proof-carrying generation: malformed Rust fails compilation, and an implementation that does not
satisfy its emitted Verus contract fails verification. Lean also proves preservation for the
supported value and arithmetic-constraint translations through the internal Verus AST.

Each specialized certificate proves exact agreement with its generated parse plan and both
directions of the readable grammar contract. For Decimal, success implies
`decimal_is_wf_decimal`; the generated `decimal_is_wf_implies_parse_plan` theorem makes grammar
rejection imply its negation. The generated semantic function then proves successful
`String -> Option<i64>` results against `decimal_matches_view`, `decimal_view_valid`, and
`decimal_view_denotation`.

## Evidence

`grammar-coverage/` is generated from one declaration that combines every shared grammar
constructor: Unicode literals, quoted strings, all token classes and length forms, references,
alternatives, optionals, bounded repetition, nested named repetition, and an ambiguous token
alternative. Unbounded separated repetition (`rep X sepBy "," +`) is accepted by the Lean backend
but rejected by Verus state emission, so this crate bounds its CSV repetition at eight cells. Its Verus and Rust tests exercise accepted and rejected inputs.

`search-order/` is a regression for ordered choice: both alternatives accept `"ab"`, and the
generated parser must select the first one, as the Lean scanner does. A literal-guided dispatch
used to try the second arm first whenever its required literal was present.

`direct-coverage/` exercises the specialized path beyond Decimal: nested captures, an optional
literal, required delimiters, fixed and greedy runs, and every direct token class. Verus checks
the generated success and no-false-rejection proofs with `--no-cheating`.

`cedar-ext/decimal/` and `cedar-ext/suite/` contain:

- generated specifications, candidate scanners, and final semantic parsers;
- Rust tests for grammar acceptance, including long inputs;
- cases copied from Cedar's production-parser unit tests;
- benchmark harnesses calling Cedar's feature-gated production parsers directly.

The suite compares exact returned values for Datetime, Duration, Decimal, IPv4, and IPv6,
including semantic rejection after successful grammar recognition. The generated scanner has
formal soundness, completeness, and exact-rejection certificates. The final semantic parser has
generated success and conditional exact-rejection contracts. For the scanner-selected candidate,
success proves validity and the exact denotation. Rejection proves either semantic invalidity or
failure of the generated `candidate_runtime_safe` predicate. The direct fixed-point path states
the same result through its selected typed view and `view_runtime_safe`.

The runtime-safety premise records capture bounds, positive divisors, and every checked
intermediate fitting its executable integer representation. It is necessary for the general
value DSL: an arbitrary expression can overflow an intermediate and later cancel back into the
final result range. The Cedar corpus remains additional executable evidence that the generated
specification matches the intended production behavior.

The benchmark reports grammar scanning separately from final value and constraint evaluation.
One warmed release run on the same development machine measured:

| format | Triptych scan | Triptych full | Cedar production |
| --- | ---: | ---: | ---: |
| Decimal | 11.98 ns | 25.20 ns | 89.75 ns |
| Duration | 60.11 ns | 49.37 ns | 223.19 ns |
| Datetime | 83.50 ns | 105.02 ns | 292.21 ns |
| IPv4 | 26.41 ns | 44.35 ns | 24.47 ns |
| IPv6 | 100.07 ns | 112.60 ns | 99.05 ns |

Decimal uses the straight-line cursor plan; the other four use generated search-machine states.
The generated full parsers were 3.56x, 4.52x, and 2.78x faster than Cedar's production Decimal,
Duration, and Datetime parsers in this run. IPv4 remained 1.81x slower and IPv6 1.14x slower.
Bounded primitive lowering reduced the machinery emitted for IPv4 value arithmetic, but capture
lookup and decimal decoding still dominate its end-to-end time.
The isolated Duration scan is slower than the full parser because release inlining can fuse the
scanner with semantic evaluation and eliminate intermediate candidate materialization.

The search-machine emitter scans each variable-width token prefix once. Compact decimal fields
such as IPv4 octets and date components additionally use a verified decoder with a fixed
four-character bound, giving the optimizer a small unrollable loop while preserving the same
unbounded mathematical specification. Longer fields retain the exact checked decoder.

These are wall-clock measurements from one development machine, not a formal timing guarantee.
The formal result is behavioral: the generated cursor or search machine returns exactly the
certified scanner result, including success captures and rejection. Ambiguous ordered search can
still branch exponentially.

## Commands

From the repository root:

```sh
./verus-experiments/setup-verus.sh
lake build Triptych.Backend.VerusTests Triptych.Architecture.ScanPlanTests \
  Triptych.Backend.Verus.RuntimeModelTests
lake env lean verus-experiments/grammar-coverage/Input.lean
lake env lean verus-experiments/direct-coverage/Input.lean
lake env lean verus-experiments/search-order/Input.lean
(cd cedar-examples && lake build Inputs.Decimal)
./verus-experiments/verify.sh
cargo test --manifest-path verus-experiments/grammar-coverage/Cargo.toml --offline --locked
cargo test --manifest-path verus-experiments/direct-coverage/Cargo.toml --offline --locked
cargo test --manifest-path verus-experiments/search-order/Cargo.toml --offline --locked
cargo test --manifest-path verus-experiments/cedar-ext/decimal/Cargo.toml --offline --locked
cargo test --manifest-path verus-experiments/cedar-ext/suite/Cargo.toml --offline --locked
cargo bench --manifest-path verus-experiments/cedar-ext/decimal/Cargo.toml \
  --bench runtime --offline --locked
cargo bench --manifest-path verus-experiments/cedar-ext/suite/Cargo.toml \
  --bench runtime --offline --locked
```

The setup script pins Verus `0.2026.08.30.b432e82` and its required Rust toolchain.
