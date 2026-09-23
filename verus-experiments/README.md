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

The Rust backend has two verified execution paths.

For eligible deterministic formats, the shared `Architecture/ScanPlan.lean` compiles the grammar
ahead of time into a structured `ScanPattern`, then derives a linear cursor plan. The plan is
compiled away: `parser.rs` contains direct branches and loops, capture start/end indices, and no
grammar tables or runtime interpreter. Decimal currently uses this path.

The first specialized fragment covers the fixed-point shape used by Decimal:

- one optional ASCII sign literal;
- one nonempty digit capture;
- one required separator;
- one bounded digit capture;
- deterministic boundaries between every field.

The emitted Verus proof establishes that execution agrees exactly with the generated plan
semantics. On success it also constructs the captured-string witnesses required by the readable
root grammar predicate, such as `decimal_is_wf_decimal`.

Grammars outside that specialization use the existing source-faithful flattened grammar scanner:

- arbitrary Unicode literals and Lean-style quoted string literals;
- production references, source-ordered alternatives, and optional items;
- `digit`, `hexDigit`, `bit`, and `asciiRange` token classes;
- exact, bounded, and nonempty-unbounded token lengths;
- bounded or unbounded separated repetition, including nested named repetitions.

Recursive production graphs remain unsupported. Triptych rejects unresolved references, cycles,
duplicate production names, and malformed repetition before emitting Rust.

Both paths expose the same kind of entry point:

```rust
pub fn decimal_parse_candidate(input: &str) -> Option<DecimalParseResult>
```

`DecimalParseResult` contains the complete match position and capture spans. The specialized
parser uses ASCII byte access after a checked `is_ascii` guard, so each cursor access is constant
time. The generic fallback preserves source-order choice and complete capture behavior for the
larger grammar fragment.

This is a verified **grammar and capture parser**, not yet the full semantic
`String -> Option<alpha>` parser emitted by Lean. It does not apply `value`, semantic constraints,
or `ofSpec` at runtime. For example, the Decimal scanner accepts syntactically well-formed values
outside `Int64`; `decimal_is_valid` in `spec.rs` rejects them. Keeping that boundary explicit
avoids claiming that a capture candidate is already a Cedar Decimal value.

The retired bytecode-style `RuntimeProgram` interpreter is archived under
`Triptych/Archive/Verus/`. It is not used by either production path.

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

Value and constraint emission currently supports scalar captures that are direct root references
and the first-order `ValExpr`/`Constraint` fragment. Repeated-capture `count`, qualified or nested
semantic captures, `value'`, and `constraints'` remain unsupported. `ofSpec` and `toSpec` names are
recorded at the conversion boundary; their Lean implementations are not translated into Rust.

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

1. `Architecture/ScanPlan.lean` attempts a fail-closed compilation. Capture nesting is retained
   in `ScanPattern`; `ScanPlan.decode_eq_decodePattern` proves that flattening it into operations
   preserves the complete captured result. Before lowering, an independent executable certificate
   checks source-grammar shape, unique capture slots, and deterministic local boundaries;
   `compileScanPlan_certifiedFor` proves every successful compilation passed it.
2. `Architecture/CursorProgram.lean` lowers the plan into fixed-width and greedy cursor
   instructions. `CursorProgram.lowerScanPlan_run` and `lowerScanPlan_decodePattern` prove that
   the composed lowering preserves complete results and captured strings for every input.
3. `ScanPlan.decodeCertified_eq_decode` and
   `CursorProgram.decodeCertified_eq_decode` prove generic completeness and exact rejection for
   every plan that passes `certifiedFor`: a successful direct result is kept, while direct
   rejection continues through the complete scanner.
4. Eligible fixed-point cursor programs become specialized Rust control flow with generated
   grammar-witness proofs; other certified plans and unsupported direct shapes use
   `RuntimeModel.lean` and the complete checked scanner. Thus completeness is generic even though
   the current straight-line Verus optimization covers a narrower shape.
5. The specification translator maps the same grammar, value, and constraints into typed Verus IR.
6. `Lowering.lean` converts specification operations into the Verus AST and selects only required
   helpers.
7. `PrettyPrint.lean` renders the AST to Verus source.
8. Verus checks the scanner implementation and all emitted proof contracts with
   `--no-cheating`.

The IR is backend-neutral, but only the Rust/Verus emitter currently compiles it away into
specialized source. The Lean runtime can execute either the structured pattern or the same flat
plan; a direct Lean source lowering can be added without changing grammar analysis or semantics.

Triptych's generator and pretty-printer are not formally verified. The safety model is
proof-carrying generation: malformed Rust fails compilation, and an implementation that does not
satisfy its emitted Verus contract fails verification. Lean also proves preservation for the
supported value and arithmetic-constraint translations through the internal Verus AST.

The specialized Decimal certificate proves exact agreement with `decimal_parse_plan` and both
directions of the readable grammar contract. Success implies `decimal_is_wf_decimal`; the
generated `decimal_is_wf_implies_parse_plan` theorem makes rejection imply its negation.
Executable value computation, semantic-constraint checking, and conversion to the domain result
type remain future work. The current Rust artifact is therefore a verified grammar-and-capture
parser, not yet the full `String -> Option<Decimal>` parser emitted by Lean.

## Evidence

`grammar-coverage/` is generated from one declaration that combines every shared grammar
constructor: Unicode literals, quoted strings, all token classes and length forms, references,
alternatives, optionals, bounded and unbounded repetition, nested named repetition, and an
ambiguous token alternative. Its Verus and Rust tests exercise accepted and rejected inputs.

`cedar-ext/decimal/` contains:

- the generated Decimal specification and scanner;
- Rust tests for grammar acceptance, including long inputs;
- Cedar's production-parser corpus through Cedar's public API;
- a benchmark harness comparing the generated grammar scanner with a Cedar-style regex path.

The optimized benchmark uses `"-1234567890.1234"` over five million iterations:

| implementation | ns/parse | relative to ScanPlan |
| --- | ---: | ---: |
| generated Triptych ScanPlan | 13.86 | 1.00x |
| Cedar regex recognition | 79.87 | 5.76x slower |
| Cedar-style regex plus value computation | 93.57 | 6.75x slower |

The old generic candidate scanner measured about `5.7 us/parse` on the same development machine.
The large improvement comes from eliminating candidate vectors, capture-map copying, grammar
validation, and runtime grammar traversal.

The recognition comparison is the closest like-for-like row. The full Cedar-style path also
computes an `i64`, while the generated function currently returns capture spans. These are
wall-clock measurements, not a formal timing guarantee.

## Commands

From the repository root:

```sh
./verus-experiments/setup-verus.sh
lake build Triptych.Backend.VerusTests Triptych.Architecture.ScanPlanTests \
  Triptych.Backend.Verus.RuntimeModelTests
lake env lean verus-experiments/grammar-coverage/Input.lean
(cd cedar-examples && lake build Inputs.Decimal)
./verus-experiments/verify.sh
cargo test --manifest-path verus-experiments/grammar-coverage/Cargo.toml --offline --locked
cargo test --manifest-path verus-experiments/cedar-ext/decimal/Cargo.toml --offline --locked
cargo bench --manifest-path verus-experiments/cedar-ext/decimal/Cargo.toml \
  --bench runtime --offline --locked
```

The setup script pins Verus `0.2026.08.30.b432e82` and its required Rust toolchain.
