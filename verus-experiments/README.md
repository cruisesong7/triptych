# Verus backend experiment

Triptych emits three Rust/Verus artifacts from the same elaborated declaration used by the Lean
backend:

- `spec.rs`: readable grammar, view, value, constraint, and validity specifications;
- `parser.rs`: generated proof machinery for grammar recognition, captures, and supported
  semantic conversions;
- `contract.rs`: external-parser and optional serializer proof obligations.

The user-owned `soundness.rs` implements that contract for an optimized Rust parser.

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

Both grammar paths expose the same kind of entry point:

```rust
pub fn decimal_parse_candidate(input: &str) -> Option<DecimalParseResult>
```

`DecimalParseResult` contains the complete match position and capture spans. The specialized
parser uses ASCII byte access after a checked `is_ascii` guard, so each cursor access is constant
time. The generic fallback preserves source-order choice and complete capture behavior for the
larger grammar fragment.

For Decimal's recognized fixed-point shape, the backend additionally emits a crate-private
semantic proof core:

```rust
pub(crate) fn decimal_parse(input: &str) -> Option<i64>
```

The write-once external-parser module exposes the production entry point:

```rust
DecimalParser::parse(input: &str) -> Option<i64>
```

It implements `DecimalExternalParserContract`; Verus therefore proves soundness, completeness,
exact rejection, and equality between each successful machine result and the generated view
denotation. The crate-private core evaluates the generated value formula, enforces its `Int64`
range constraint, and applies the `Int64.ofInt` conversion as Rust's checked `i64`
representation. The bounded digit fold stops updating its machine accumulator after the
natural-part limit is crossed, so arbitrarily long leading-zero runs remain accepted without
risking machine-integer overflow.

Formats outside the recognized semantic shape continue to receive the verified grammar/capture
entry point only. For example, `decimal_parse_candidate` intentionally accepts syntactically
well-formed values outside `Int64`; `DecimalParser::parse` rejects them.

The retired bytecode-style `RuntimeProgram` interpreter is archived under
`Triptych/Archive/Verus/`. It is not used by either production path.

## Readable specification

The Verus surface follows the generated Lean specification:

| Lean | Verus |
| --- | --- |
| `Decimal.IsWf.Sign` | `decimal_is_wf_Sign` |
| `Decimal.IsWf.Decimal` | `decimal_is_wf_Decimal` |
| `Decimal.View` | `DecimalView` |
| `Decimal.value` | `decimal_value` |
| `Decimal.SatisfiesConstraints` | `decimal_satisfies_constraints` |
| `Decimal.IsValid` | `decimal_is_valid` |

Text is represented as `Seq<char>`, matching Lean strings by Unicode code point rather than
silently narrowing them to bytes. Grammar predicates support the same shared grammar constructors
as the scanner.

Value and constraint emission supports the analyzable `Int` DSL used by all four Cedar extension
families. That includes qualified captures, repeated-capture counts, hexadecimal fields,
colon-separated IPv6 accumulation, segment counts, sign prefixes, arithmetic conditionals,
truncating division and remainder, and expanded Gregorian `daysInMonth`/`daysFromCivil`
expressions. `ofSpec` and `toSpec` define the conversion boundary to Cedar's structured domain
types; their Lean implementations are not copied into Rust.

Decimal, Duration, Datetime, IPv4, and IPv6 are all emitted by elaborating their actual
`triptych` declarations in `cedar-examples/Inputs`. There is no Cedar-specific Verus template or
profile generator. Each declaration reproducibly emits its own `spec.rs`, `parser.rs`, and
`contract.rs`.

The optimized parser and its trait implementation in `soundness.rs` remain independently
maintained. Regeneration therefore updates the specification boundary without overwriting
production parser code or proofs.

### Generated-artifact drift guard

Checked-in `spec.rs`, `parser.rs`, and `contract.rs` files are the Verus snapshots. CI can verify
that they still match the actual Triptych translation without first overwriting them:

```sh
lake exe triptych -- check-verus \
  cedar-examples/Inputs/Decimal.lean \
  cedar-examples/Inputs/Duration.lean \
  cedar-examples/Inputs/Datetime.lean \
  cedar-examples/Inputs/IPv4.lean \
  cedar-examples/Inputs/IPv6.lean
```

The default `--syntax` mode compares lexical Rust/Verus tokens, ignoring only whitespace and
comments outside string, character, and raw-string literals. A changed identifier, literal,
operator, declaration, proof contract, or missing/stale generated file fails the command.
`--exact` instead requires byte-for-byte equality.

The checker regenerates expected output in memory and makes Triptych's `verus` and `to` clauses
read-only for that process. Handwritten `optimized.rs`, `soundness.rs`, printer proofs, and other
production code are outside the generated snapshot set.

### Vermilion semantic roundtrip guard

`check-verus-roundtrip` is a developer tool for work on the Verus backend. Format authors never
need to run it. It adds an independent translation check around the generated Verus
specification:

```sh
lake exe triptych -- check-verus-roundtrip \
  --vermilion-root /path/to/vermilion \
  cedar-examples/Inputs/Decimal.lean
```

For each `verus` clause, Triptych deterministically emits temporary artifacts:

- the exact checked-in `spec.rs`;
- the same source plus a proof-only anchor that makes Vermilion recover every generated spec
  function;
- a Lean alias module for the recovered definitions;
- direct public theorem statements comparing those definitions with the original generated Lean
  specification;
- a generated check module that independently repeats every expected theorem type;
- a manifest fixing the generated module and public theorem names.

The theorem statements cover every generated function with a declared Lean counterpart. They also
generate the complete parser-result bridge:

- `view_denotation` and `view_valid` align the recovered per-view computations;
- `matching_view_normalizes` proves that every recovered matching view over an encoded Lean
  string has fields that are themselves encoded Lean strings;
- `matches_view_exact` pins every recovered view field to its exact named
  `Triptych.component`, including qualified captures such as `Time.hh` and `Offset.hh`;
- `matching_view_exists` aligns root-grammar recognition; and
- `matches_result` equates Lean's valid `computeValue` result with the recovered Verus
  `*_matches_result` relation.

The generated `*_matches_result` relation lives in `spec.rs`, so Vermilion translates the actual
relation consumed by external-parser contracts. `contract.rs` publicly re-exports the generated
specification API for compatibility with downstream proofs. Obligation order and names come solely
from the translated `FormatInput` and emitted IR. A separately maintained
`verus-experiments/vermilion-roundtrip/proofs/TriptychVermilionProofs/<Format>.lean` module must prove each public theorem
named in the manifest.

Direct counterparts are unconditional. A `SatisfiesConstraints` counterpart is guarded by the
start production's `IsWf` predicate because the Lean decoder returns default captures on malformed
input, while the generated Verus predicate requires an actual matching view.

The command fails unless the exact snapshot check passes, the source project and Vermilion use
the same Lean toolchain, Vermilion emits the recovered definitions, the generated aliases,
direct check module, and developer proof compile together, the pinned `encodeString` bridge is
unchanged, and every manifest theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`. Temporary artifacts are retained after failure for inspection; each artifact set
records the Vermilion root, toolchain, and revision (or a `lake-manifest.json` fingerprint when
the checkout has no git metadata) in `vermilion.txt`.

## External parser contract

When a declaration has a `parser` clause, Triptych creates `soundness.rs` once. Its generated trait
states soundness, completeness, and exact rejection for the optimized Rust parser. Triptych does
not overwrite this file because the implementation and its proofs are user-owned.

When the same declaration also has a `printer` clause, the generated external contract adds:

- `extparse_to_string_roundtrip`;
- `extparse_to_string_injective`;
- `extparse_normalize_eq_iff_parse_eq`.

The contract includes `to_string_to_spec`, the specification view of the external canonical
serializer. Its roundtrip and injectivity obligations are restricted to domain values
representable by some valid external-parser input.

For Decimal, `DecimalParser` implements that trait and is the public production parser. The
generated machinery remains crate-private proof support:

- `parser.rs` is regenerated proof scaffolding;
- `soundness.rs` contains the independently maintained fast parser boundary and discharges the
  generated contract.

`DecimalPrinter::to_string(value: i64) -> String` is the corresponding verified production
serializer. It matches Cedar Rust's Decimal rendering: an optional minus sign, the minimal
integral digits, a decimal point, and exactly four fractional digits. Its executable postcondition
ties the returned string to the generated Decimal specification and proves that parsing it returns
the original value, including `i64::MIN`.

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
directions of the readable grammar contract. The semantic certificate proves
`decimal_semantic_parse_plan(input).is_some() <==> decimal_is_valid(input)`. Finally,
`DecimalParser` implements the generated external-parser contract, tying its executable
`Option<i64>` result to the unique valid Triptych view. Verus checks the complete artifact with
`--no-cheating`.

## Evidence

`grammar-coverage/` is generated from one declaration that combines every shared grammar
constructor: Unicode literals, quoted strings, all token classes and length forms, references,
alternatives, optionals, bounded and unbounded repetition, nested named repetition, and an
ambiguous token alternative. Its Verus and Rust tests exercise accepted and rejected inputs.

`cedar-ext/{decimal,duration,datetime,ipaddr}/` contain:

- generated Verus specifications and external-parser contracts;
- specialized allocation-free Rust parsers;
- parser-local Verus proofs, including calendar arithmetic and IPv6 compression/overflow;
- deterministic differential regressions against Cedar's production parsers;
- alternating-round release benchmark harnesses using Cedar's benchmark-only parser entry points.

After replacing the old Cedar-specific templates, all four handwritten parser families fully
verify against the actual Triptych-generated specifications. The current `--no-cheating` results
are Decimal `56/0`, Duration `118/0`, Datetime `122/0`, and combined IPv4/IPv6 `323/0`.
The printer-enabled formats also discharge the generated external serializer obligations;
Datetime intentionally has parser contracts only because its DSL declaration has no printer.
`verify.sh` checks the generator, generated runtime, grammar coverage, every extension proof, and
every differential Rust regression suite.

The benchmarks report the median of seven alternating rounds. Decimal uses five million
iterations per round; the other formats use two million.

| format and representative input | optimized ns/parse | Cedar ns/parse | speedup |
| --- | ---: | ---: | ---: |
| Decimal `-1234567890.1234` | 20.27 | 90.91 | 4.49× |
| Duration `-12d23h59m59s999ms` | 17.70 | 260.77 | 14.73× |
| Datetime `2024-01-15T10:30:45.123-0800` | 16.68 | 289.38 | 17.35× |
| IPAddr `2001:db8:85a3::8a2e:370:7334/64` | 72.54 | 94.84 | 1.31× |

Each pair parses the same input and consumes the complete returned value in the benchmark
checksum. The optimized paths include recognition, semantic computation, range checking, and
domain conversion. These are wall-clock measurements from one development machine, not formal
timing guarantees; a benchmark row is not itself evidence that the current generated external
contract has been discharged.

Full provenance, source links, raw rounds, environment data, and Cedar's benchmark-adapter patch
are stored in [`benchmark-results/`](benchmark-results/README.md).

## Commands

From the repository root:

```sh
./verus-experiments/setup-verus.sh
lake build Triptych.Backend.VerusTests Triptych.Architecture.ScanPlanTests \
  Triptych.Backend.Verus.RuntimeModelTests
lake env lean verus-experiments/grammar-coverage/Input.lean
(cd cedar-examples && lake build \
  Inputs.Decimal Inputs.Duration Inputs.Datetime Inputs.IPv4 Inputs.IPv6)
./verus-experiments/verify.sh
cargo test --manifest-path verus-experiments/grammar-coverage/Cargo.toml --offline --locked
for extension in decimal duration datetime ipaddr; do
  cargo test --manifest-path "verus-experiments/cedar-ext/${extension}/Cargo.toml" \
    --offline --locked
done
./verus-experiments/benchmark-cedar-extensions.sh
```

The setup script pins Verus `0.2026.08.30.b432e82` and its required Rust toolchain.
