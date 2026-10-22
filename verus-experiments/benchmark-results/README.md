# Cedar extension parser benchmark report

The latest complete four-parser console record is [`latest.txt`](latest.txt). The fresh
handwritten Decimal-parser run is recorded separately in
[`decimal-optimized-2026-09-24.txt`](decimal-optimized-2026-09-24.txt). Running
`../benchmark-cedar-extensions.sh` overwrites `latest.txt` with provenance and all seven timing
samples for every parser.

## What is being compared

Each benchmark first asserts that the specialized parser and Cedar return the same complete value,
then measures the two functions on one representative valid input. These timed inputs are selected
in the benchmark harnesses; they are not sampled from Cedar's entire test suite.

| Format | Timed input | Harness | Optimized parser | Cedar production parser |
| --- | --- | --- | --- | --- |
| Decimal | `-1234567890.1234` | [`decimal/benches/runtime.rs`](../cedar-ext/decimal/benches/runtime.rs) | [`DecimalParser::parse`](../cedar-ext/decimal/src/optimized.rs) | [`Decimal::from_str`](../../../cedar/cedar-policy-core/src/extensions/decimal.rs) |
| Duration | `-12d23h59m59s999ms` | [`duration/benches/runtime.rs`](../cedar-ext/duration/benches/runtime.rs) | [`DurationParser::parse`](../cedar-ext/duration/src/optimized.rs) | [`parse_duration`](../../../cedar/cedar-policy-core/src/extensions/datetime.rs) |
| Datetime | `2024-01-15T10:30:45.123-0800` | [`datetime/benches/runtime.rs`](../cedar-ext/datetime/benches/runtime.rs) | [`DatetimeParser::parse`](../cedar-ext/datetime/src/optimized.rs) | [`parse_datetime`](../../../cedar/cedar-policy-core/src/extensions/datetime.rs) |
| IPAddr | `2001:db8:85a3::8a2e:370:7334/64` | [`ipaddr/benches/runtime.rs`](../cedar-ext/ipaddr/benches/runtime.rs) | [`IpAddrParser::parse`](../cedar-ext/ipaddr/src/optimized.rs) | [`IPAddr::from_str`](../../../cedar/cedar-policy-core/src/extensions/ipaddr.rs) |

Cedar's private parsers are exposed by tiny feature-gated adapters which only map their successful
results to benchmark values. The exact local Cedar patch is stored in
[`cedar-benchmark-adapter.patch`](cedar-benchmark-adapter.patch).

## Test-case provenance

Correctness is tested separately from timing:

- Decimal's regression corpus is copied from Cedar's `decimal_creation` unit test:
  [`cedar_runtime.rs`](../cedar-ext/decimal/tests/cedar_runtime.rs) and
  [`decimal.rs`](../../../cedar/cedar-policy-core/src/extensions/decimal.rs). It is supplemented
  by more than 130,000 structured and deterministic-fuzz comparisons in
  [`generated_parser.rs`](../cedar-ext/decimal/tests/generated_parser.rs).
- Duration cases are adapted from Cedar's `parse_duration_pos`/`parse_duration_neg` tests and
  supplemented by a generated quantity/unit grid:
  [`regression.rs`](../cedar-ext/duration/tests/regression.rs).
- Datetime cases are adapted from Cedar's positive/negative parser tests and supplemented by a
  2,700-case calendar/layout grid:
  [`regression.rs`](../cedar-ext/datetime/tests/regression.rs).
- IPAddr covers IPv4/IPv6/CIDR examples, malformed forms, generated IPv4 boundaries, and compressed
  IPv6 layouts:
  [`regression.rs`](../cedar-ext/ipaddr/tests/regression.rs).

Every regression compares the specialized result with Cedar's production parser result.

## Current formal-verification status

The template-free generated layer is in place for all four extension families. The latest
`--no-cheating` checks have this boundary status:

| Parser | Current result | Remaining boundary |
| --- | --- | --- |
| Decimal | 56 verified, 0 errors | complete |
| Duration | 118 verified, 0 errors | complete |
| Datetime | 122 verified, 0 errors | complete (parser-only DSL declaration) |
| IPAddr | 323 verified, 0 errors | complete for generated IPv4 and IPv6 contracts |

The Rust regression suites pass for all four optimized parsers against Cedar's production
parsers. That differential evidence is separate from the completed Verus refinement proofs
listed above.

The common generated external-parser contract requires:

- `extparse_sound`: every accepted Rust result is valid and has exactly the denotation returned by
  the generated specification.
- `extparse_complete`: every input accepted by the generated specification is accepted by the Rust
  parser with the same value.
- `extparse_reject`: the Rust parser rejects exactly the inputs that are invalid in the generated
  specification.

### Decimal

The proof connects the handwritten public parser in
[`decimal/src/optimized.rs`](../cedar-ext/decimal/src/optimized.rs), through the generated
contract implementation in [`decimal/src/soundness.rs`](../cedar-ext/decimal/src/soundness.rs),
to the generated grammar and semantic plan in
[`decimal/src/spec.rs`](../cedar-ext/decimal/src/spec.rs) and
[`decimal/src/parser.rs`](../cedar-ext/decimal/src/parser.rs). It verifies:

- the optional sign, required natural digits, decimal point, and one-to-four fractional digits;
- exact capture/view reconstruction and uniqueness;
- exact scale-to-four-decimal-place `i64` denotation;
- arbitrary leading zeros without accumulator overflow;
- exact positive and negative `i64` boundaries, including `i64::MIN`;
- acceptance, completeness, and rejection equivalence.

Decimal also has generated contracts for the Cedar-compatible `toString` implementation:

- `extparse_to_string_roundtrip`;
- `extparse_to_string_injective`;
- `extparse_normalize_eq_iff_parse_eq`.

These prove parse/print round trips, injectivity on representable Decimal values, and equality of
normalized strings exactly when parsed values are equal.

The same three serializer contracts are generated and discharged for Duration, IPv4, and IPv6.
Datetime intentionally has no generated serializer contract because its Triptych declaration does
not contain a `printer` clause.

### Duration

The proof connects [`duration/src/optimized.rs`](../cedar-ext/duration/src/optimized.rs) to
[`duration/src/spec.rs`](../cedar-ext/duration/src/spec.rs) through
[`duration/src/contract.rs`](../cedar-ext/duration/src/contract.rs). Its parser-local model
establishes:

- ASCII input and optional leading minus handling;
- nonempty decimal quantities;
- ordered, nonrepeated `d`, `h`, `m`, `s`, and `ms` units;
- exact millisecond multipliers and accumulated value;
- absence of machine-integer overflow;
- exact `i64` bounds, including the negative minimum edge;
- every loop state and rejection branch against the recursive generated specification.

### Datetime

The proof connects [`datetime/src/optimized.rs`](../cedar-ext/datetime/src/optimized.rs) to
[`datetime/src/spec.rs`](../cedar-ext/datetime/src/spec.rs) through
[`datetime/src/contract.rs`](../cedar-ext/datetime/src/contract.rs). Its parser-local model
establishes:

- every supported fixed-width date/time, millisecond, `Z`, and numeric-offset layout;
- digit widths, separators, and time/offset field ranges;
- Gregorian leap-year and month/day validity;
- the executable civil-date conversion against its mathematical specification;
- exact epoch-millisecond and timezone-offset semantics;
- bounds for all arithmetic and casts;
- every accepted or rejected result against the generated specification.

### IPAddr

The proof connects [`ipaddr/src/optimized.rs`](../cedar-ext/ipaddr/src/optimized.rs) to the
separately generated IPv4 and IPv6 specifications and contracts under
[`ipaddr/src/ipv4`](../cedar-ext/ipaddr/src/ipv4) and
[`ipaddr/src/ipv6`](../cedar-ext/ipaddr/src/ipv6). Its parser-local model establishes:

- family classification, slash handling, maximum length, and rejection of mixed IPv4/IPv6 syntax;
- canonical CIDR syntax and the IPv4/IPv6 prefix ranges;
- exactly four canonical IPv4 octets, each in `0..=255`, and exact `u32` assembly;
- IPv6 hexadecimal semantics, uncompressed eight-group form, and exactly one valid `::`
  compression site;
- exact omitted-group insertion and `u128` address assembly;
- accumulator, shift, and arithmetic bounds;
- exact family, address, and default/explicit prefix values;
- every partial parser state and rejection branch against the recursive generated specification.

### Verification boundary

Each optimized Rust parser now refines its generated Verus specification end to end. The
regression suite separately compares all optimized results with Cedar Rust's production parser on
the recorded corpus. It does **not** formally prove Cedar Rust's implementation correct, formally
prove the measured speedup, or prove the Verus generator itself.

Run the complete proof suite with [`verify.sh`](../verify.sh):

```sh
./verus-experiments/verify.sh
```

## Methodology

- Cargo optimized `bench` profile, no Criterion statistical model.
- Seven rounds per implementation with alternating execution order.
- Decimal: 5,000,000 parses per round; others: 2,000,000.
- Input and complete returned values pass through `std::hint::black_box`.
- The benchmark asserts equal parser results and equal per-round output checksums.
- `std::time::Instant` measures wall-clock elapsed time.
- Median is reported with minimum/maximum and all raw round samples.
- No separate warm-up run; the first measured round is retained.
- No CPU affinity, frequency locking, or thermal normalization is applied.

## Run of 2026-09-24

- Triptych commit: `3ad9646b2a679500823656b02ad8bca7b838e06e`, dirty worktree containing this implementation.
- Cedar commit: `92b97a45c091bb285b997664bf14bfffd8c402cc`, plus the stored benchmark adapter patch.
- Host: MacBook Pro `Mac15,7`, Apple M3 Pro, 12 cores, 36 GB memory.
- OS: macOS 26.6.2, Darwin 25.6.0, arm64.
- Rust: `rustc 1.95.0 (59807616e 2026-04-14)`.

The Decimal row and raw samples below were refreshed after replacing its generated executable
path with the handwritten parser; its exact provenance is in
[`decimal-optimized-2026-09-24.txt`](decimal-optimized-2026-09-24.txt). The other three rows remain
from the complete four-parser run in `latest.txt`.

| Format | Verified median (range) | Cedar median (range) | Cedar/verified |
| --- | ---: | ---: | ---: |
| Decimal | 20.78 ns (20.70–22.35) | 94.75 ns (89.38–99.22) | 4.56× |
| Duration | 17.70 ns (17.65–29.72) | 260.77 ns (256.17–265.76) | 14.73× |
| Datetime | 16.68 ns (16.63–28.80) | 289.38 ns (287.34–319.30) | 17.35× |
| IPAddr | 72.54 ns (70.96–81.95) | 94.84 ns (93.91–99.52) | 1.31× |

Raw ns/parse rounds:

| Format | Verified rounds | Cedar rounds |
| --- | --- | --- |
| Decimal | 22.35, 20.78, 21.29, 20.78, 20.72, 20.74, 20.70 | 89.38, 97.28, 99.22, 96.35, 94.75, 93.29, 91.89 |
| Duration | 29.72, 17.66, 17.66, 17.70, 17.80, 17.65, 18.07 | 263.78, 259.03, 265.76, 263.06, 258.55, 256.17, 260.77 |
| Datetime | 28.80, 16.93, 16.64, 16.68, 16.63, 16.76, 16.65 | 298.01, 287.34, 288.35, 288.57, 289.38, 319.30, 314.93 |
| IPAddr | 81.95, 72.54, 72.67, 73.72, 70.96, 71.60, 71.09 | 94.84, 93.91, 97.16, 94.12, 99.52, 94.50, 98.59 |

Regenerate and overwrite `latest.txt` with:

```sh
./verus-experiments/benchmark-cedar-extensions.sh
```
