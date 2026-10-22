# Vest Decimal experiment

This experiment evaluates Vest 0.2.1 as a direct implementation path for Triptych's Decimal
grammar:

```text
Decimal  ::= Sign Natural "." Fraction
Sign     ::= "-"
Natural  ::= digit+
Fraction ::= digit{1,4}
```

## Exact grammar

`decimal.vest` expresses the full accepted language. The 1-4 digit fraction uses four alternatives
that reparse the remaining input at an exact length. Vest generates `src/decimal.rs`, including
Rust value types, an executable parser and serializer, specifications, and proof implementations.

```sh
vest decimal.vest -o src/decimal.rs
cargo test --locked
```

All executable acceptance, rejection, and serializer round-trip tests pass. Verification of this
generated file does not currently pass. Vest emits proof implementations requiring serializer
traits that `Tail >>= [digit; N]` does not provide. Simpler encodings also exposed unresolved
unambiguity obligations for delimiter-terminated `Vec<digit>` and optional fields.

Two frontend details also affected the transcription:

- A named format ending in `Vec<digit>` consumes to end-of-input and cannot be reused before `.`.
- Naming a field `rest` collides with Vest's generated parser cursor.

## Verified control

`verified-fixed4/` removes the variable-width boundaries and recognizes exactly two natural digits
and four fractional digits. It is not the Triptych language; it is a control showing that the
toolchain and basic Vest pipeline work.

```sh
cd verified-fixed4
vest decimal.vest -o src/decimal.rs
cargo test --offline
cargo verus verify --offline --target-dir /tmp/vest-fixed4-strict \
  --fwd-verus-args-to roots -- --no-cheating
```

The tests pass, and Verus reports 52 verified obligations with no errors.

## Semantic value

Both generated parsers return structural digit values. Vest's DSL does not express Triptych's
conversion to the scaled `Int64` Decimal value or its range constraint. Doing so requires a custom
`vest_lib` mapping and format-specific Verus proofs.

## Performance sample

`src/bin/bench.rs` compares the exact generated executable with a small hand-written scanner:

```sh
cargo run --release --offline --bin bench
```

On the development machine, the sample produced approximately 157 ns per Vest parse and 47 ns per
hand-written parse. This is only a directional microbenchmark, but it supports measuring generated
text parsers rather than assuming binary-format performance transfers unchanged.

## Takeaway

Vest is immediately useful for fixed-width and explicitly length-delimited formats. The exact
Triptych Decimal grammar is not currently push-button in the Vest DSL because textual
delimiter-terminated repetition, bounded suffixes, and semantic conversion require lower-level
work.

A Triptych Verus backend therefore still has motivation, but it should reuse Vest where practical
instead of rebuilding Vest's verified combinator foundation. The useful contribution is a
Triptych-aware text lowering: specialized scanner code, generated semantic mappings and
constraints, and proof adapters to Vest or Verus.
