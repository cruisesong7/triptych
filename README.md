# FormatSpec

A Lean 4 library for **specifying and verifying flat, non-recursive string-format
parsers** — the "verified textual scalar/record parsing" niche.

Given a `format_spec` DSL block (a grammar, plus optional value / constraint sections),
it generates:

* a **readable surface specification** — inlined per-production well-formedness
  predicates (`IsWf.*`), a `value` function, and the `IsValid` acceptance predicate,
  reading like a hand-written spec;
* an **analyzable/executable engine** — a deep-embedded grammar interpreter with a total
  capture-extracting `decode`, and a decidable validator;
* **machine-checked reconciliation** — auto-emitted, axiom-clean proofs that the readable
  surface spec and the engine agree, on **both recognition and value**: `IsWf_equiv`
  (recognition, via the `decode ↔ IsWf` roundtrip) and `computeValue_eq` (the extracted
  value equals the readable `value` on the decoded captures). Plus `sorry`'d contract
  obligations tying an external hand-written parser to the spec — the one seam that has no
  formal oracle (conformance to the real-world format is inherently trusted).

All generated equivalence/decidability results depend only on the standard axioms
`propext, Classical.choice, Quot.sound` — no `sorry`, `native_decide`, or extra axioms.

## Example

```lean
format_spec IPv6 where
  grammar
    V6Addr ::= rep H16 sepBy ":" {8}     -- eight H16 groups joined by ":"
    H16    ::= hexDigit{1,4}
  to "FormatSpec/Examples/IPv6"
```

produces `IPv6.IsWf.V6Addr`, `IPv6.IsValid`, a `DecidablePred` validator, and
`IPv6.IsWf_equiv : ∀ s, IsWf IPv6.grammar s ↔ IPv6.IsWf.V6Addr s`. A spec with a value
section additionally gets `<Name>.computeValue` and its reconciliation theorem
`<Name>.computeValue_eq` (see Decimal, Duration, Datetime, Graph).

See `FormatSpec/DESIGN.md` for the full design, and `FormatSpec/Examples/` for worked
examples (Decimal, Duration, Datetime, IPv4, IPv6, Graph).

## Scope

* **Grammar tier:** a strict subclass of regular — concatenation, finite alternation,
  optional items, character-class token runs (`digit`/`hexDigit`/`bit` with length
  bounds), and separated group repetition (`rep … sepBy`). No recursion (not
  context-free); no data-dependent length.
* **Constraint tier:** grammar ∩ any decidable predicate over the captures (so the
  *accepted* language can be non-regular, e.g. "length is a triangular number").
* **Value tier:** any type (via the `value'` escape) — structured output (graphs,
  records), not just `Int`.

Full automation (grammar reconciliation + decidability + value contract auto-discharged)
covers flat-regular grammars with an `Int`-arithmetic value and comparison/cardinality
constraints. Structured values and non-arithmetic constraints use escapes (grammar and
decidability still auto-proven; value/constraint contract left as a typed hole).

## Build

```
lake build FormatSpec
```

Lean `v4.31.0`, batteries only (no Mathlib).

## Provenance

Originated while verifying the Cedar extension-type parsers (Decimal, Duration,
Datetime, IPAddr); extracted into a standalone repository. Source files retain their
original Apache-2.0 "Cedar Contributors" headers.
