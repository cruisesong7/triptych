# FormatSpec

A Lean 4 library for **specifying and verifying flat, non-recursive string-format
parsers** — the "verified textual scalar/record parsing" niche.

Given a `format_spec` DSL block (a grammar, plus optional value / constraint sections),
it generates up to three files, split by audience:

* **`spec.lean` — a readable surface specification** — inlined per-production well-formedness
  predicates (`IsWf.*`), a `value` function, and the `IsValid` acceptance predicate,
  reading like a hand-written spec. Proof-free (what you *cite*);
* **`parser.lean` — the runnable, verified artifact** — the analyzable deep-embedded engine
  (total capture-extracting `decode`, decidable `isValid`, `computeValue`); the **generated
  correct-by-construction parser** `parse` (= `computeValue` gated on the decidable `isValid`)
  with its **auto-discharged** contracts `parse_sound`/`parse_complete`/`parse_reject`; and the
  machine-checked, axiom-clean surface⟺engine reconciliation on **both recognition and value**
  — `IsWf_equiv` (via the `decode ↔ IsWf` roundtrip) and `computeValue_eq`. No `sorry` (what
  you *run + trust*);
* **`soundness.lean` — the obligation surface** — emitted *only* when a `parser … projection …`
  clause names an existing external parser: the `sorry`'d `sound`/`complete`/`reject` relating
  that hand-written parser to the spec. The one seam with no formal oracle (real-world-format
  conformance is inherently trusted); the *only* proofs left to the human.

Every generated proof outside `soundness.lean` depends only on the standard axioms
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
section additionally gets the verified parser `<Name>.parse : String → Option α` (with its
auto-discharged `parse_sound`/`parse_complete`/`parse_reject`) and the reconciliation theorem
`<Name>.computeValue_eq` (see Decimal, Duration, Datetime, Graph). Adding a
`parser <p> projection <π>` clause emits `soundness.lean` with the `sorry`'d obligations for an
external parser — Decimal points it at the real `Cedar.Spec.Ext.Decimal.parse`.

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

Lean `v4.31.0`, batteries only (no Mathlib). The Decimal example additionally depends on
cedar-lean (via a local `require Cedar from "../cedar-spec/cedar-lean"` — same toolchain, same
batteries commit) so its `soundness.lean` can state obligations against the real
`Cedar.Spec.Ext.Decimal.parse`. Clone `cedar-spec` beside this repo, or drop the Decimal
`parser` clause to build without it.

## Provenance

Originated while verifying the Cedar extension-type parsers (Decimal, Duration,
Datetime, IPAddr); extracted into a standalone library that now takes a light optional
dependency back on cedar-lean for the Decimal external-parser example. Source files retain
their original Apache-2.0 "Cedar Contributors" headers.
