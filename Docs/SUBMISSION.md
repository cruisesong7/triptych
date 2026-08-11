# Triptych: grammar-to-specification compiler for verifying format parsers

## Submission Details

**Links**

- **Hack Portal idea:** [link]
- **Demo video:** [link]
- **Other artifacts:** code: https://github.com/cruisesong7/triptych (Lean 4; Cedar-free core
  builds with `lake build`; optional packages live in `other-examples/` and `cedar-examples/`)

**Award categories (select up to 2):**

- [x] Tools
- [x] Operational Excellence

## Team

| Name | Alias | Role |
| --- | --- | --- |
| Cruise Song | @crusong | AS intern |

## High-Level Description

Every string format a service accepts — decimals, datetimes, IP addresses, policy syntax — has a parser, and a parser bug is a correctness or security bug. The gold standard is a machine-checked proof that the parser matches its specification, but today that means hundreds of lines of bespoke Lean proof per format: Cedar hand-wrote exactly this for each of its extension types.

Triptych makes that artifact free. You write one declarative block — an EBNF-style grammar, plus optional value and constraint sections — and the tool generates a readable specification, an executable verified parser, and the machine-checked proofs that they agree, plus the exact proof obligations needed to validate an existing hand-written parser (like Cedar's) against the spec.

Impact: anyone maintaining a string-format parser (policy languages, config formats, identity tokens, network addresses) gets a citable formal spec and a correct-by-construction parser for the cost of writing EBNF.

## Solution

One `triptych` block in, three generated files out:

- **`spec.lean` — cite.** Each grammar production becomes a readable predicate and a typed
  derivation tree with `render`/`Valid`. Alternatives, optionals, and repetitions appear as
  constructors, `Option`, and `List`. Proof-free.
- **`parser.lean` — run + trust.** An executable engine, a generated verified parser `parse` with auto-discharged soundness/completeness/rejection theorems, and machine-checked proofs that spec and engine agree on both *recognition* and *value*. Declared external parsers also receive `checkedExtParse`, a sound wrapper that validates every result against the generated parser without trusting the external implementation. Zero `sorry`, standard axioms only.
  Generated structural trees additionally have exact capture construction, full-parse
  membership, decode roundtrip whenever capture functionality is certified, and an exact
  projection to the flat value/constraint view.
- **`soundness.lean` — the static obligation surface.** Emitted for a declared external parser or
  printer. External contracts remove runtime checking and prove full agreement of the original
  parser. A printer contributes one typed `encode_view` witness; generated-parser roundtrip,
  injectivity, normalization, and the external parser's corresponding theorems are derived from
  it. The witness can now be discharged by constructing a valid root derivation; when a semantic
  right inverse is available, `DerivationPrinter` packages it as a verified serializer.
  `printer auto` synthesizes that certificate for the first total signed-decimal fragment.
  Both multiplication orders of the sign and natural magnitude are recognized.

Working today: six formats (Decimal, Duration, Datetime, IPv4, IPv6, Graph). Graph is the
Cedar-free structured-value example; the Cedar-facing examples exercise the theorem surfaces
needed to match Cedar's hand-written extension parsers. All five Cedar soundness modules
discharge their generated obligations, and the differential conformance target reports zero
failures.

## Architecture / How It Works

A four-stage compiler pipeline, implemented as a Lean metaprogram:

1. **DSL → data.** Lean's parser (extended via `syntax` rules) reads the `triptych` block; an elaborator lowers it to a first-order `Grammar` datatype — a closed, inspectable AST. Because the grammar is *data*, not code, the tool can analyze it.
2. **Two interpretations of one AST.** From the same `Grammar` value we derive a *denotation* (a logical predicate: what strings mean) and an executable *decoder* (a recognizer that extracts named captures).
3. **One generic proof.** The hard theorem — the decoder recognizes exactly the denoted language — is proved once, for the whole grammar class, in the library (~660 lines of mutual induction). Every format reuses it.
4. **Total generation.** Per format, the metaprogram *emits* the readable spec and its equivalence proofs as Lean source, checked by the kernel. The grammar class (flat-regular: no recursion, no data-dependent length) is restricted precisely so this emission is a fixed recipe — never proof search, never stuck.

Scope is layered: the grammar tier is a strict subclass of regular; a constraint tier lifts the *accepted* language to any decidable predicate (checksums, calendar rules, triangular lengths); a value tier produces any type (scalars or structured values — our Graph example parses SAT adjacency bit-strings into actual graph records). Semantics outside the small analyzable AST use typed `value'`/`constraints'` functions; `[X]` passes all spans of a repeated capture to either escape as `List String`, while recognition, decidability, typed views, and value/constraint reconciliation remain generated. Only claims about an independent external parser or a chosen canonical serializer become user proof obligations.

## How We Used AI

Built pair-programming with Claude Code end-to-end: the DSL/elaborator design, the generic roundtrip proof, the file-split architecture, and the alignment of generated obligations against Cedar's hand-written theorems (Claude diffed our generated statements against `Cedar.Thm.Ext.*` and caught semantic mismatches — e.g. our `complete` was existential where Cedar's is target-parametrized, and our printer theorems initially targeted the wrong parser). What worked: proof prototyping in scratch files before wiring emitters; adversarial comparison against prior art.

## What's Next

- **Reusable semantics and bridges** — specify common signs, bounded integers, separators, and
  external-parser combinators once; improve diagnostics when proof automation stops.
- **Broader printer synthesis** — extend `printer auto` beyond the total signed-decimal pattern
  to constrained values, conversions, and named canonicalization policies.
- **Collection-aware semantics** — build beyond completed `count X` and list-aware
  `value'`/`constraints'` support with analyzable `sum` and per-element predicates.
- **Compiler quality** — broaden static capture-functionality certificates and deterministic
  execution paths; package CI, structural cost budgets, and a benchmark smoke target are present.
- **Then add examples** — UUIDv4/v7 first, followed by DIMACS CNF. See `ROADMAP.md` for the
  current phase ordering.
- Lessons: restricting the input class is what makes generation *total*; the right place for every unprovable fact is a small, typed, named obligation.
