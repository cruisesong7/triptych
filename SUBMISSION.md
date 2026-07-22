# FormatSpec: grammar-to-specification compiler for verifying format parsers

## Submission Details

**Links**

- **Hack Portal idea:** [link]
- **Demo video:** [link]
- **Other artifacts:** code: https://github.com/cruisesong7/formatspec (Lean 4; builds with `lake build FormatSpec`)

**Award categories (select up to 2):**

- [x] Tools
- [x] Operational Excellence

## Team

| Name | Alias | Role |
| --- | --- | --- |
| Cruise Song | @crusong | AS intern |

## High-Level Description

Every string format a service accepts — decimals, datetimes, IP addresses, policy syntax — has a parser, and a parser bug is a correctness or security bug. The gold standard is a machine-checked proof that the parser matches its specification, but today that means hundreds of lines of bespoke Lean proof per format: Cedar hand-wrote exactly this for each of its extension types.

FormatSpec makes that artifact free. You write one declarative block — an EBNF-style grammar, plus optional value and constraint sections — and the tool generates a readable specification, an executable verified parser, and the machine-checked proofs that they agree, plus the exact proof obligations needed to validate an existing hand-written parser (like Cedar's) against the spec.

Impact: anyone maintaining a string-format parser (policy languages, config formats, identity tokens, network addresses) gets a citable formal spec and a correct-by-construction parser for the cost of writing EBNF.

## Solution

One `format_spec` block in, three generated files out:

- **`spec.lean` — cite.** Each grammar production becomes a readable predicate you can eyeball against the grammar. Proof-free.
- **`parser.lean` — run + trust.** An executable engine, a generated verified parser `parse` with auto-discharged soundness/completeness/rejection theorems, and machine-checked proofs that spec and engine agree on both *recognition* and *value*. Zero `sorry`, standard axioms only.
- **`soundness.lean` — the obligation surface.** Emitted only when you point the spec at a real external parser/printer: the handful of `sorry`'d theorems a human must prove. We point Decimal, Duration, and Datetime at Cedar's actual parsers, and derive Cedar's printer theorems — roundtrip, injectivity, normalization — automatically from two encode obligations.

Working today: six formats (Decimal, Duration, Datetime, IPv4, IPv6, Graph); the generated theorem set matches, one-to-one, what Cedar proves by hand for its extension types.

## Architecture / How It Works

A four-stage compiler pipeline, implemented as a Lean metaprogram:

1. **DSL → data.** Lean's parser (extended via `syntax` rules) reads the `format_spec` block; an elaborator lowers it to a first-order `Grammar` datatype — a closed, inspectable AST. Because the grammar is *data*, not code, the tool can analyze it.
2. **Two interpretations of one AST.** From the same `Grammar` value we derive a *denotation* (a logical predicate: what strings mean) and an executable *decoder* (a recognizer that extracts named captures).
3. **One generic proof.** The hard theorem — the decoder recognizes exactly the denoted language — is proved once, for the whole grammar class, in the library (~660 lines of mutual induction). Every format reuses it.
4. **Total generation.** Per format, the metaprogram *emits* the readable spec and its equivalence proofs as Lean source, checked by the kernel. The grammar class (flat-regular: no recursion, no data-dependent length) is restricted precisely so this emission is a fixed recipe — never proof search, never stuck.

Scope is layered: the grammar tier is a strict subclass of regular; a constraint tier lifts the *accepted* language to any decidable predicate (checksums, calendar rules, triangular lengths); a value tier produces any type (scalars or structured values — our Graph example parses SAT adjacency bit-strings into actual graph records). Anything inexpressible degrades gracefully to a typed, `sorry`'d obligation rather than a wall.

## How We Used AI

Built pair-programming with Claude Code end-to-end: the DSL/elaborator design, the generic roundtrip proof, the file-split architecture, and the alignment of generated obligations against Cedar's hand-written theorems (Claude diffed our generated statements against `Cedar.Thm.Ext.*` and caught semantic mismatches — e.g. our `complete` was existential where Cedar's is target-parametrized, and our printer theorems initially targeted the wrong parser). What worked: proof prototyping in scratch files before wiring emitters; adversarial comparison against prior art.

## What's Next

- **rep-element capture exposure** — let structured values address individual repeated elements; unlocks a DIMACS CNF example with real header-vs-body cross-constraints (prior verified DIMACS parsers — CakeML, Isabelle — are bespoke; ours would be generated).
- **Layout inverse (`asString`)** — auto-derive the default printer from the grammar, shrinking the printer obligations further.
- **Discharge the Cedar obligations** — prove the 13 generated `sorry`s against Cedar's real parsers, making this a drop-in validation layer for cedar-lean.
- Lessons: restricting the input class is what makes generation *total*; the right place for every unprovable fact is a small, typed, named obligation.
