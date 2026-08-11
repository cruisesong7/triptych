# Triptych

```
   +--------+  +--------+  +--------+
   |        |  |  /##\  |  |        |
   | # # #  |  | ###### |  | # # #  |
   |  # # # |  | ###### |  |  # # # |
   | # # #  |  | ###### |  | # # #  |
   |        |  |  \##/  |  |        |
   +--------+  +--------+  +--------+
     parser       spec      soundness

         T R I P T Y C H
       one grammar, three panels
```

A Lean 4 library for **specifying and verifying flat, non-recursive string-format
parsers** — the "verified textual scalar/record parsing" niche.

Given a `triptych` DSL block (a grammar, plus optional value / constraint sections),
it generates up to three files, split by audience:

Capture names follow Lean identifier rules. Keyword-shaped names must be escaped everywhere
(`«bit»`); Triptych preserves that semantic capture name and quotes generated Lean identifiers.
Distinct captures that normalize to the same public surface binder are rejected with a
source-located diagnostic rather than silently renamed.

* **`spec.lean` — a readable surface specification** — inlined per-production well-formedness
  predicates (`IsWf.*`), a `value` function, and the `IsValid` acceptance predicate,
  reading like a hand-written spec. Empty constraint phases are omitted: without
  capture constraints `IsWf` aliases the start-production predicate, and without value
  constraints `IsValid` aliases `IsWf`. It also contains typed
  `<Name>.Derivation.<Production>` trees with `render` and `Valid`: alternatives are
  constructors, optional symbols are `Option`, and repetitions are `List`. Proof-free
  (what you *cite*);
* **`parser.lean` — the runnable, verified artifact** — the analyzable deep-embedded engine
  (total capture-extracting `decode`, decidable `isValid`, `computeValue`); the **generated
  correct-by-construction parser** `parse` (= `computeValue` gated on the decidable `isValid`)
  with its **auto-discharged** contracts `parse_sound`/`parse_complete`/`parse_reject`; and the
  machine-checked, axiom-clean surface⟺engine reconciliation on **both recognition and value**
  — `IsWf_equiv` (via the `decode ↔ IsWf` roundtrip) and `computeValue_eq`. It also emits a
  typed `<Name>.View` containing the exact input plus the captures used by values and
  constraints (`String` when always present, `Option String` when grammar-optional, and
  `List String` when repeated). `decodeView_input`, `IsValid_view`, and `computeValue_view`
  let bridge proofs reason over named fields instead of `CaptureMap` plumbing. `parse_view`
  gives the executable validation/denotation equation, while `parse_eq_some_iff_view` and
  `parse_eq_none_iff_view` give its guard-free success and rejection relations. For declared
  external parsers, `checkedExtParse` validates every external success against the generated
  parser. Its exact success, soundness, and typed-view theorems are auto-discharged without
  trusting the external implementation. Once static external-parser soundness is proved,
  `checkedExternalParse_eq_of_sound` shows that checking does not change its behavior. The
  wrapper is emitted when the spec value type has `DecidableEq`; otherwise Triptych leaves the
  static integration unchanged and reports a source-located warning. The
  structural trees additionally receive exact `capturesWith` functions and generated proofs
  that every valid tree belongs to `fullParses`. `decode_render_of_captureFunctional` proves
  exact decode roundtrip under the grammar's capture-functionality contract; statically
  certified grammars also receive premise-free `decode_render`. The root additionally projects
  to the flat value/constraint view through `toView`, with matching
  `decodeView_render_of_captureFunctional` and, when certified, `decodeView_render`.
  The static automation layer uses two extensible registries: `triptych_parser` for terminating
  normalization and `triptych_parser_search` for bounded E-matching. `triptych_sound` exposes
  successful `Option` paths; `triptych_auto [rules...]` combines user agreement facts with those
  registries and `grind` to discharge routine soundness, completeness, and typed-view
  consequences. `triptych_encode [roundtrip, agreement, IsValid_view, computeValue_view]`
  deterministically builds identity-denotation printer witnesses; a fifth argument supplies an
  explicit conversion inverse. `triptych_encode_direct` starts from generated-spec acceptance and
  value proofs instead, so it has no external-parser dependency.
  `triptych_encode_derivation [decodeView_render, encodeDerivation]` uses a structural tree
  witness instead, eliminating decoder and capture-map bookkeeping. Unsupported primitives and
  missing format semantics remain explicit.
  The discharged `extparse_eq_some_iff_view` and `extparse_eq_none_iff_view` package the
  stronger static external obligations in the same form. No `sorry` (what you *run + trust*);
* **`soundness.lean` — the obligation surface** — emitted *only* when a `parser <p>`
  or explicit `printer <toString>` clause is present: scaffold placeholders requiring proof that
  a *user-supplied* external parser (`extparse_sound`/`_complete`/`_reject`) agrees with the spec,
  or that a value serializer produces a valid typed view (`encode_view`) — plus the printer theorems
  (`parse_toString_roundtrip`/`toString_injective`/`normalize_eq_iff_parse_eq`) auto-derived
  from that view witness. `encode_accepted` and `encode_value` remain as derived compatibility
  theorems for external-parser completeness. With both `ofSpec` and `toSpec`, one more obligation
  guards the conversion: `toSpec_ofSpec`
  (`toSpec (ofSpec v) = v` *on accepted values* — provable exactly when the constraints pin
  accepted values inside `ofSpec`'s faithful domain, e.g.
  `value ∈ [Int64.MIN, Int64.MAX]` for `Int64.ofInt`; a
  missing range constraint makes the conversion law unprovable, surfacing the silent-wrap trap),
  from which `parse_sound_toSpec` for the *generated* parser is
  auto-derived. A lint additionally warns at elaboration when `ofSpec` appears with no value
  constraint at all. These seams have no formal
  oracle (real-world-format conformance and the canonical serializer are user choices); they
  are the *only* proofs left to the human. Because this file holds *your* proofs, it is a
  **write-once scaffold**: `spec.lean`/`parser.lean` are regenerated on every elaboration, but
  an existing `soundness.lean` is never overwritten (delete it to re-scaffold). Staleness is
  structurally impossible — its obligations are stated against the defs imported from
  `parser.lean`, so a grammar change either retargets them (and outdated proofs fail to
  compile) or breaks the file loudly. Regeneration of `spec.lean`/`parser.lean` is itself
  guarded: a pre-existing file *not* generated by this tool (no `/- Generated by Triptych`
  sentinel header) is never overwritten — hard error.

Every generated proof outside `soundness.lean` depends only on the standard axioms
`propext, Classical.choice, Quot.sound` — no `sorry`, `native_decide`, or extra axioms.

## Ambiguity and value coherence

The grammar class permits ambiguous decompositions through alternation, optional items, and
backtracking token splits. `decode` enumerates every full parse and selects the first, so
recognition correctness alone does not make the selected captures or value grammar-determined.

`Triptych.Theorems.Coherence` exposes that boundary:

* `fullParses` is the complete operational parse list, with `decode = fullParses.head?`;
* `CaptureCoherent`, `EnvCoherent`, and `ValueCoherent` state progressively weaker forms of
  agreement between all full parses;
* `GrammarCaptureFunctional` lifts capture coherence to every input: the grammar denotes a
  partial function from strings to complete capture maps, even if duplicate derivations exist;
* `computeValueF_coherent` covers scalar capture readers, while `computeValueMap_coherent`
  covers repeated-capture readers such as IPv6's `[H16]`;
* `Denotes` gives a relational format semantics, and `decodeGatedMap_eq_some_iff_denotes`
  proves that first-match execution realizes it when both acceptance and value are coherent;
* `DecodeUnique` is a decidable sufficient condition; `#eval decide` checks concrete inputs,
  while the coherence theorems consume a proof of the proposition.

Representative example inputs evaluate as unique. Triptych does not yet emit a static
all-input proof for the full grammar language. It does provide a first conservative checker:
`Grammar.staticUnique` recognizes unary reference paths, required sequences with
prefix-deterministic intermediate symbols, and alternatives beginning with pairwise-distinct
literal characters. Literals and exact-width token runs are prefix-deterministic; a
variable-width token is accepted at the sequence tail, where only its full-consumption match
matters, or before a nonempty literal delimiter whose first character is outside the token
class. A required reference of the form `X ::= ["lit"]` is also accepted at the sequence head
when the unique remainder cannot begin with `lit`'s first character. This proves the optional
sign and decimal-point boundaries in Decimal. `GrammarDecodeUnique.of_staticUnique` proves the
check sound for every input and derives the weaker semantic target
`GrammarCaptureFunctional`. This certifies both Graph and Decimal statically; the DSL emits
`grammarDecodeUnique`,
`grammarCaptureFunctional`, and `grammarValueCoherent` automatically. Its
`parse_iff_denotes` theorem consumes only capture functionality and states that parser success
is equivalent to the capture-level `Denotes` relation. For a domain-valued parser, the relational
reader is `ofSpec` composed with the grammar value reader. Recursive FIRST-set alternatives,
shared-prefix alternatives, general nullable sequences, and repetition remain.

## Example

This example follows Cedar's naming: `/64` is the CIDR prefix, represented by Cedar's
`IPv6Prefix` type and `CIDR.pre` field.

```lean
triptych IPv6 where
  grammar
    V6Net       ::= V6Addr | V6Addr "/" Prefix
    V6Addr      ::= Full | Compressed
    Full        ::= rep H16 sepBy ":" {8}
    Compressed  ::= [Left] "::" [Right]
    Left        ::= rep H16L sepBy ":" {1,7}
    Right       ::= rep H16R sepBy ":" {1,7}
    H16         ::= hexDigit{1,4}
    H16L        ::= hexDigit{1,4}
    H16R        ::= hexDigit{1,4}
    Prefix      ::= digit{1,3}
  value'
    toIPv6Net [H16] [H16L] [H16R] Prefix
  constraints
    count H16L + count H16R < 8
    noLeadingZero Prefix
    nat Prefix ∈ [0, 128]
  to "Outputs/IPv6"
```

produces `IPv6.IsWf.V6Net`, `IPv6.IsValid`, a `DecidablePred` validator, the automatically
proved surface/engine equivalences, and a verified `IPv6.parse : String → Option IPNet`.
`count X` reads the generated repetition count, while a `[X]` list argument passes every span
matched by `rep X ...`; together they express and reconstruct full and compressed IPv6.
`IPv6.View` exposes those lists and the optional prefix as typed fields, and the generated
theorems state `IPv6.IsValid s ↔ ∃ v, IPv6.decodeView s = some v ∧ v.Valid` and
`IPv6.computeValue s = (IPv6.decodeView s).map View.denotation`. A spec with a value section
additionally gets the verified parser `<Name>.parse : String → Option α` (with its
auto-discharged `parse_sound`/`parse_complete`/`parse_reject`) and the reconciliation theorem
`<Name>.computeValue_eq` (see Decimal, Duration, Datetime, Graph). Adding a
`parser <p>` clause immediately emits a sound `checkedExtParse` wrapper plus
`soundness.lean` with the stronger static obligations for the unwrapped external parser —
the value section's optional `toSpec <f>` supplies the semantic comparison when its result type
differs, and otherwise defaults to `id`. Decimal points the parser clause at the real
`Cedar.Spec.Ext.Decimal.parse`. A
`printer auto` asks Triptych to synthesize a total certified serializer from an analyzable
`value`; it succeeds only when the compiler can prove a right inverse. The initial rule covers
signed decimal integers (`Sign * nat Digits` or `nat Digits * Sign`). Unsupported, constrained,
`ofSpec`, and arbitrary `value'` cases are rejected. An explicit `printer <toString>` names one
canonical serializer over the generated parser's result type. One typed `encode_view` obligation
says it decodes to a valid view with the original value as its converted denotation. Triptych
derives parse/print roundtrip, `toString`
injectivity, and normalization for the *generated* parser directly from that witness. When a
`parser` clause is also present, its derived acceptance/value projections feed the corresponding
*external* parser theorems (matching Cedar's `parse_toString_roundtrip` etc.). When a printer
roundtrip and parser-agreement theorem are already available, `triptych_encode` composes them with
the generated view theorems. `triptych_encode_direct` provides the Cedar-independent route from
direct validity and generated-value facts. A third route, `triptych_encode_derivation`, projects a
valid root derivation directly to `encode_view`. `DerivationPrinter` packages
`toDerivation : Value → RootDerivation` with structural validity, view validity, and
denotation-preservation proofs; its `toString` and parser roundtrip follow generically. Multiple
certificates can select different verified presentations of one value. Arbitrary `value'`
functions still require a user-supplied certificate or printer proof.

See `DESIGN.md` for the full design. The Cedar-free Graph example lives in
`../other-examples/Graph/`. Cedar-backed examples (Decimal, Duration, Datetime, IPv4, IPv6) live
directly under `../cedar-examples/`. Every shipped Cedar `soundness.lean` scaffold is discharged,
and the generated parser, readable spec, checked-external, and printer conformance suites
currently report zero failures.

## Scope

* **Grammar tier:** a strict subclass of regular — concatenation, finite alternation,
  optional items, character-class token runs (`digit`/`hexDigit`/`bit` with length
  bounds), and separated group repetition (`rep … sepBy`). No recursion (not
  context-free); no data-dependent length.
* **Constraint tier:** grammar ∩ any decidable predicate over the captures (so the
  *accepted* language can be non-regular, e.g. "length is a triangular number").
* **Value tier:** any type (via the `value'` escape) — structured output (graphs,
  records), not just `Int`.

Grammar reconciliation and decidability are automatic across this scope. Scalar `value` and
`constraints` sections are inspectable ASTs; structured values and non-arithmetic constraints
use `value'`/`constraints'`. Both escapes accept `[X]` for all spans of a repeated capture, and
generated views preserve that argument as `List String`. Their surface/engine reconciliation is
also automatic because both layers invoke the supplied typed function. Manual obligations remain
only where semantics cannot be inferred from the grammar: agreement with an external parser,
conversion fidelity, and the choice of a canonical serializer.

## Roadmap

See [`ROADMAP.md`](ROADMAP.md). The Cedar baseline is complete. Current work prioritizes reusable
DSL components, richer collection semantics, stronger bridge automation and diagnostics, broader
printer synthesis, static capture-functionality coverage, CI/performance work, and then new
examples such as UUID and DIMACS CNF.

## Build

```sh
lake build
```

Lean `v4.31.0`, batteries only (no Mathlib). This root package is Cedar-free.

Build the Cedar-free examples package separately:

```sh
cd other-examples
lake build
lake exe parser_benchmark
```

The Cedar-backed examples and validation proofs are an optional companion package:

```sh
cd cedar-examples
lake build
lake build ConformanceTests
```

That package uses a local `require Cedar from "../../cedar-spec/cedar-lean"` so its
soundness modules can target Cedar's real extension parsers. Clone `cedar-spec` beside this
repo to build the integration; it is not needed to build or depend on Triptych core.

The CI workflow runs all three package gates and pins the Cedar integration checkout to the
parser API revision used by the bridge proofs. `decodeBudget` exposes the exact structural
reference, repetition, and terminal-prefix limits used by the reference decoder; these are
enumeration budgets, not a polynomial total-runtime claim.

## Provenance

Originated while verifying the Cedar extension-type parsers (Decimal, Duration,
Datetime, IPAddr); extracted into a standalone Cedar-free library with a separate optional
Cedar examples package. Source files retain their original Apache-2.0 "Cedar
Contributors" headers. Known as **FormatSpec** before 2026-07; the name *Triptych* refers to
the three hinged panels the tool emits from one grammar — spec, parser, and the
reconciliation proof between them.
