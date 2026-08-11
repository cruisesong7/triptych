# Triptych Roadmap

The Cedar IP address family is complete end to end. The roadmap now prioritizes reducing
user-authored semantic proof work, broadening useful synthesis, and improving compiler
diagnostics and execution quality.

## 1. Completed Cedar baseline

The five Cedar-backed formats now provide the baseline against which new compiler work is
measured.

### IPv4

- complete: discharge the canonical serializer's typed `encode_view` obligation;
- complete: discharge all three external-parser obligations;
- complete: retain exact agreement with Cedar for bare addresses, CIDR prefixes, prefix bounds,
  octet bounds, and canonical decimal spelling;
- complete: remove every proof placeholder from `IPv4/soundness.lean`.

### IPv6

- complete: full and compressed `::` grammar, optional CIDR prefixes,
  and generated `String → Option IPNet` parser;
- complete: analyzable `count X` constraints and generic proof automation for the
  cross-repetition `left + right < 8` bound;
- complete: Cedar unit-test conformance for valid, invalid, compressed, boundary, prefix,
  and family-dispatch cases;
- complete: add Cedar external-parser and canonical-printer clauses;
- complete: prove the generated value agrees with Cedar across every supported syntactic form;
- complete: discharge the typed printer witness and all external-parser obligations.

### Combined validation

- complete: validate the family-level behavior of Cedar's `ip` parser across IPv4 and IPv6;
- complete: cover inputs where IPv4 and IPv6 dispatch or rejection could disagree;
- complete: keep generated and bridge theorems on the accepted standard axioms;
- complete: run generated parser, readable-spec, checked-external, and printer suites from the
  independent `cedar-examples` package.

**Exit criterion achieved:** IPv4 and full IPv6 parse, value, reject, external-parser, printer,
and conformance obligations are complete. Every shipped Cedar `Outputs/*/soundness.lean` file
contains proofs rather than placeholders, and the conformance target reports zero failures.

## 2. Make proofs substantially more automatic

Use the finished IPAddr work to identify repeated proof patterns and move them into Triptych.
Prioritize reductions in user-authored proof volume:

- complete: emit typed decoded-component views with exact-input, validity, denotation,
  generated-parser success, and derived external-parser success normal-form theorems;
- complete: preserve scalar capture absence in views with grammar-derived `Option String`
  fields instead of collapsing absence to `""`;
- complete: emit decode-elimination lemmas for component readers, constraint phases, and values;
- complete: emit `checkedExtParse`, an exact success theorem, and soundness/view theorems that
  validate arbitrary external parser results against the generated parser;
- complete: prove the checked wrapper is extensionally equal to an external parser once its
  static soundness theorem is available;
- complete: replace separate printer acceptance/value obligations with one typed `encode_view`
  witness and derive generated-parser roundtrip, injectivity, normalization, and compatibility
  projections automatically;
- complete: add `triptych_encode` to compose printer roundtrip, parser agreement, generated view
  validity/value facts, and an optional explicit conversion inverse into `encode_view`;
- complete: add `triptych_encode_direct`, the external-parser-free composition route from direct
  generated-spec acceptance and value facts to `encode_view`;
- complete: generate typed structural derivation trees for every production, with alternatives
  as constructors, optionals as `Option`, repetitions as `List`, and proved `render`,
  exact-capture full-parse membership, and coherent decode roundtrip;
- complete: project the root derivation to the flat value/constraint `View`, emit exact
  `decodeView_render` theorems, and add `triptych_encode_derivation` so printer proofs can
  construct syntax directly;
- independently specify and verify reusable DSL components such as signs, fixed-width digits,
  bounded integers, and separators at the language, capture, and denotation levels;
- complete: register Cedar decimal natural/signed conversion rules and IPv4 parser components
  as reusable automation rules so downstream proofs apply a
  named component specification instead of unfolding its implementation;
- complete: build an extensible external-parser rule registry and `triptych_sound` tactic for
  successful `Option` paths, alternatives, maps, filters, guards, and conditionals;
- complete: add a separate `triptych_parser_search` saturation registry and bounded
  `triptych_auto` tactic; use it in Decimal, Duration, Datetime, and IPv4 to derive routine
  external soundness, completeness, and typed-view consequences from semantic agreement facts;
- generate stronger bridge lemmas for common external parser combinators;
- automate remaining format-specific rejection, `toSpec`, and direct printer/view construction
  obligations where the DSL contains enough semantic information;
- turn recurring decomposition arguments into reusable tactics or theorem families;
- generate useful proof hints and source-located diagnostics when automation stops;
- separate genuinely semantic obligations from bookkeeping that the compiler can discharge;
- report obligation counts and which DSL escape caused each remaining manual proof;
- add regression tests measuring handwritten proof lines for each Cedar example.

**Exit criterion:** regenerating the IPAddr examples leaves only format-specific semantic facts
for the user, with routine parser plumbing discharged automatically.

## 3. Improve compiler utility and execution quality

- partial: `DerivationPrinter` now packages a value-to-derivation inverse and all validity laws;
  `printer auto` synthesizes it for total signed-decimal `value` definitions in either
  multiplication order;
- extend automatic printer synthesis to constrained/domain-converted values and named policies
  such as Duration's smallest-unit and largest-unit-first presentations;
- improve diagnostics for inaccessible captures, malformed repetitions, overlapping choices,
  constraint-phase mistakes, and unsupported format features;
- complete: add CI jobs for the Cedar-free core, `other-examples`, and the optional Cedar package;
- avoid unnecessary parse enumeration in deterministic fragments;
- partial: expose exact reference-recursion, repetition, and terminal-prefix budgets and run a
  timing-report benchmark smoke test; total runtime remains branch-sensitive under backtracking;
- make generated files and proof obligations easier to navigate from the source DSL.

### Standalone specialized parsers and foreign consumers

The generic generated entry points are verified but still expose compiler plumbing such as
`gatedParse`, the grammar, constraints, value reader, and conversions. Package each format as an
individual executable artifact in stages:

1. generate a specialized Lean entry point, `<Name>.parse : String → Option δ`, whose public
   signature hides all generic arguments;
2. emit a standalone Lean executable with a stable text or JSON protocol and a reproducible
   corpus test comparing it with the in-Lean parser;
3. optionally expose the same specialized entry point through a narrow C ABI and a Rust consumer
   crate;
4. document the trust boundary: the Lean theorem verifies parser semantics, while code
   generation, the Lean runtime, ABI wrapper, FFI, and Rust caller remain trusted integration
   components;
5. treat direct verified Rust extraction or translation as a separate research track rather
   than describing reverse FFI as verified Rust.

## 4. Maintain the Cedar baseline

- complete: discharge Datetime's three external-parser obligations;
- complete: audit Decimal and Duration after applying the new automation;
- complete: require zero proof placeholders and complete conformance for all shipped Cedar
  examples;
- keep the five formats building as regression fixtures for changes to the DSL, emitter,
  automation, and Cedar dependency.

## 5. Collection-aware values and constraints

Repeated captures are already available to `value'` as `List String`. Generalize the
analyzable value and constraint tiers with operations such as:

- `count X` (complete);
- `sum X`;
- per-element predicates such as `forall X`;
- list arguments for `constraints'` (complete, including mixed scalar/list predicates and typed
  generated views);
- richer access to repeated values beyond the completed generated count reader.

## 6. Broader capture-functionality certificates

The current proved foundation remains available:

- required deterministic sequences;
- direct disjoint literal alternatives;
- unary token/literal delimiter boundaries;
- a leading optional-literal reference separated by FIRST-character exclusion;
- emitted `grammarDecodeUnique`, `grammarCaptureFunctional`, `grammarValueCoherent`, and
  `parse_iff_denotes` when certification succeeds.

Broaden this analysis when a concrete format, printer proof, or parser optimization needs it.
Later extensions may include recursive FIRST-language
disjointness, general nullable sequences, repetition functionality, production-level
certificate composition, and eventually a tagged finite-state transducer checker with
counterexamples.

## 7. New examples

After the higher-leverage automation, diagnostics, and execution work:

1. **UUIDv4**, followed by **UUIDv7**;
2. **DIMACS CNF**;
3. SemVer, cron expressions, DNS names, or HTTP Structured Fields based on the next concrete
   language feature that needs pressure-testing.

Full JSON and SQL remain out of scope until Triptych has recursive grammar and value semantics.
