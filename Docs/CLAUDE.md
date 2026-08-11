# Triptych — session handoff / project context

This file captures the project state a fresh coding session needs to continue the work.

## What this repo is

A Lean 4 library: a **grammar-to-specification compiler** for flat, non-recursive
string-format parsers. A `triptych` DSL block (grammar + optional value/constraints)
generates a readable surface spec, an analyzable/executable engine, and an auto-emitted,
machine-checked reconciliation proof between them. See `README.md` (overview) and
`DESIGN.md` (full design).

**Provenance:** extracted from `~/Documents/cedar-spec` (branch `cruise-grammar-to-spec`,
history preserved on `origin/cruise-grammar-to-spec` of `github.com/cruisesong7/cedar-spec`)
where it originated verifying Cedar's extension-type parsers. Now standalone.

## Build / environment

- `lake build Triptych` — Cedar-free core build (~37 jobs). Lean **v4.31.0**,
  **batteries only, NO Mathlib** (deliberate, for now).
- `cd other-examples && lake build` — Cedar-free Graph example package.
- `cd cedar-examples && lake build` — optional Cedar bridges, soundness
  proofs, and Cedar-backed examples.
- `cd cedar-examples && lake build ConformanceTests` — explicit differential suite,
  excluded from the Cedar examples package's default target.
- Remote: `github.com/cruisesong7/triptych` (public), branch `main`.
- Shell note: if the session's cwd resets between commands, prefix with
  `cd ~/Documents/triptych`.

## Hard invariants (do not violate)

- **Axioms:** every generated equivalence/decidability result must depend ONLY on
  `propext, Classical.choice, Quot.sound`. NEVER introduce `sorry`, `native_decide`,
  `ofReduceBool`, or new axioms. The only intentional source-level `sorry`s are the
  generated user-obligation scaffolds for a declared parser/printer. A printer emits one
  `encode_view` obligation: serialization decodes to a valid typed view whose converted
  denotation is the original domain value. `encode_accepted`, `encode_value`,
  `ofSpec_toSpec`, generated-parser roundtrip, injectivity, and normalization are derived.
  `triptych_encode` composes a known serializer roundtrip and parser-agreement theorem with the
  generated view facts; an `ofSpec` conversion still requires its explicit inverse fact.
  `triptych_encode_direct` instead starts from generated-spec acceptance and value proofs and
  therefore has no external-parser dependency.
  `triptych_encode_derivation` starts from a generated root derivation and
  `decodeView_render`, removing decoder/capture-map bookkeeping. `DerivationPrinter` packages
  `toDerivation` with structural, view, and denotation proofs and derives `toString`.
  `printer auto` currently synthesizes this certificate only for the total signed-decimal
  `value` pattern, accepting either multiplication order; do not claim that arbitrary,
  constrained, `ofSpec`, or `value'` functions can be inverted.
  A declared external parser emits `extparse_sound`/`_complete`/`_reject`. Values with BOTH
  `ofSpec` and `toSpec` also receive the faithfulness
  obligation `toSpec_ofSpec : isValid s → computeValue s = some v →
  toSpec (ofSpec v) = v` on accepted values. It is provable exactly when the range constraint
  pins accepted values inside `ofSpec`'s faithful domain and unprovable when a wrapping
  conversion is left unguarded. Its payoff `parse_sound_toSpec` is discharged via
  `gatedParseOfSpec_sound_toSpec`. A lint additionally warns at elaboration when `ofSpec` appears
  with no value constraint at all. Shipped examples discharge every scaffold obligation.
  Printer theorems use the clean δ-view `parse (toStr d) = some d`. The generated
  `parse_sound`/`_complete`/`_reject` are fully axiom-clean. A `parser` clause also emits the
  axiom-clean `checkedExtParse` fallback and its soundness/view theorems whenever the spec value
  has `DecidableEq`; these introduce no additional obligation.
- Verify axiom-cleanliness with a temp `#print axioms <name>` file, then delete it.
- `simp` config syntax (v4.31): `simp (config := { maxSteps := N }) only [...]` — config
  BEFORE `only`. `grind` is available; `tauto` is NOT (no Mathlib).
- Use `git ci` (commit --signoff), not `git commit`.

## Architecture (dependency order)

- `Grammar.lean` — core `Grammar`/`Production`/`Seq`/`SymItem`/`Sym`/`TokClass`/`LenSpec`
  data. `Sym`: `lit | ref | term | rep`. `TokClass`: `digit | hexDigit | bit`.
  `Sym.allRefs` (sees through `rep`), `Sym.repOk`/`Grammar.repOk` (rep well-formedness).
- `Classify.lean` — decidable syntactic checks (acyclicity, ref resolution) via `directRefs`.
- `Denote.lean` — `matchesSym`/`matchesSeq`/`matchesProd` → `IsWf` (Prop denotation);
  readable leaf predicates `IsDigits`/`IsBits`/…; `matchesTerm`.
- `Value.lean` — `ValExpr` AST + `eval : Env → Int` (scalar value DSL); readers
  (`natOf`/`intOf`/`lenOf`/`signOf`), `surfaceBinder`.
- `Constraint.lean` — `Constraint`/`ConstraintEntry` AST, explicit
  `.wellFormed`/`.value` phase classification, `card`/`presentCount`, and the `opaque`
  internal node used by the surface `constraints'` escape (`opaqueEnvClosure`).
- `Decode.lean` — executable capture extractor `decode`/`matchSym`/`matchStar`/`matchRep`;
  `computeValue : … → Option Int` and `computeValueF : … → (Env → α) → Option α` (arbitrary
  value type). `CaptureMap`/`Env`.
- `Roundtrip.lean` — `decodeSome_iff_IsWf` (decode ↔ IsWf), `rep_iter`/`matchStar_iter`,
  `decIsWf` (conditional `DecidablePred (IsWf g)`, needs `g.repOk = true`).
- `Coherence.lean` — value is grammar-determined, not decoder-selected: `fullParses`
  (all full parses, `decode = head?` of them), full-map `CaptureCoherent`, scalar-view
  `EnvCoherent`, and map-generic `ValueCoherent`; `GrammarCaptureFunctional` is the
  all-input partial-function property. `computeValueF_coherent` covers scalar readers and
  `computeValueMap_coherent` covers repeated captures. `DecodesAs` is the relational value
  semantics. `DecodeUnique` (≤ 1 full parse) is a decidable per-string sufficient condition;
  `#eval decide` is a runtime diagnostic, while the theorems consume a proof.
  `GrammarDecodeUnique` is the stronger all-input derivation certificate.
- `Unambiguity.lean` — soundness of the conservative `Grammar.staticUnique` syntax check.
  It proves `GrammarDecodeUnique` for unary reference paths, required sequences with
  prefix-deterministic intermediate symbols, and pairwise-distinct literal-leading
  alternatives; the DSL derives and emits `grammarCaptureFunctional` and
  `grammarValueCoherent` when it succeeds.
- `RelationalParser.lean` — connects generated gated parsers to capture-level `Denotes`.
  Under `GrammarCaptureFunctional`, it covers map/environment readers and `ofSpec` variants;
  the DSL emits `parse_iff_denotes` from these theorems. Graph has this contract and all three
  static all-input certificates. Other example `#eval`s remain representative.
- `Reconcile.lean` — reusable lemmas for emitted grammar/full-WF equivalences (leaf
  `_matchesTerm`, `matchesSym_rep_iff`, reader-agreement `natOf_getD` etc.).
- `Assemble.lean` — bundles `isWf`/`satisfiesConstraints`/`isValid`; `component`;
  contract statements `SoundStmt`/`CompleteStmt`/`RejectStmt`
  (over value type `β`, `toSpec : α → β`).
- `Emit.lean` — renders surface predicates (`symPred`/`termPred`), grammar literals,
  `matchesRefProof`/`isWfGrammarEquivProof`/`isWfEquivProof`/`isValidEquivProof`.
- `Syntax.lean` — the `triptych` command (DSL surface → core, elaborate, write the three
  generated files). Emits `gatedParse`/`parserContractsProof` (the verified parser) and
  splits output into `spec`/`parser`/`soundness` (see below).
- `other-examples/Graph/` — the Cedar-free structured Graph example.
- `cedar-examples/Inputs/<Format>.lean`
  — each handwritten grammar runs
  `triptych` and writes up to THREE modules under `Outputs/<Format>/`: `spec.lean` (readable surface,
  proof-free), `parser.lean` (engine bundle + auto-discharged proofs `IsWf_equiv`/
  `computeValue_eq`/decidability + the generated correct-by-construction parser `parse` and its
  discharged `parse_sound`/`parse_complete`/`parse_reject`), and — ONLY when the `triptych`
  has a `parser <p>` clause OR a `printer` clause — `soundness.lean` (proof-obligation
  placeholders, partitioned into two banner-delimited sections: "· generated parser" — one
  `encode_view` obligation, derived encode/conversion projections, and discharged
  `parse_toString_*` theorems; then "· external parser" — the `extparse_*` obligations and
  discharged external printer theorems. With `ofSpec` + `toSpec`, `toSpec_ofSpec` and its
  discharged payoff `parse_sound_toSpec` are also in the generated section. A `printer`-only
  spec has just the generated section; a `parser`-only spec just the external one. File chain:
  spec ← parser ← soundness.
  Importing the handwritten input module regenerates spec/parser (guarded: a pre-existing file WITHOUT the
  `/- Generated by Triptych` sentinel header is never overwritten — hard error);
  `soundness.lean` is WRITE-ONCE (it holds the
  user's proofs — never overwritten once it exists; delete it to re-scaffold). Staleness stays
  impossible structurally: its obligations are stated against defs imported from `parser.lean`,
  so a grammar change retargets them or breaks loudly. Trade-off: generator improvements to the
  discharged printer theorems emitted there require a delete-and-regen to pick up.
  Importing the generated modules builds standalone (so they can't silently drift). Decimal's
  `parser` clause names the real `Cedar.Spec.Ext.Decimal.parse` (see below).
- `cedar-examples/ConformanceTests.lean` — a one-time confidence
  check (its own `ConformanceTests` lib
  target, out of `default_target`): runs the GENERATED EXECUTABLE parsers (`<Name>.parse` =
  `gatedParse[OfSpec] isValid computeValue …`, the decode-based engine — NOT the readable surface
  `IsValid` Prop) against Cedar's REAL parsers over Cedar's OWN unit-test corpus
  (`cedar-lean/UnitTest/{Decimal,Datetime}.lean`). Because `ofSpec` makes Decimal/Duration `parse`
  return the SAME type as Cedar's, the check is direct equality `ourParse s = cedarParse s` (Cedar
  is the oracle — checks accept-set AND value at once); Datetime (no `ofSpec`) compares
  `ourParse s = (cedarParse s).map datetimeMillis`. Plain `#eval` (no `native_decide`, no axioms);
  a nonzero failure count aborts the build. Current generated-parser suites pass 32/32 Decimal,
  42/42 Duration, and 74/74 Datetime cases; checked-external suites repeat those corpus sizes.
  On the shared IPAddr corpus, IPv4 and IPv6 each pass 89/89 generated-parser, 89/89 readable-spec,
  and 89/89 checked-external cases. IPv6 printer roundtrip passes 52/52. Total failures: 0.
  This suite caught the Duration sign bug (below).
- **Package boundary:** the root `lakefile.lean` and manifest depend only on Batteries.
  `cedar-examples/lakefile.lean` owns the local cedar-lean dependency and imports Triptych
  core as a path dependency. Handwritten DSL sources live under `Inputs.*`; generated
  `spec`/`parser`/optional `soundness` modules live under `Outputs.<Format>.*`.
  Format-specific proof machinery lives under `Proofs.<Format>.*`, while reusable backend
  helpers live under `CedarSupport.*`.
  After a generator edit, build `CedarExamples` twice if regeneration leaves an olean one
  pass behind.

## DSL capabilities (current scope)

- Grammar: concatenation, alternation (`|`), optional `[x]`, terminals `digit`/`hexDigit`/`bit`
  with length `{n}`/`{lo,hi}`/`+`, the `sign` terminal (optional leading `-`, only as a
  production's sole rhs — see sign captures below), and separated group repetition
  `rep <item> sepBy "<sep>" <len>`. Strict subclass of regular; NO recursion (not context-free),
  NO data-dependent length.
- Constraints: capture-only forms, including arithmetic bounds, enter `wfPart`; only
  expressions explicitly mentioning final `value` enter `valPart`. Includes cardinality
  `card` and arbitrary-decidable capture escapes `constraints' f X Y` (so `IsWf` can be
  non-regular, e.g. "length is triangular").
- Values: `value <arith>` (scalar Int DSL) OR `value' f X Y` escape returning ANY type
  (structured output — graphs, records). Escape value type flows through `computeValueF`.
  Value readers: `nat X`/`int X`/`len X` (magnitude/length of capture `X`), and a BARE capture
  name `X` = its ±1 SIGN (there is NO `sign` keyword — it was removed). A bare name is valid ONLY
  when `X ::= sign` (a dedicated sign capture); elaboration rejects a bare ref to a non-sign
  capture (the old silent-`+1` trap) and `nat/int/len` of a sign capture. `sign` lowers to the
  same `Sym` as `["-"]` (optional lit), so it's pure grammar sugar — the engine/denotation/proofs
  never see a new constructor; detection of sign productions is SYNTACTIC (in `elabTriptych`).
- Clause nesting: `ofSpec <f>` and `toSpec <g>` are semantic sub-clauses of scalar `value`;
  `value'` may also carry `toSpec` when an external parser returns a different type. The maps
  have opposite directions: `ofSpec : β → δ` converts a spec value to the generated parser's
  domain type; `toSpec : δ → β` converts a domain/external-parser result to the spec value.
  An omitted `toSpec` defaults to `id`; write it only when the two value types differ.
  When both are present, `toSpec_ofSpec : toSpec (ofSpec v) = v` on accepted values is the
  conversion obligation. With a printer, `encode_view` derives
  `ofSpec_toSpec : ofSpec (toSpec d) = d`. Both conversions are independent of the optional
  `parser <p>` clause, which now only names an implementation.
  CONVERSION GUARD: `ofSpec` with no value constraint draws an elaboration-time warning because
  a wrapping conversion such as `Int64.ofInt` can silently convert out-of-range accepted inputs.
- `rep` well-formedness (enforced at parse time + carried in `repOk`, required by the
  roundtrip): separator must be NON-EMPTY and lower bound >= 1. Both are cases where the
  decoder (`item (sep item)*`) genuinely disagrees with the denotation.

## Key capture-model fact (bites structured/rep values)

`decode` records captures under nonterminal NAMES, only via the `ref` case. Consequences:
- A bare top-level terminal (`Adj ::= bit+`) records NO name-keyed capture — wrap it in a
  named sub-production (`Adj ::= Cells; Cells ::= bit+`) so `Cells` holds the span. The bare-sign
  variant of this trap (a bare `["-"]` captured nowhere, silently dropping the sign — once a real
  Duration bug caught by conformance) is now PREVENTED by design: the `sign` terminal must be a
  production's sole rhs (`Sgn ::= sign`), so the sign always owns a capture, and `value` reads it
  by bare name. Both Decimal and Duration use this (`Decimal ::= Sgn Natural "." Fraction`,
  `Duration ::= Sgn Components`); `value` = `Sgn * (…magnitude…)`.
- `CaptureMap.toEnv` uses `find?` → returns the FIRST match, so repeated elements of a `rep`
  collapse in the SCALAR (`Env`) view. The rep's item COUNT is captured under `<Item>#count`.
  The individual repeated elements ARE now addressable via `CaptureMap.toEnvList` (all spans of
  a name, in order) / the surface `componentList`: a `value'` escape marks a list argument `[X]`
  and receives `List String` (all of `X`'s repeated spans). IPv6 uses this for the full,
  left-of-`::`, and right-of-`::` group lists, then builds a structured `IPNet`. Plumbing:
  `computeValueMap`
  (`CaptureMap → α`, vs `computeValueF`'s `Env → α`) drives the escape; `opaqueMapClosure` builds
  the closure; `computeValueEqProof` reads a list cap via `componentList`, a scalar via
  `component`. The scalar DSL also supports `count X`, backed by the generated `X#count`
  capture; this is enough for bounds such as IPv6's `count H16L + count H16R < 8`.
  General analyzable `sum X`/`forall X` reductions still require collection-aware AST semantics.
  Both `value'` and `constraints'` accept `[X]`; the latter supports mixed scalar/list predicates,
  evaluates against the full `CaptureMap`, and exposes list arguments in generated views.

## Open next steps

`ROADMAP.md` is authoritative. Work in this order:

1. Specify reusable DSL components and strengthen external-parser bridge automation, proof hints,
   and source-located diagnostics.
2. Extend printer synthesis beyond the total signed-decimal pattern to constrained values,
   conversions, and named canonicalization policies.
3. Generalize repeated captures beyond `count X` and list-aware escapes: analyzable sums and
   per-element constraints.
4. Broaden static capture-functionality certificates and improve deterministic execution.
   `DecodeBudget`, the Graph benchmark smoke executable, and three-package CI are now present;
   they do not yet constitute a total-runtime complexity proof.
5. Package each generated `<Name>.parse` behind a standalone executable and then a narrow C ABI.
   Keep the trust statement explicit: reverse FFI does not verify Lean's runtime, ABI, or Rust.
6. Add UUIDv4/v7 and then DIMACS CNF after those utility improvements. Full JSON and SQL require
   a separate recursive-grammar project and are not near-term examples.

Deferred housekeeping: consider Mathlib for the Graph representation as a separate toolchain
upgrade and keep the concise `HACKATHON.md` pitch aligned with the main overview.

## Generated structural derivations

Every production now has `<Name>.Derivation.<Production>`. Alternatives become constructors,
optional symbols become `Option`, repetitions become `List`, and references contain child
derivations. `render` and `Valid` are emitted in `spec.lean`; executable validity instances,
`capturesWith`, exact `ProdMatch`, start-production `mem_fullParses`, and
`decode_render_of_captureFunctional` are emitted in `parser.lean`. A statically
capture-functional grammar also gets `decode_render`. The root gets `toView`,
`decodeView_render_of_captureFunctional`, and, under the same certificate,
`decodeView_render`. Decimal, IPv4, and IPv6 have standalone construction fixtures under
`Proofs/*/StructuralDerivation.lean`.

## Context on the SAT-graph thread (why the Graph example exists)

The conventional SAT representation of a graph is the upper-triangle of its adjacency matrix
as a space-separated bit assignment (the model read back from a Ramsey/coloring instance). The
The Cedar-free Graph example parses that into a structured graph value. "One grammar for all
orders" is achieved by a `bit+` grammar (any length) + a triangular-number constraint (carves
out valid lengths) + a value that recovers `n` from the length — demonstrating the
grammar-over-approximate / constraints-carve / value-interpret split. NOTE: DIMACS clauses are
the *solver input* (distinct from the graph *assignment*); graph6 (6-bit packed) is the dense
on-disk graph format and is a data-dependent-length case (out of grammar scope → hand-written
decode).
