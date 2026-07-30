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
  user-obligations in the `soundness.lean` of examples with a `parser`/`printer` clause:
  the 3
  external-parser obligations (`extparse_sound`/`_complete`/`_reject` vs the REAL Cedar parser)
  per example with a `parser` clause — Decimal, Duration, Datetime — plus, for examples that also
  have a `printer` clause (Decimal, Duration), 3 obligations: 2 encode
  (`encode_accepted`/`encode_value`, the latter phrased π-view `computeValue (toStr d) = some (π
  d)`) + 1 section (`lift_section : σ (π d) = d`, needed because the δ-view printer roundtrip lifts
  the generated parser through `σ`; = Cedar's `Int64.ofInt_toInt` for Decimal) — plus, for
  examples with BOTH `lift` and `parser … projection` (Decimal, Duration), 1 faithfulness
  obligation `lift_faithful : isValid s → computeValue s = some v → π (σ v) = v` (π∘σ = id ON
  ACCEPTED VALUES — the dual of `lift_section`, provable exactly when the range constraint pins
  accepted values inside σ's faithful domain; UNPROVABLE if the constraint is missing and σ
  wraps, so the silent-wrap trap surfaces as a permanent sorry; its payoff `parse_sound_proj`,
  the π-view soundness of the generated lifted parser, is discharged via
  `gatedParseLift_sound_proj`). A lint additionally warns at elaboration when `lift` appears
  with no value constraint at all. Decimal's 7 and Duration's 7 obligations are discharged.
  The remaining 8 are Datetime's 3 external-parser obligations and IPv4's 2 encode plus 3
  external-parser obligations. The printer
  theorems derived from those obligations
  (`parse_toString_roundtrip`/`toString_injective`/`normalize_eq_iff_parse_eq`, plus the
  `extparse_*` trio) are NOT `sorry`d — they carry `sorryAx` only transitively. Both parsers'
  printer theorems are stated in the clean δ-VIEW `parse (toStr d) = some d` (matching Cedar
  exactly). The generated `parse_sound`/`_complete`/`_reject` are fully axiom-clean. (Datetime has
  no `printer`: Cedar has no canonical `ToString Datetime`.)
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
  escape (`opaqueEnvClosure`).
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
  Under `GrammarCaptureFunctional`, it covers map/environment readers and lifted variants;
  the DSL emits `parse_iff_denotes` from these theorems. Graph has this contract and all three
  static all-input certificates. Other example `#eval`s remain representative.
- `Reconcile.lean` — reusable lemmas for emitted grammar/full-WF equivalences (leaf
  `_matchesTerm`, `matchesSym_rep_iff`, reader-agreement `natOf_getD` etc.).
- `Assemble.lean` — bundles `isWf`/`satisfiesConstraints`/`isValid`; `component`;
  contract statements `SoundStmt`/`CompleteStmt`/`RejectStmt` (over value type `β`, `π : α→β`).
- `Emit.lean` — renders surface predicates (`symPred`/`termPred`), grammar literals,
  `matchesRefProof`/`isWfGrammarEquivProof`/`isWfEquivProof`/`isValidEquivProof`.
- `Syntax.lean` — the `triptych` command (DSL surface → core, elaborate, write the three
  generated files). Emits `gatedParse`/`parserContractsProof` (the verified parser) and
  splits output into `spec`/`parser`/`soundness` (see below).
- `other-examples/Graph/` — the Cedar-free structured Graph example.
- `cedar-examples/{Decimal,Duration,Datetime,IPv4,IPv6}/`
  — each `grammar.lean` runs
  `triptych` and writes up to THREE modules beside it: `spec.lean` (readable surface,
  proof-free), `parser.lean` (engine bundle + auto-discharged proofs `IsWf_equiv`/
  `computeValue_eq`/decidability + the generated correct-by-construction parser `parse` and its
  discharged `parse_sound`/`parse_complete`/`parse_reject`), and — ONLY when the `triptych`
  has a `parser <p> projection <π>` clause OR a `printer` clause — `soundness.lean` (the `sorry`d
  obligations, PARTITIONED into two banner-delimited sections: "· generated parser" — the shared
  `encode_*`/`lift_section` obligations (plus, with `lift` + `projection`, `lift_faithful` and its
  discharged payoff `parse_sound_proj`) + the discharged `parse_toString_*` printer theorems about
  `<Name>.parse`; then "· external parser" — the `extparse_*` obligations + discharged external
  printer theorems about the real Cedar `parse`. Generated-first, since the external printer
  theorems reuse the generated section's `encode_*`. A `printer`-only spec has just the generated
  section; a `parser`-only spec just the external one). File chain: spec ← parser ← soundness.
  Importing `grammar` regenerates spec/parser (guarded: a pre-existing file WITHOUT the
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
  `gatedParse[Lift] isValid computeValue …`, the decode-based engine — NOT the readable surface
  `IsValid` Prop) against Cedar's REAL parsers over Cedar's OWN unit-test corpus
  (`cedar-lean/UnitTest/{Decimal,Datetime}.lean`). Because `lift` makes Decimal/Duration `parse`
  return the SAME type as Cedar's, the check is direct equality `ourParse s = cedarParse s` (Cedar
  is the oracle — checks accept-set AND value at once); Datetime (no lift) compares
  `ourParse s = (cedarParse s).map datetimeMillis`. Plain `#eval` (no `native_decide`, no axioms);
  a nonzero failure count aborts the build. Currently 32 Decimal + 42 Duration + 74 Datetime +
  30 IPv4 + 29 IPv6 = 207 cases, all passing. This is what caught the Duration sign bug (below).
- **Package boundary:** the root `lakefile.lean` and manifest depend only on Batteries.
  `cedar-examples/lakefile.lean` owns the local cedar-lean dependency and imports Triptych
  core as a path dependency. Its format modules live directly at `Decimal.*`, `Duration.*`,
  `Datetime.*`, `IPv4.*`, and `IPv6.*`; shared bridge helpers live under `CedarSupport.*`.
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
- Clause nesting (two duals): `lift <σ>` is a SUB-clause of `value` (parses only after a scalar
  `value <arith>`, not `value'` — a `value'` already picks its own output type), and `projection
  <π>` is a sub-clause of `parser`. They are opposite maps: `σ : β → δ` lifts the spec value type
  UP to the domain type so the GENERATED parser returns `Option δ`; `π : δ → β` reads an EXTERNAL
  parser's domain value DOWN to `β` to state its contract. For a lifted example they are a
  section/retraction pair (`σ ∘ π = id`, the `lift_section` obligation; the dual `π ∘ σ = id` ON
  ACCEPTED VALUES is the `lift_faithful` obligation, emitted whenever lift + projection are both
  present — see the axiom-invariant bullet above). So: `projection` is
  parser-only (and, with `printer`, also underpins the lifted generated roundtrip via
  `lift_section`); `lift` needs a scalar `value` and works standalone (no parser/printer needed).
  LIFT GUARD: `lift` with NO value constraint at all draws an elaboration-time lint warning
  (a wrapping σ like `Int64.ofInt` silently wraps out-of-range accepted inputs; the range
  constraint is what makes `lift_faithful` provable — ignore the warning only for a
  total-embedding σ).
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
  General `sum X`/`forall X` reductions still require collection-aware semantics.
  List args are `value'`-only; `constraints'` rejects `[X]` explicitly.

## Open next steps

`ROADMAP.md` is authoritative. Work in this order:

1. Finish IPAddr's external-parser and printer proofs now that full IPv6 grammar, values,
   generated proofs, and conformance are working.
2. Generalize repeated captures beyond `count X` and `value' [X]`: analyzable sums and
   per-element constraints, plus list-aware `constraints'`.
3. Improve compiler utility: generated layout printers, source-located ambiguity/coherence
   diagnostics, deterministic execution paths, cost bounds, and package-level CI.
4. Only after Cedar is complete, add UUIDv4/v7 and then DIMACS CNF. Full JSON and SQL require a
   separate recursive-grammar project and are not near-term examples.

Deferred housekeeping: consider Mathlib for the Graph representation as a separate toolchain
upgrade; document the layered scope boundary; review or prune legacy `HACKATHON.md`.

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
