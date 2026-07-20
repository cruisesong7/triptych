# FormatSpec — session handoff / project context

This file is auto-loaded by Claude Code sessions opened in this repo. It captures state a
fresh session needs to continue the work.

## What this repo is

A Lean 4 library: a **grammar-to-specification compiler** for flat, non-recursive
string-format parsers. A `format_spec` DSL block (grammar + optional value/constraints)
generates a readable surface spec, an analyzable/executable engine, and an auto-emitted,
machine-checked reconciliation proof between them. See `README.md` (overview) and
`FormatSpec/DESIGN.md` (full design).

**Provenance:** extracted from `~/Documents/cedar-spec` (branch `cruise-grammar-to-spec`,
history preserved on `origin/cruise-grammar-to-spec` of `github.com/cruisesong7/cedar-spec`)
where it originated verifying Cedar's extension-type parsers. Now standalone.

## Build / environment

- `lake build FormatSpec` — full build (~53 jobs). Lean **v4.31.0**, **batteries only, NO
  Mathlib** (deliberate, for now).
- Remote: `github.com/cruisesong7/formatspec` (public), branch `main`.
- Shell note: if the session's cwd resets between commands, prefix with
  `cd ~/Documents/formatspec`.

## Hard invariants (do not violate)

- **Axioms:** every generated equivalence/decidability result must depend ONLY on
  `propext, Classical.choice, Quot.sound`. NEVER introduce `sorry`, `native_decide`,
  `ofReduceBool`, or new axioms. The only intentional `sorry`s are the user-obligations in the
  `soundness.lean` of examples with a `parser`/`printer` clause (currently 13): the 3
  external-parser obligations (`extparse_sound`/`_complete`/`_reject` vs the REAL Cedar parser)
  per example with a `parser` clause — Decimal, Duration, Datetime — plus, for examples that also
  have a `printer` clause (Decimal, Duration), 2 encode obligations
  (`encode_accepted`/`encode_value`). So: Decimal 5 + Duration 5 + Datetime 3 = 13. The printer
  theorems derived from the encode obligations (`parse_toString_roundtrip`/`toString_injective`/
  `normalize_eq_iff_parse_eq`) are NOT `sorry`d — they carry `sorryAx` only transitively. The
  generated `parse_sound`/`_complete`/`_reject` are fully axiom-clean. (Datetime has no `printer`:
  Cedar has no canonical `ToString Datetime`.)
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
- `Constraint.lean` — `Constraint`/`ConstraintEntry` AST, `wfPart`/`valPart` classification,
  `card`/`presentCount`, `opaque` escape (`opaqueEnvClosure`).
- `Decode.lean` — executable capture extractor `decode`/`matchSym`/`matchStar`/`matchRep`;
  `computeValue : … → Option Int` and `computeValueF : … → (Env → α) → Option α` (arbitrary
  value type). `CaptureMap`/`Env`.
- `Roundtrip.lean` — `decodeSome_iff_IsWf` (decode ↔ IsWf), `rep_iter`/`matchStar_iter`,
  `decIsWf` (conditional `DecidablePred (IsWf g)`, needs `g.repOk = true`).
- `Reconcile.lean` — reusable lemmas for the emitted `IsWf_equiv` (leaf `_matchesTerm`,
  `matchesSym_rep_iff`, reader-agreement `natOf_getD` etc.).
- `Assemble.lean` — bundles `isWf`/`satisfiesConstraints`/`isValid`; `component`;
  contract statements `SoundStmt`/`CompleteStmt`/`RejectStmt` (over value type `β`, `π : α→β`).
- `Emit.lean` — renders surface predicates (`symPred`/`termPred`), grammar literals,
  `matchesRefProof`/`isWfEquivProof`/`isValidEquivProof` (the uniform proof closer).
- `Syntax.lean` — the `format_spec` command (DSL surface → core, elaborate, write the three
  generated files). Emits `gatedParse`/`parserContractsProof` (the verified parser) and
  splits output into `spec`/`parser`/`soundness` (see below).
- `Examples/{Decimal,Duration,Datetime,IPv4,IPv6,Graph}/` — each `grammar.lean` runs
  `format_spec` and writes up to THREE modules beside it: `spec.lean` (readable surface,
  proof-free), `parser.lean` (engine bundle + auto-discharged proofs `IsWf_equiv`/
  `computeValue_eq`/decidability + the generated correct-by-construction parser `parse` and its
  discharged `parse_sound`/`parse_complete`/`parse_reject`), and — ONLY when the `format_spec`
  has a `parser <p> projection <π>` clause — `soundness.lean` (the `sorry`d external-parser
  obligations). File chain: spec ← parser ← soundness. Importing `grammar` regenerates;
  importing the generated modules builds standalone (so they can't silently drift). Decimal's
  `parser` clause names the real `Cedar.Spec.Ext.Decimal.parse` (see below).
- **cedar-lean dependency:** `lakefile.lean` has `require Cedar from "../cedar-spec/cedar-lean"`
  (same toolchain v4.31.0, same batteries commit) so `soundness.lean` can reference the real
  Cedar ext parsers. After a generator edit affecting the dep, `lake build` twice (regeneration
  timing quirk: a regenerated file's olean can lag its own source within one pass).

## DSL capabilities (current scope)

- Grammar: concatenation, alternation (`|`), optional `[x]`, terminals `digit`/`hexDigit`/`bit`
  with length `{n}`/`{lo,hi}`/`+`, and separated group repetition `rep <item> sepBy "<sep>" <len>`.
  Strict subclass of regular; NO recursion (not context-free), NO data-dependent length.
- Constraints: `wfPart` (string-only) + `valPart` (value-dependent) DSL forms, cardinality
  `card`, and arbitrary-decidable escapes `constraints' f X Y` (so the ACCEPTED language can be
  non-regular, e.g. "length is triangular").
- Values: `value <arith>` (scalar Int DSL) OR `value' f X Y` escape returning ANY type
  (structured output — graphs, records). Escape value type flows through `computeValueF`.
- `rep` well-formedness (enforced at parse time + carried in `repOk`, required by the
  roundtrip): separator must be NON-EMPTY and lower bound >= 1. Both are cases where the
  decoder (`item (sep item)*`) genuinely disagrees with the denotation.

## Key capture-model fact (bites structured/rep values)

`decode` records captures under nonterminal NAMES, only via the `ref` case. Consequences:
- A bare top-level terminal (`Adj ::= bit+`) records NO name-keyed capture — wrap it in a
  named sub-production (`Adj ::= Cells; Cells ::= bit+`) so `Cells` holds the span.
- `CaptureMap.toEnv` uses `find?` → returns the FIRST match, so repeated elements of a `rep`
  collapse. The rep's item COUNT is captured under `<Item>#count`; the individual repeated
  element values are NOT individually addressable yet. (See next steps.)

## Open next steps (discussed, not yet done)

1. **rep-element capture exposure** — let structured values read individual repeated elements
   (and expose `#count` to the `constraints'` escape by name, e.g. a `count(X)` primitive or
   `#`-key access). Unlocks: arbitrary-order graphs via `rep` + a triangular-count constraint;
   per-element value constraints. Most-requested increment.
2. **Add Mathlib** — swap the hand-rolled `Graph` struct in `Examples/Graph` for real
   `SimpleGraph (Fin n)` / adjacency `Matrix`. Mathlib master currently needs toolchain
   ~v4.33.0-rc1 → a deliberate toolchain bump (do it as its own step; expect some proof drift).
3. **DIMACS CNF example** — the actual SAT-solver input format (space-separated signed-int
   clauses, `0`-terminated, `p cnf` header). Squarely in the full-automation tier; a good test
   of whether `rep … sepBy` wants a terminator variant (0-terminated vs separated).
4. **SCOPE.md** — document the layered ceiling (grammar = subclass of regular; constraints lift
   accepted language to any decidable; values any type) + the graceful-degradation gradient
   (full auto-proof → escape with manual value/constraint contract → hand-written decode).
5. Housekeeping: `FormatSpec/HACKATHON.md` is legacy from the origin repo — review/prune.

## Context on the SAT-graph thread (why the Graph example exists)

The conventional SAT representation of a graph is the upper-triangle of its adjacency matrix
as a space-separated bit assignment (the model read back from a Ramsey/coloring instance). The
`Examples/Graph` example parses that into a structured graph value. "One grammar for all
orders" is achieved by a `bit+` grammar (any length) + a triangular-number constraint (carves
out valid lengths) + a value that recovers `n` from the length — demonstrating the
grammar-over-approximate / constraints-carve / value-interpret split. NOTE: DIMACS clauses are
the *solver input* (distinct from the graph *assignment*); graph6 (6-bit packed) is the dense
on-disk graph format and is a data-dependent-length case (out of grammar scope → hand-written
decode).
