# Design Note: Grammar-to-Specification Compiler for Cedar Extension Parsers

Status: exploratory design (2026-07). Not yet implemented. Captures a coherent
design developed while verifying the Cedar extension-type parsers
(`Decimal`, `Duration`, `Datetime`, `IPAddr`).

## 1. What the tool is (and is not)

**It is** a *grammar-to-specification compiler*: given an (informal) grammar for a
flat, non-recursive string format, it deterministically generates the Lean
**specification** for that format plus the **contract theorem surface**.

**It is not** a verified parser generator. We do not generate the parser
implementation, and we do not run proof search to prove the parser correct. The
parser (e.g. the `Std.Time`-based `Datetime.parse`, or the `splitToList`-based
`Decimal.parse`) stays hand-written and external.

This places the tool *upstream* of Narcissus/EverParse: those generate an
implementation + machine-checked proofs from a format; we generate the
verification **target** (the spec) and its **obligation surface** (the contract
theorems, some proved, some left as faithful `sorry`s).

## 2. The class of grammars

The Cedar ext parsers are all **flat regular attribute grammars**:

- **Non-recursive** — the nonterminal dependency graph is a DAG (no
  self-reference). Consequence: the least-fixed-point denotation collapses to a
  finite first-order formula with *bounded* quantifiers. No `inductive` relation
  is needed; a plain `def ... : Prop` suffices. (Contrast: JSON / Cedar policy
  grammars are recursive and *require* an inductive `Derives` relation.)
- **Regular, not finite** — datetime is finite (all fields fixed-width), but
  decimal (`left` unbounded) and duration (`digits+`) are infinite. The only
  iteration is a character-class Kleene-star **at the leaves** (digit runs), never
  at the grammar level.
- **Decidable recognition** — regular + decidable leaf predicates + bounded ∃
  ⟹ `DecidablePred IsWf`. This is *why* the parser can be a total boolean-guarded
  function instead of a fuel-bounded recursive descent.

## 3. The three-layer spec: `R = Layout ∧ Valid`

A format is a **relation** `R ⊆ Value × String` (as in Narcissus, but here it is a
flat `Prop`, not an inductive type). Both spec functions are *projections* of `R`:

- `IsWf str  :≡  ∃ v, R v str`      -- recognition = forget the value
- `computeValue str  :≡  the v. R v str`  -- evaluation = read R as a partial function
                                          -- (well-defined iff R is functional in v
                                          --  = non-malleability = unambiguous layout)

Neither is "the compose side" nor "the decompose side" — they are two readings of
one relation. `R` splits into two layers:

```
R v str  ≡  Layout v str    -- pure CFG: concatenation template + typed leaf tokens
          ∧  Valid v         -- extra-grammatical value constraints
```

- **`Layout`** — the context-free part. Generative form: `∃ caps, str = a ++ sep ++ b
  ∧ ⋀ tokᵢ capᵢ`. Fully mechanical to emit from the grammar template.
- **`Valid`** — the "human-forced constraints beyond CFG": `Int64` overflow,
  `tzOffsetMinsLt60`, `minsOffset < 60`, leap-second rejection. These are
  **refinement predicates on the decoded value** (cf. EverParse/PulseParse
  refinement types), *not* on the string. `parse_eq_none_iff`'s shape
  `¬IsWf ∨ (computeValue = some v ∧ outOfRange v)` is literally `¬Layout ∨ ¬Valid`.

## 4. `computeValue` = `valuation ∘ decode`

```
computeValue = valuation ∘ decode
  decode    : String → Option Captures   -- SYNTHESIZED + pre-verified from Layout
  valuation : Captures → D                -- the attribute (semantics); see boundary
```

- **`decode` is free and verified-by-construction.** It is the inverse of the
  layout's `asString`. Each layout combinator ships with a once-proven roundtrip
  lemma (`decode (asString caps) = some caps`). The `splitToList` / `takeEnd` /
  fixed-width `take` that `computeValue` needs is **selected** from a closed
  combinator library — never synthesized ad hoc — and comes pre-proven. This fully
  answers the "but computeValue needs splitToList" concern: the string
  decomposition lives entirely in `decode`, which is library machinery.
- **`valuation` is the supplied attribute**, and its shape determines
  synthesizability (§5).

## 5. The synthesizability boundary (the core design idea)

Two decidable, *syntactic* properties of the grammar determine whether a
production is fully synthesized:

1. **Fixed arity** — every field count is a literal (`4 groups`, `2 digits`).
2. **Affine valuation** — the value is `Σ fieldᵢ · constᵢ` (a positional numeral).

Positional numeral formats are affine *by construction* (`value = Σ digitᵢ · baseⁱ`),
so affinity dominates. You only escape it via a non-numeral semantics.

| Escape route | Example | Breaks |
|---|---|---|
| non-affine valuation | datetime → epoch millis (calendar) | `valuation` nonlinear |
| variable-arity decode | IPv6 `::` zero-fill | `decode` not a fixed split; induces data-dependent weights |
| non-affine constraint | Luhn / IBAN mod-97 checksum | `Valid` nonlinear (valuation still affine) |

### Cedar ext types against the boundary
- **Decimal, Duration** — fixed-arity, affine → fully synthesizable.
- **IPv4** — fixed-arity (4×base-256), affine, structured codomain `IPNet`
  (sum-of-products) → fully synthesizable. Codomain generality handled by making
  the positional combinator polymorphic over the accumulation
  semiring (`Nat`, `BitVec`, ...).
- **IPv6 fully-expanded** (8 groups, no `::`) → synthesizable.
- **IPv6 `::`** — variable-arity → **delegated** (see §6). Note `::` also threatens
  **non-malleability** (`::1`, `0::1`, `0:0:0:0:0:0:0:1` all denote one address);
  the hand-verification must prove `toString` emits a canonical (fully-expanded)
  form. IPAddr sits exactly on the frontier: affine value, but variable-arity decode.
- **Datetime** — fixed-arity but calendar valuation is non-affine → `valuation`
  supplied as trusted `Std.Time.toTimestamp`; everything around it synthesizes.

## 6. Boundary detection + typed-hole delegation

The elaborator classifies each production by the §5 syntactic checks *before*
emitting anything, and routes to synthesize-or-delegate. "Prompting the user" in a
Lean metaprogram = emitting a **typed hole** whose type is the contract:

```lean
-- SYNTHESIZED (fixed-arity core)
def IsWf_V4 ...        := ...   -- generated
def computeValue_V4 ... := ...  -- generated (affine)

-- DELEGATED (variable-arity `::`): typed hole, type = the spec of what to build
def decode_V6 (s : String) : Option (Vector (BitVec 16) 8) := by sorry
-- obligations emitted as named sorry'd statements:
--   decode_V6_roundtrip, decode_V6_canonical (non-malleability)

-- tool still synthesizes everything DOWNSTREAM of the hole:
def computeValue_V6 (s : String) : Option IPNet := (decode_V6 s).map valuation_V6
```

Plus a compile-time diagnostic listing which productions were synthesized vs
delegated and *why*. The manual `decode` must return the **fixed capture shape**
the synthesizer expects (`::` normalizes-to 8 groups), which keeps the
synthesized/manual seam type-safe.

## 7. What is generated free vs left as `sorry`

Because the layout combinators are a closed, pre-verified library:

- **Auto-discharged (no `sorry`)** — the *grammar-generic* contract theorems:
  `toString_injective`, `normalize_eq_iff_parse_eq` (generic over any
  `VerifiedParser`), `parse_toString_roundtrip` (reduces to combinator roundtrip
  lemmas), and `DecidablePred IsWf`. As implemented, the emitted surface⟺engine
  reconciliation is auto-discharged on **both** axes: `IsWf_equiv` /
  `decodeSome_iff_IsWf` (recognition) and `computeValue_eq` (the extracted value equals
  the readable `value` on the decoded captures). The value theorem holds for both tiers —
  the DSL `value` (reconciled via the reader-agreement lemmas) and the `value'` escape
  (surface and engine share the author's fn, so it is defeq).
- **Emitted as `sorry`d statements** — the *parser-specific* bridge:
  `parse_sound`, `parse_complete`, `parse_eq_none_iff`. These relate the generated
  spec to the **hand-written, external** parser (`Std.Time`, `splitToList`), so they
  cannot be free. Crucially, the *statements* are faithful-by-construction (generated
  from the same `R`), so the human can't accidentally state the wrong bound/disjunct.

Prerequisite refactor: extract a `VerifiedParser α` bundle (`IsWf`, `computeValue`,
`parse`, `encode`, `toString` + the 4 obligations) and prove the generic tail
(`roundtrip`/`injective`/`normalize`) **once**. Today those ~40 lines are copy-pasted
across `Decimal.lean` and `Duration.lean`. The macro generates *instances* of this
bundle, so the bundle must exist first.

## 8. Two directions (the tool is invertible)

- **Direction 2 (codegen):** grammar → `Grammar.lean`. This is `⟦·⟧`.
- **Direction 1 (extraction):** `Grammar.lean` → grammar. This is `⟦·⟧⁻¹`, and it
  **validates** Direction 2: regenerate `Duration/Grammar.lean` from its extracted
  grammar and check *definitional equality* against the hand-written original.
  Extraction also bootstraps the grammar corpus from the existing specs.

Related but distinct idea: a **grammar-conformance reformatter** — reorder/rename a
Lean spec's *declarative* sites (`Components` fields, `∧`/`∨` conjuncts, `asString`
`++` order, `-- ANCHOR:` sections) to read like an informal grammar. Correctness
condition: every rewrite is at a **commutative** site (∧, ∨, field order) OR carries
a defeq/equivalence obligation. `++` order, positional indices (datetime char 17/18),
and `splitToList` arm order are **sequential** — must not be blindly reordered. Run
this way, the reformatter doubles as a **grammar/spec drift detector**.

## 9. Novelty (honest placement)

The *pieces* are all published; the *seam* is the contribution.

- **Prior art:** Narcissus (ICFP'19), EverParse (USENIX'19), PulseParse (2025) —
  derive impl+proofs from formats (recursive/nested; inductive relations).
  Rendel & Ostermann, *Invertible Syntax Descriptions* (Haskell Symp. 2010) &
  FliPpr — one description → parser+printer via partial isomorphisms.
  Attribute grammars (Knuth 1968); *Synthesis of Semantic Actions in Attribute
  Grammars* (arXiv 2208.06916); *Inferring Attributed Grammars from Parser
  Implementations* (arXiv 2507.13117 ≈ our Direction 1). Verified regex w/ captures
  (lean-regex; ICFP'24 JS-regex mechanization — "captures turn recognition into
  segmentation" = our `IsWf` vs `decode` distinction).
- **Plausibly new:** (a) the synthesizability frontier as a *decidable syntactic
  classifier* with graceful in-grammar degradation via typed holes + auto-generated
  obligations; (b) deliberately restricting to the flat-regular class so the spec is
  a decidable `Prop` (no inductive apparatus) and generation is **total** (no proof
  search, never stuck); (c) affine-valuation as *the* decidable synthesis pivot.
- **Framing to defend:** *not* "more capable than Narcissus" (it proves things we
  don't; we generate the spec it assumes). Rather: **fully automatic generation of
  the verification target + obligation surface, where the restricted class makes
  generation total and partially self-proving.** Compete on the boundary, not on
  generality. For Cedar, this is the tractable warm-up for the eventual
  validated-policy-parser work (recursive grammar → verified generator or
  translation validation à la Jourdan-Pottier-Leroy).

## 10. Naming

Chosen handle: **"grammar-to-specification compiler"** (long form), **"spec
generator"** (short form). Rationale: emphasizes the *output is a logical
specification + proof obligations*, distinguishing it from a **parser generator**
(yacc/ANTLR/Menhir) whose output is a parser *implementation*. Avoid "grammar
compiler" as the primary name — it collides with the yacc mental model (a grammar
compiler *is* roughly a parser generator).

## 11. Relation to parser generators (and a literature novelty check)

**Parser generator** (yacc/bison, ANTLR, Menhir): grammar + semantic actions →
*parser source code*, offline at build time, no correctness guarantee. Our tool is
the mirror image: grammar → *spec + contract theorems* (logic, not code); the
parser stays hand-written and is verified *against* the generated spec. Same
offline grammar-in shape; opposite codomain (spec vs implementation).

Literature check (shallow — DuckDuckGo only; DBLP/SemanticScholar/arXiv APIs were
rate-limited/unreachable at time of writing, so this is NOT an exhaustive novelty
search and must be redone properly before any paper claim):

- **Verified parser *generators*** — Lasser, Casinghino, Fisher, Roux, *A Verified
  LL(1) Parser Generator* (ITP 2019) and *CoStar* (PLDI 2021) / CoStar++ (NFM 2023):
  grammar → *verified parser implementation*. LL(1)/CoStar are correctness relative
  to the *grammar* only (recognition + parse trees; NO semantic value). CoStar++ adds
  a semantic layer (values + constraints) but *definitionally* — see §13 for the
  confirmed details. They generate+prove the *implementation*; we generate the *spec*
  for a separate hand-written parser and target a flat-regular (not full CFG) class.
- **Correct-by-construction from formats** — Narcissus, EverParse, PulseParse:
  generate impl+proof from a format relation.
- **Opposite direction (spec inference)** — *Inferring Attributed Grammars from
  Parser Implementations* (arXiv 2507.13117); Daikon-style spec mining: infer spec
  *from* an implementation (≈ our Direction-1 extraction, not Direction-2).
- **Grammar-guided spec synthesis (NL)** — *Doc2Spec* (arXiv 2602.04892): LLM induces
  a spec grammar from NL then generates specs guided by it — spec output, but
  NL-driven and not machine-checked/parser-verification-oriented.

**Finding:** the specific cell — *deterministic generation of a machine-checked
logical spec + parser-contract proof obligations FROM a grammar, for a separately
hand-written parser, over a flat-regular class where generation is total* — appears
**unoccupied** in what was surveyed. Neighbors either generate impl+proof (verified
generators / Narcissus) or infer spec-from-impl (spec mining). Caveat: searches were
shallow; a real DBLP + Semantic Scholar sweep is required before asserting novelty.

## 12. Relation to Narcissus — NOT "upstream"

Tempting shorthand: "we're upstream of Narcissus" (our output = its input type).
This is **misleading** and should be avoided:
- Different provers (Narcissus = Coq, us = Lean); the interfaces do not connect.
- Narcissus input is a nondeterministic format relation in its own combinator DSL,
  built so its *derivation tactics* can chew on it. We emit a flat `Prop` spec +
  contract theorems around an *existing* parser. We do not emit a Narcissus-format.
- Narcissus *derives* the parser; we *keep* the hand-written parser.

Accurate framing: **same conceptual input (a grammar/format), different codomain.**
Narcissus → verified parser *implementation*. Us → *spec + obligations* for an
external parser. Not a pipeline; parallel tools with opposite deliverables. The
"upstream" phrasing wrongly implies we're a mere front-end whose real work is
downstream — our output is a complete, self-contained deliverable.

## 13. CoStar++ comparison (the sharpest neighbor) + the cost-accounting insight

CoStar / CoStar++ (Lasser, Casinghino, Fisher, Roux; PLDI'21 / NFM'23; branch
`predicates-and-actions`): a verified ALL(*) parser **generator** in Coq. Generates
its **own** parser for **recursive CFGs**, proved sound + complete + error-free once
∀ grammars, and the `predicates-and-actions` branch adds **semantic predicates**
(value constraints) and **semantic actions** (value computation), with a
Verbatim-based verified lexer.

On the axes it fights on, CoStar++ **dominates**: bigger grammar class (CFG ⊃
regular), values + constraints + full proofs, zero `sorry`. Do NOT frame our work as
"more novel" or "computes values from a grammar" — CoStar++ already does that.

**But two things reopen the gap, and they reinforce each other:**

**(A) Performance / integration mismatch for cedar-ext.** ALL(*) is an adaptive
LL(*) engine with per-decision DFA-simulation lookahead — machinery for *recursion
and ambiguity that cedar-ext formats do not have*. Running `"2.5"` / `"127.0.0.1"`
through it is massive overkill (linear but large constant). It extracts Coq→OCaml
and depends on CoLoR + Verbatim — a foreign runtime to embed in Lean/Rust. And the
hard cedar-ext semantics (calendar, overflow, `::`) are *actions you'd still write*.
Net: CoStar++ is the wrong tool to *produce* a useful/performant cedar-ext parser.
(Caveat: argued from algorithm class + base-CoStar benchmark shape, not measured
cedar-ext numbers.)

**(B) The cost-accounting insight — CoStar++ does NOT make our 2000 lines free.**
"Verified parser generator" conflates three costs:
  1. **Syntax** (string decomposition ↔ grammar) — CoStar++ meta-theorem makes this
     **free**. For cedar-ext this slice is *small* (trivial flat layouts).
  2. **Semantics** (base-conversion value, `Int64` overflow, calendar → epoch,
     non-malleability) — this is **~90% of our 2000-line `Lemmas.lean` cost**, and
     in CoStar++ it lives in **"prove your semantic actions/predicates correct"**.
     Same arithmetic content, NOT free.
  3. Integration (action fires at production) — CoStar++ machinery.

So CoStar++ eats the *cheap* slice (syntax) and charges you the *expensive* one
(semantics) regardless. Counterintuitive but decisive: for **recursion-heavy,
semantics-light** grammars (programming languages) CoStar++ is a huge win; for
**recursion-light, semantics-heavy** grammars (cedar-ext: trivial to parse, values
need real arithmetic) it saves the cheap part and leaves the 2000 lines intact as
action-correctness obligations. The `R = Layout ∧ Valid` split *is* this accounting:
no parser generator makes `Valid` (semantics) free.

**(C) Verify-existing-parser.** CoStar++ certifies only the parser it generates; it
has no notion of verifying a *foreign* hand-written parser. Given (A), this is the
*operative* reason, not a nicety: cedar needs its fast native parser verified
*because* the generated alternative is unusable here.

### 13.1 CONFIRMED: CoStar++'s values + constraints are DEFINITIONAL (correction)

Earlier drafts implied "we verify the value, CoStar++ doesn't." **This is false and
is hereby corrected.** Read the actual paper — Lasser et al., *Verified ALL(\*)
Parsing with Semantic Actions and Dynamic Input Validation* (NFM 2023), the
`predicates-and-actions` branch of CoStar. Confirmed from the abstract:

- Sound/complete/terminating **"with respect to a semantic specification"** that
  **"accounts for both predicates and actions."**
- **"It does not claim the user's actions are independently proven correct — rather,
  the interpreter is verified relative to a specification that incorporates them."**

So CoStar++ DOES have both semantic layers, but **definitionally**:
- **semantic actions** = the value function ("convert sequential inputs to structured
  outputs") — user-supplied, definitional;
- **semantic predicates / "dynamic input validation"** = value constraints, including
  **non-context-free** properties (bounds, cross-field) — user-supplied, definitional.

**This is structurally identical to our design.** Our `computeValue` is a user-supplied
value function; our `Valid`/range is a user-supplied constraint. When we prove
`parse_sound : parse s = some d → computeValue s = d.val.toInt`, we prove the parser
*realizes* `computeValue` — exactly CoStar++'s "faithfully realizes the actions."
Neither proves the value function is the "true" meaning; that is definitional in both.

Corrected consequence for positioning:
- **vs LL(1) / base CoStar:** DECISIVE difference — they have NO semantic layer
  (recognition + parse trees, grammar-relative only). Value function + constraints are
  entirely absent. Adding `computeValue` + `Valid` is real content they lack.
- **vs CoStar++:** NOT a difference in kind. They have definitional values (actions)
  and definitional constraints (predicates / dynamic input validation), just like us.
  We do **not** out-verify them on the semantic axis. Stop claiming "we have semantics
  and they don't" — against CoStar++ that is wrong.

Confirmed differentiators vs CoStar++ are ONLY:
1. **Flat decidable spec** — `IsWf` is a flat `Prop` with `DecidablePred`; no inductive
   `Derives`, no fuel/termination proof (their headline result is a non-issue for us),
   no ALL(\*) engine. An audit + infrastructure edge, from non-recursion — NOT a
   stronger guarantee.
2. **Verify an external hand-written parser** (§13-C) — they verify only their own
   generated parser. The one structural thing they cannot do.

Design takeaway borrowed FROM CoStar++: "dynamic input validation" frames the
**constraint predicate as a first-class part of the language spec, and it may be
non-context-free** (3 of their 4 benchmarks have non-CF specs). This validates giving
`Valid` first-class status in the DSL (a `constraint <term>` section), not treating it
as a bolt-on afterthought.

(Sourcing caveat: the two quotes are from the abstract + a secondary summary; the full
PDF was paywalled / had an expired TLS cert at time of writing. The definitional
reading is strongly supported by the abstract's explicit disclaimer but was not read
off the Coq theorem statements directly — confirm against the source if load-bearing.)

### 13.2 What LL(1) / CoStar actually verify (for the record)

- **A Verified LL(1) Parser Generator (ITP 2019):** soundness + completeness +
  **termination without fuel**, all relative to the grammar's derivation relation.
  Soundness = output is a valid derivation of `G`; completeness = if a derivation
  exists the parser finds it (accepts exactly `L(G)`). NO semantic value — recognition
  + trees. LL(1)-ness is the *restriction* enabling determinism + the termination
  proof. Their headline hard result (fuel-free termination) is FREE for us: a
  non-recursive grammar cannot diverge.
- **CoStar (PLDI 2021):** same shape for non-left-recursive CFGs — correct parse tree
  relative to the grammar, ambiguity detection, no semantic value.
- **The point:** their spec IS the grammar (an inductive `Derives` relation, because
  the grammar recurses). Guarantee = "accept exactly `L(G)`, output valid derivations,
  terminate" — purely SYNTACTIC. The *meaning* (value) is out of scope for LL(1)/CoStar
  entirely, and definitional in CoStar++.

### 13.3 What decidability of `IsWf` buys us (for the record)

Non-recursive ⟹ `IsWf` unfolds to a flat bounded `Prop` ⟹ `DecidablePred IsWf`. This
gives, concretely: (a) `decide (IsWf s) : Bool` is a *provably-correct executable
validator* — the spec doubles as an oracle; (b) bridge lemmas can `decide`/case-split
by computation instead of manual derivation (why the flat class needs less proof
infra); (c) it is the precise, *testable* formalization of "this grammar is in the flat
class" (a recursive `Derives G` is NOT decidable by structural computation on the
predicate); (d) executable differential testing of spec vs hand-written parser for
free, before any proof.

CORRECTION on "flatness": `IsWf` (recognition) is ALWAYS flat/decidable in this class,
but `computeValue` (the VALUE function) is flat only for **affine positional numerals**
(decimal, duration, IPv4). It is NOT flat for calendar arithmetic (datetime →
epoch-ms: `isLeapYear`, `daysInMonth`) or variable-arity (IPv6 `::`). Non-recursive
grammar ⟹ flat recognition; it does NOT ⟹ flat valuation. Two independent axes; do not
conflate them (earlier drafts loosely called `computeValue` "a flat arithmetic formula"
as a blanket claim — wrong).

## 14. The honest contribution + reusable-library framing

**Honest novelty verdict:** against CoStar++ as published research we add **no new
metatheory** — values (actions), constraints (predicates), full proofs all exist
there over a bigger class. Ours is an **engineering / tooling** contribution
("known ideas, new setting"), pitched to a tools/artifact track, never as advancing
parsing theory. Modest but real.

**The strongest true framing is a reusable Lean library, not a Cedar tool.** Nothing
in the design is Cedar-specific: the `VerifiedParser α` bundle, the layout-combinator
library with roundtrip lemmas, the affine-valuation synthesizer, and the fixed-arity
classifier are all about *flat regular string formats*. It applies to any Lean
project parsing scalars from strings — UUID, semver, ISO-8601, IPv4/v6, decimal/
currency, MAC, port, hex/base64, hostname. The deliverable:

> A reusable Lean library for **specifying and verifying flat string-format
> parsers** — the layer CoStar++ *delegates to you* (semantic actions/predicates
> over scalars) and Narcissus targets in *binary*. It fills the "verified textual
> scalar parsing in Lean" niche, which neither occupies. Write a one-line grammar →
> get `IsWf`, `computeValue`, `Decidable`, roundtrip, injectivity for free, with
> typed holes for the non-affine semantic actions it cannot synthesize.

Novelty = "occupies an empty, practically-important niche," not "new metatheory."

## 15. Strategic decision that gates all of this

The above only makes sense if **Cedar keeps its hand-written ext parsers** (verify-
what's-shipped). If Cedar were open to *replacing* them, one would evaluate a
CoStar++/Verbatim-style verified parser instead — though (A) argues it's a poor fit
for these formats regardless. Confirm the "verify existing parser" requirement is
firm before investing. This is the same replace-vs-validate fork as the eventual
Cedar policy-parser assurance work (verified generator vs translation validation).

## 16. The `triptych` DSL — decided design

(Decided over the design thread; supersedes earlier sketches in §6–§7. The doc
grammars / current formalization are NOT ground truth — they are a moving target we
may change to match this scheme.)

### 16.1 Three generated predicates + value function

The old `R = Layout ∧ Valid` is refined into a **three-predicate decomposition**,
split by the single question *"does the check depend on the value function?"*:

```
IsWf                 s : Prop   -- syntax: grammar structure + string-only rules
                                --   (e.g. widths, digit/hex-ness, noLeadingZero).
                                --   VALUE-FREE ⟹ DecidablePred IsWf unconditionally.
SatisfiesConstraints s : Prop   -- semantic constraints on `computeValue s`
                                --   (bound OR checksum OR cross-field relation —
                                --    deliberately NOT named "IsInBounds", to avoid
                                --    over-promising that every constraint is a bound).
IsAccepted           s : Prop  := IsWf s ∧ SatisfiesConstraints s
                                --   top-level; characterized by parser behavior:
                                --   IsAccepted s  ↔  (parse s).isSome
computeValue         s : D      -- the value function (D may be structured, e.g. IPNet)
```

Naming rationale: `IsAccepted` is defined by *what the parser does*, not an English
adjective, so it cannot drift. "valid" is avoided on both sides of the conjunction
(the earlier `IsValid = IsWf ∧ IsValid` was tautological-looking).

`Denotes v s := IsWf s ∧ computeValue s = some v ∧ SatisfiesConstraints v` is the
value↔string *relation* (the Narcissus/PulseParse "format"); `IsAccepted s ↔ ∃ v,
Denotes v s`. Keep `Denotes` a *conceptual* object — materialize it as a real def
only if a contract theorem needs the relation form.

Resolves a real inconsistency in the current specs: **Decimal** already keeps value
constraints OUT of `IsWfStr` (overflow is a separate disjunct of `parse_eq_none_iff`)
— matches this scheme. **IPAddr** currently folds `constraintsWf` (`≤ 255`) INTO
`IsWfV4` — does NOT match; under this scheme those move into `SatisfiesConstraints`.
Uniform rule: `IsWf` = syntax only, always.

### 16.2 Two-tier decidability (the creative edge)

- `IsWf` is decidable **unconditionally** (value-free, flat, bounded) — so
  `decide (IsWf s) : Bool` is a provably-correct executable validator, and an
  auto-generated differential test `∀ s, decide (IsWf s) = (parse s).isSome` runs
  against the external parser BEFORE any hand proof. Holds even for datetime/IPAddr,
  whose value functions are non-affine/structured.
- `IsAccepted` is decidable **iff** `SatisfiesConstraints` is — which, for bounds, it
  always is. So: recognition always decidable; acceptance decidable-modulo-value-
  constraints. Clean separation.

### 16.3 Section headers: `grammar` / `constraints` / `value`

Local section tokens inside the `triptych` command's own grammar (implemented as
literal atoms in the `syntax ... : command` rule) — NOT global keywords.
**`grammar`** is used instead of `syntax` because `syntax` is a reserved Lean keyword.

```lean
triptych IPv4 where
  grammar
    V4Addr ::= NumV4 "." NumV4 "." NumV4 "." NumV4
    NumV4  ::= digit{1,3}
  constraints
    noLeadingZero NumV4        -- string-only  → folds into IsWf
    nat NumV4 ≤ 255            -- value        → folds into SatisfiesConstraints
  value
    IPNet.V4 (CIDR.mk (bytes (nat NumV4) ...) ...)
```

- **`grammar`** → EBNF productions (named nonterminals, DAG). Produces the `IsWf`
  structure, `decode`, `asString`. Bounded repetition `{n}` desugars to literal
  repetition (stays fixed-arity); unbounded `*` (IPv6 `::`) triggers delegation.
- **`constraints`** → a *grouped block* (NOT inline `where`). Chosen over inline
  because IPAddr has **cross-production / whole-string** constraints (`'::' at most
  once`; `sides total < 8`; default-prefix) that have no single production to attach
  to. Each line is **auto-classified** by value-dependence: references only the
  capture string → conjoined into `IsWf`; references `nat`/`computeValue` → conjoined
  into `SatisfiesConstraints`. `noLeadingZero` is a built-in primitive
  (`startsWith "0" → s = "0"`), pervasive in IPAddr (`IsCanonicalNat`).
- **`value`** → the value function, written in a **flat first-order value-DSL**
  (readable, matches the doc's `value(X) = …`), NOT a raw opaque Lean term. This is
  the key divergence from CoStar++: they consume the value fn as a black box
  (`f vs`); we own the AST, so we can (a) translate it to `computeValue`, (b) analyze
  it for affinity, (c) auto-generate roundtrip/soundness proofs in the affine case.
  See §16.4.

### 16.4 The value-DSL: flat first-order, NOT restricted to affine

Expressiveness (can you write it?) and proof-tier (can we auto-prove it?) are
INDEPENDENT axes. Do not conflate (an earlier draft did):

- **DSL expressiveness = flat, non-recursive, total first-order.** Includes:
  field readers (`int X`, `nat X`, `len X`, `sign`), arithmetic (`+ - * ^`, lits),
  conditionals (`if`/`match` on optionals), comparisons/bool ops (`==`,`<`,`%`,`&&`),
  **data-constructor application** + **typed non-scalar output** (IPAddr's value is
  `IPNet`, not `Int` — the DSL must build sums/products), and **non-recursive named
  helpers** (`where isLeapYear(y) = …`, a local DAG mirroring the grammar's
  productions). This covers decimal, duration, IPv4, AND **datetime** (calendar
  arithmetic is non-affine but FLAT: `daysSinceEpoch·86400000 + …`, closed-form).
- **Proof tier = an analysis pass over the value-AST:**
  - *affine* (`Σ nat(fieldᵢ)·wᵢ`, coefficients possibly bounded-length-dependent like
    decimal's `10^(4-|Fraction|)`) → auto-generate `computeValue` AND its
    roundtrip/soundness proof. The ~2000-line hand-proof, automated.
  - *flat non-affine* (datetime) → `computeValue` generated + total + executable +
    decidable `IsWf` all still hold; only the roundtrip PROOF is a `sorry`/hand proof
    (calendar reasoning is irreducible).
  - *opaque escape* (`value opaque := <raw Lean term>`) → reserved ONLY for genuinely
    non-flat things (needing recursion/unbounded iteration). None of Cedar's ext
    types need it — datetime is flat, so it stays in the readable analyzable tier.

| Value written as… | readable? | computeValue | decidable/executable? | roundtrip proof |
|---|---|---|---|---|
| affine DSL | ✅ | generated | ✅ | **auto** |
| flat non-affine DSL (datetime) | ✅ | generated | ✅ | `sorry` (hand) |
| `opaque := <raw Lean>` | ✗ | generated (`∘ decode`) | ✗ | `sorry` |

### 16.5 IPAddr as the boundary case (6-bucket categorization)

IPAddr's many NL descriptions sort as: (1) bounds `≤ 255/0xffff/128` →
`constraints`/`SatisfiesConstraints`; (2) `noLeadingZero` → `constraints`/`IsWf`
(string-only); (3) default full-width prefix → `value` conditional; (4) "V4 tried
first" → ordered alternation in `grammar`; (5) base-256/65536 assembly → `value`
(affine, structured `IPNet` output); (6) **`::` gap** (unbounded `*`, variable arity,
data-dependent zero-fill; the doc's own `V6Components` goes *inductive* `full | gap`
with `∀ s ∈ list` folds) → **the one genuine escape**, delegated via typed hole. So
the DSL covers V4 + full-V6 + all constraints (synthesized), and detects-and-delegates
`::` alone. IPAddr sits half-in (synthesized), half-out (`::` delegated) — the case
that proves the fixed-arity boundary is real. Consequence: the value-DSL MUST support
structured (non-`Int`) output with constructor application; the contract-theorem
generator must handle structured value types, not assume a scalar `computeValue`
(the doc already notes IPAddr soundness is "phrased per witnessing components").

### 16.6 The value type: `computeValue : Int`, NO `package` layer (corrected)

A false start (now corrected): I proposed a `package : Int → Option D` layer to
"cast" the value into the format's real type (`Int64`, `IPNet`). **That layer is
unnecessary and is dropped.** The reasoning:

- **`computeValue` is `Int` (arbitrary precision), deliberately.** Computing in `Int`
  (not `Int64`) is REQUIRED: it yields the *true* mathematical value so overflow is
  *detectable*. If it computed in `Int64`, overflow would wrap silently and the value
  would already be garbage — you couldn't even state the overflow condition. (My
  `ValExpr.eval : Env → Int` is correct as-is for this reason.)
- **The `Int64` bound is a CONSTRAINT, not a cast.** "fits in `Int64`" ⟺ `Int64.ofInt?`
  succeeds ⟺ `Int64.MIN ≤ computeValue s ≤ Int64.MAX`. That is exactly a
  `SatisfiesConstraints` entry — and exactly the existing Decimal `parse_eq_none_iff`
  disjunct. So `Int64`-enforcement lives in `constraints`, as the user intuited.
- **The spec NEVER constructs `D`; it projects the parser's output DOWN.** The proposed
  `package` also did *construction* (build `Decimal`/`IPNet` from `Int`s) — but the
  spec never needs to. `parse_sound` compares `computeValue s : Int` against
  `d.val.toInt` — it takes the parser's *already-built* `d : D` and projects it *down*
  to `Int` via a projection `π : D → Int`. Construction is the *parser's* job;
  verification only reads the `Int` back out. So construction (the other half of
  `package`) evaporates too.

**Corrected value model — three pieces, no package:**
```
computeValue         : String → Int      -- ValExpr.eval ∘ decode; arbitrary precision
SatisfiesConstraints : String → Prop     -- includes Int64.MIN ≤ · ≤ Int64.MAX (the "cast" check)
IsAccepted           := IsWf ∧ SatisfiesConstraints
-- contract theorem: parse s = some d → IsAccepted s ∧ computeValue s = π d
--   where π : D → Int is a small PROJECTION (Int64 wrapper ↦ .toInt), used only in the
--   theorem STATEMENT, not a computational stage; derivable from D's structure.
```

- **Non-number / structured `D` (IPAddr → `IPNet`):** same principle. No construction on
  the spec side; instead **per-component** `computeValue`s + **per-component projections**
  (compare `nat g₀ = <octet 0 of d>`, …). Confirmed by the doc: IPAddr soundness is
  "phrased per witnessing components rather than through a single computeValue." So
  structured output needs multiple `Int`-valued `computeValue`s + a tuple projection,
  NOT a `package`/constructor layer in the spec.

Net: `ValExpr` stays scalar-`Int` (correct); `Int64` = a `constraints` bound; typed/
structured output handled by projecting the PARSER's result down to `Int`(s) in the
contract statement. The earlier `package` layer was construction the projection-based
contract makes unnecessary.

### 16.7 The expressiveness trilemma + the `opaque` escape (why a closed DSL is OK)

A deep-embedded DSL is by construction a **closed, small subset** — you can only
inspect/analyze what you deliberately put in the AST. This is not a wart; it is forced
by an unavoidable trilemma. You can have at most TWO of:

1. **Read any grammar off the bat** (arbitrary value/constraint expressiveness)
2. **Analyzable** (affinity detection, auto-proofs — the edge over CoStar++)
3. **Closed/small DSL** (no user extension needed)

- CoStar++ picks **1 + 3**: arbitrary raw functions, no DSL — but NOT analyzable
  (opaque `f vs`, definitional ceiling).
- Our deep DSL picks **2 + 3**: analyzable + closed — but NOT arbitrarily expressive.
- **1 + 2** (arbitrary AND analyzable) is essentially impossible — analyzing arbitrary
  computation is undecidable.

So "ideally read any grammar" and "the analysis edge that justifies the project" pull
in OPPOSITE directions — they are the same tension. The resolution is NOT to make users
extend the DSL, but a **tiered escape hatch** (the tiers of §16.4), so nobody is ever
blocked:

- **Tier 1** — DSL, affine → auto-proof.
- **Tier 2** — DSL, flat non-affine (datetime) → executable + hand-proof.
- **Tier 3** — `opaque := <raw Lean term>` → arbitrary Lean, = CoStar++ expressiveness,
  definitional (loses auto-analysis, keeps correctness-vs-spec). **This is the "read
  anything" answer.**

A grammar outside the DSL vocabulary does NOT hit a wall — its unexpressible pieces drop
to Tier 3 and get CoStar++-level treatment (no worse), while everything expressible stays
in Tier 1/2 with full analysis. Graceful degradation, per-piece.

**DSL extension** (adding a constructor to `ValExpr`/`Constraint`) is warranted ONLY for
a construct that is *recurring AND analyzable* (e.g. if many formats need `hex X` values).
The utility for extending is NOT a meta-DSL — it is (a) a documented ~5-edit recipe (AST
constructor + `eval` case + `syntax` rule + elaborator case + decidability case), and
(b) the deep AST itself: adding a constructor makes the compiler flag every non-exhaustive
`match` that needs a new case (in `eval`, the classifier, decidability) — type-directed
extension, a free benefit of deep embedding that shallow would not give. Extension is an
optional optimization, NEVER on the critical path, because Tier 3 always unblocks.

One-line framing: **the DSL is a fast path for the analyzable/common case; `opaque` is
the universal path; extension is an optional optimization for recurring analyzable
constructs, guided by the AST's exhaustiveness checking.**
