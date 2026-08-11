# Design Note: Grammar-to-Specification Compiler for Cedar Extension Parsers

Status: implemented (design 2026-07; the `triptych` command, engine, emitted
equivalence/decidability proofs, and the six examples all build under Lean v4.31.0).
This note captures the design developed while verifying the Cedar extension-type
parsers (`Decimal`, `Duration`, `Datetime`, `IPAddr`). It describes the current
implementation; future work is labeled explicitly and tracked in `ROADMAP.md`.

The repository has three explicit package boundaries: the root `Triptych` core,
`other-examples/` for Cedar-free worked examples, and `cedar-examples/` for the five
Cedar-backed examples, bridges, external-parser proofs, and conformance suite. The core and
other-examples package therefore has no cedar-lean dependency.

## 1. What the tool is (and is not)

**It is** a *grammar-to-specification compiler*: given an (informal) grammar for a
flat, non-recursive string format, it deterministically generates the Lean
**specification** for that format plus the **contract theorem surface**. It also
emits its OWN correct-by-construction reference parser (`gatedParse` = `computeValue`
gated on the decidable acceptance predicate) and discharges that parser's
sound/complete/reject contracts for free — so every generated spec ships a verified
reference parser, not merely an obligation surface.

**It is not** a verified *production* parser generator. The reference parser is the
decode-backed engine — simple and obviously-correct, not optimized (no streaming,
error recovery, or complexity theorem). The tool's distinctive job is to validate a
*separate, external, hand-written* parser (e.g. the `Std.Time`-based `Datetime.parse`,
or the `splitToList`-based `Decimal.parse`) against the generated spec, via the
`SoundStmt`/`CompleteStmt`/`RejectStmt` obligations. The optional Cedar companion package's
conformance suite differential-tests the generated engine against the real Cedar parsers.

This places the tool beside, not upstream of, Narcissus/EverParse: those generate an optimized
implementation plus proofs from a format; we generate the verification **target**, a proved
reference parser, and faithful contract statements for an independent implementation.

## 2. The class of grammars

The Cedar ext parsers are all **flat regular attribute grammars**:

- **Non-recursive** — the nonterminal dependency graph is a DAG (no
  self-reference). Consequence: the least-fixed-point denotation collapses to a
  finite first-order formula with *bounded* quantifiers. No `inductive` relation
  is needed; a plain `def ... : Prop` suffices. (Contrast: JSON / Cedar policy
  grammars are recursive and *require* an inductive `Derives` relation.)
- **Regular, not finite** — datetime is finite (all fields fixed-width), but
  decimal (`left` unbounded) and duration (`digits+`) are infinite. Iteration appears
  both in character-class token runs (`digit+`, `hexDigit{1,4}`) and in separated
  group repetition (`rep H16 sepBy ":" {8}`). Both forms remain regular and are
  represented explicitly in the grammar AST.
- **Decidable recognition** — regular + decidable leaf predicates + bounded ∃
  ⟹ `DecidablePred IsWf`. This is *why* the parser can be a total boolean-guarded
  function instead of a fuel-bounded recursive descent.

## 3. The layered specification

A format induces a flat accepted-value relation `R ⊆ Value × String` (as in Narcissus, but
here it is a `Prop`, not an inductive type). The public operations expose its layers:

- `IsWf str` recognizes grammar layout plus capture-only constraints;
- `computeValue str : Option Value` evaluates the selected decode, whether or not final-value
  constraints hold;
- `IsValid str` combines `IsWf` with those final-value constraints;
- `parse str` gates `computeValue` with executable validity.

The selected value is grammar-determined only when the full parses agree on the captures it
reads. Syntactic unambiguity is sufficient but not necessary: several parses may be
value-coherent because the value function ignores their differences. Conversely, recognition
correctness alone says nothing about capture/value coherence.

The implementation makes this explicit in `Triptych.Theorems.Coherence`: `fullParses` names
every operational full parse; `CaptureCoherent`/`EnvCoherent`/`ValueCoherent` separate map,
scalar-view, and value agreement; `DecodesAs` is the grammar/value relation; and `Denotes`
additionally relates per-parse acceptance constraints to the value. Under `FormatCoherent`,
`decodeGatedMap_eq_some_iff_denotes` proves that first-match execution realizes the relation.
`DecodeUnique` states a decidable sufficient condition; `#eval decide` checks a concrete input
at runtime, while the coherence theorems consume a proof. `GrammarCaptureFunctional` lifts
capture coherence to all inputs and is the exact grammar-level property needed by arbitrary
capture constraints and value readers. A stronger static all-input certificate
(`GrammarDecodeUnique`) can now be synthesized for the conservative `Grammar.staticUnique`
fragment: unary reference paths, required sequences whose intermediate symbols have unique
prefix matches, and sequence-unique alternatives with pairwise-distinct direct literal
leaders. Literals and exact-width token runs satisfy the prefix condition; the final symbol may
be a unary variable-width path because only full consumption matters there. A variable-width
unary token path may also precede a literal delimiter outside its token class. The checker
handles a leading `X ::= ["lit"]` reference when the unique remainder excludes `lit`'s first
character, which certifies Decimal's optional sign without assigning priority to it. For
grammars in this fragment, the DSL emits `grammarDecodeUnique`, derives
`grammarCaptureFunctional`, and, when a value exists, emits `grammarValueCoherent` and
`parse_iff_denotes`; Graph and Decimal receive all four. Relational parser contracts consume
only capture functionality. Extending the checker to recursive FIRST sets, shared-prefix
alternatives, general nullable sequences, and repetitions requires stronger split/disjointness
reasoning.

Neither is "the compose side" nor "the decompose side" — they are two readings of
one relation. The implemented relation has explicit layout, capture-constraint, value, and
final-value-constraint parts:

```
R m v str  ≡  Layout m str
           ∧ WfConstraints m
           ∧ v = valuation m
           ∧ ValueConstraints m v
```

- **`Layout`** is the grammar denotation and capture decomposition.
- **`WfConstraints`** contains capture-only rules such as canonical spelling, octet bounds,
  datetime field bounds, and IPv6 group counts. `IsWf` combines this phase with layout.
- **`valuation`** is either the scalar `value` AST or the supplied typed `value'` function.
- **`ValueConstraints`** contains rules that explicitly mention the final `value`, such as the
  Decimal and Duration `Int64` range. `IsValid` combines this phase with `IsWf`.

The split is syntactic and predictable: arithmetic over captures remains in `IsWf`; only an
explicit final-`value` reference moves a rule to `SatisfiesConstraints`.

## 4. `computeValue` = `Option.map valuation ∘ decode`

```
computeValue s = (decode s).map valuation
  decode    : String → Option CaptureMap  -- synthesized from the grammar
  valuation : CaptureMap → D              -- scalar DSL or typed `value'` function
```

- **`decode` is free and verified-by-construction.** The generic roundtrip theorem proves
  `decode s` succeeds exactly when the grammar denotation accepts `s`. Each generated
  production also has a typed `Derivation` with `render`, `Valid`, and exact capture
  construction. A valid root derivation belongs to `fullParses`; capture functionality
  strengthens that membership result to exact `decode (render d) = capturesWith d`.
  String decomposition therefore remains generic library machinery rather than
  format-specific handwritten splitting.
- **`valuation` is the supplied attribute**, and its shape determines
  synthesizability (§5).

## 5. The synthesizability boundary (the core design idea)

An early design used fixed arity as a synthesis boundary. Full IPv6 showed that this was too
strict. The useful questions are:

1. **Structurally bounded decomposition** — variable-length pieces still have explicit grammar
   structure and recoverable boundaries.
2. **Collection facts** — analyzable constraints can refer to generated repetition counts, while
   typed escapes can inspect every repeated span.
3. **Value transparency** — scalar formulas are analyzable; structured reconstruction may use
   the typed `value'` escape.

The scalar `value` AST makes integer formulas inspectable. Semantics outside that AST use
typed escapes while keeping grammar recognition, decoding, and value reconciliation generated.

| Escape route | Example | What remains authored |
|---|---|---|
| `value'` | datetime epoch millis; IPv4/IPv6 `IPNet` | a typed Lean function over captures |
| `[X]` arguments to `value'` / `constraints'` | IPv6 `::` zero-fill; aggregate checks | a function over `List String` captures |
| `constraints'` | datetime calendar day bound | a decidable Boolean predicate over captures |

### Cedar ext types against the boundary
- **Decimal, Duration** — use the scalar `Int` DSL, value constraints, and `ofSpec`/`toSpec`
  conversions to Cedar's domain types.
- **IPv4** — uses `value'` to construct `IPNet` directly from four octets and an optional CIDR
  prefix.
- **IPv6, including `::`** — uses bounded separated repetitions, the analyzable
  `count H16L + count H16R < 8` constraint, and list-valued `value'` arguments for zero filling.
- **Datetime** — uses `value'` for epoch-millisecond calendar arithmetic and `constraints'`
  for the cross-field day bound.

All five Cedar examples retain automatic surface/engine recognition and value agreement.
Every declared external-parser or canonical-printer obligation is discharged in the shipped
`Outputs/*/soundness.lean` modules.

## 6. Boundary detection + typed escapes

The elaborator rejects grammar structures outside its regular, non-recursive class and provides
typed value/constraint escapes for semantics outside the analyzable scalar DSL. Compressed IPv6
does not require a custom decoder:

```lean
Compressed ::= [Left] "::" [Right]
Left       ::= rep H16L sepBy ":" {1,7}
Right      ::= rep H16R sepBy ":" {1,7}

constraints
  count H16L + count H16R < 8
```

The generated decoder, readable `IsWf`, reconciliation theorem, and verified parser remain
generic. Only the structured `List String → IPNet` reconstruction is supplied through
`value'`; its generated value-agreement theorem is still automatic.

## 7. Generated proofs and explicit obligations

Because the layout combinators are a closed, pre-verified library:

- **Auto-discharged (no `sorry`)** — the *grammar-generic* contract theorems:
  `toString_injective` and `normalize_eq_iff_parse_eq` once generated-parser roundtrip is known,
  plus `DecidablePred IsWf`. When a printer is declared, one format-specific `encode_view`
  witness and the generated `parse_eq_some_iff_view` theorem discharge
  `parse_toString_roundtrip`; acceptance and value equations are derived projections of the same
  witness. As implemented, the emitted surface⟺engine
  reconciliation is auto-discharged on **both** axes: `IsWf_equiv` /
  `decodeSome_iff_IsWf` (recognition) and `computeValue_eq` (the extracted value equals
  the readable `value` on the decoded captures). The value theorem holds for both tiers —
  the DSL `value` (reconciled via the reader-agreement lemmas) and the `value'` escape
  (surface and engine share the author's fn, so it is defeq).
  The emitter also projects the exact input and every capture read by a value or constraint
  into a typed `<Name>.View`. A grammar-wide must-presence analysis emits `String` for scalar
  captures present in every derivation, `Option String` for potentially absent captures, and
  `List String` for `[X]` repetition readers. Generated value and constraint functions convert
  an absent option to `""` only at their existing semantic boundary, preserving behavior while
  exposing syntactic absence to bridge proofs.
  The generated `decodeView_input` theorem anchors every successful view to its source string,
  `IsValid_view` packages recognition as successful `decodeView` plus `View.Valid`, and
  `computeValue_view` packages denotation as mapping `View.denotation` over that same view.
  `parse_view` writes the generated parser as the engine validity guard followed by typed-view
  denotation (and the declared `ofSpec` conversion, when present). `parse_eq_some_iff_view` and
  `parse_eq_none_iff_view` remove that guard for proofs: parser success is equivalent to one
  decoded valid view with matching denotation, while rejection means no such valid view exists.
  A declared external parser additionally receives `checkedExtParse`: it returns an external
  result only after the generated parser confirms acceptance and denotation equality.
  `checkedExtParse_eq_some_iff`, `checkedExtParse_sound`, and
  `checkedExtParse_sound_view` are discharged without any theorem about the external
  implementation. This provides immediate soundness at the cost of running the reference parser.
  Independently, each grammar production is compiled to a typed structural derivation:
  alternatives are constructors, optional symbols are `Option`, repetitions are `List`, and
  references contain child derivations. The spec exposes `render` and `Valid`; the parser
  exposes exact `capturesWith` and proves every valid start derivation belongs to `fullParses`.
  Capture functionality then upgrades membership to exact `decode (render d) = capturesWith d`.
  The root derivation also has `toView`, and the corresponding `decodeView_render` theorem
  identifies its flat value/constraint view exactly.
  This keeps ambiguity honest: full-parse membership is unconditional, while decoder equality
  names precisely the coherence premise that makes enumeration order irrelevant.
  Static proof automation has two extensible, kernel-checked registries. `triptych_parser`
  contains oriented normalization rules, and `triptych_parser_search` contains facts suitable
  for E-matching and saturation. `triptych_sound` exposes supported successful `Option` paths;
  `triptych_auto [rules...]` gives format-specific facts priority, normalizes the context, then
  runs bounded `grind` search. Backend rules cover binds, maps, alternatives, filters, guards,
  and conditionals. Unsupported operations or missing semantic correspondences remain visible
  in the residual goal instead of being trusted. In the Cedar examples this automatically
  derives external soundness, completeness, and typed-view forms from the substantive
  parser-agreement and rejection facts. `triptych_encode` separately performs deterministic
  composition from a printer roundtrip, parser agreement, and the generated acceptance/value
  view theorems to `encode_view`; converted denotations require an explicit fifth inverse fact.
  `triptych_encode_direct` performs the same composition from direct generated-spec acceptance
  and value facts, requiring no external parser. `triptych_encode_derivation` instead consumes
  the generated root `decodeView_render` theorem and an `EncodeDerivationStmt`; it automatically
  projects structural validity, rendering, and denotation into `encode_view`.
  `DerivationPrinter` packages a `toDerivation : Value → RootDerivation` with structural,
  view-validity, and denotation-preservation proofs. Its `toString` and generic parser roundtrip
  are automatic. Distinct certificates may select distinct canonical presentations. Deriving
  such a certificate from arbitrary Lean in a `value'` escape is not automatic.
  Once the external obligations are proved, matching `extparse_eq_some_iff_view` and
  `extparse_eq_none_iff_view` theorems derive the same relations for the external parser. These
  normal forms remove the need to unfold `component`, `envOf`, constraint AST evaluation, value
  extraction, or generated parser gating after identifying a decode.
- **Emitted as scaffold placeholders** — `encode_view` for a declared canonical serializer,
  plus the optional external-parser bridge `extparse_sound`, `extparse_complete`, and
  `extparse_reject`. The printer witness cannot be inferred from an arbitrary Lean function, and
  the external contracts concern a hand-written implementation. Their statements are
  faithful-by-construction, while all generated-parser consequences are proved once in Triptych.
  A newly scaffolded file uses `sorry` until the author supplies those proofs; all shipped Cedar
  scaffolds have done so.

## 8. Parsing and printing from one description

The implemented compilation direction is:

```
triptych DSL
  ├─→ readable predicates + typed derivations (`spec.lean`)
  ├─→ executable decoder/parser + reconciliation proofs (`parser.lean`)
  └─→ external parser/printer contracts (`soundness.lean`, when requested)
```

Parsing is generated directly: `decode` enumerates full parses, `IsValid` gates the selected
value, and `parse` returns the denotation. Printing is certificate-driven because a grammar can
admit several valid presentations of one value. `DerivationPrinter` lets an author choose a
canonical root derivation and prove structural validity, view validity, and denotation
preservation; `render` then supplies the string and generic theorems supply parser roundtrip.
`printer auto` currently synthesizes this certificate for the total signed-decimal pattern in
either multiplication order.

Reverse extraction of a grammar from handwritten Lean and grammar-conformance reformatting are
not implemented features. Drift prevention instead comes from generating the readable surface,
engine, and their equivalence proofs from the same DSL input.

## 9. Novelty (honest placement)

The *pieces* are all published; the *seam* is the contribution.

- **Prior art:** Narcissus (ICFP'19), EverParse (USENIX'19), PulseParse (2025) —
  derive impl+proofs from formats (recursive/nested; inductive relations).
  Rendel & Ostermann, *Invertible Syntax Descriptions* (Haskell Symp. 2010) &
  FliPpr — one description → parser+printer via partial isomorphisms.
  Attribute grammars (Knuth 1968); *Synthesis of Semantic Actions in Attribute
  Grammars* (arXiv 2208.06916); *Inferring Attributed Grammars from Parser
  Implementations* (arXiv 2507.13117; reverse extraction, which Triptych does not implement).
  Verified regex w/ captures
  (lean-regex; ICFP'24 JS-regex mechanization — "captures turn recognition into
  segmentation" = our `IsWf` vs `decode` distinction).
- **Plausibly new:** (a) the analyzable scalar/typed-escape boundary, with graceful
  per-section degradation and auto-generated
  obligations; (b) deliberately restricting to the flat-regular class so the spec is
  a decidable `Prop` (no inductive apparatus) and generation is **total** (no proof
  search, never stuck); (c) typed derivations as a shared basis for direct printer certificates.
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
  *from* an implementation. Triptych does not implement this reverse direction.
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

**This is structurally identical to our design.** Our value semantics come from either the
scalar AST or a supplied `value'` function, and our constraints come from the constraint AST
or `constraints'`. When we prove
`parse_sound : parse s = some d → IsValid s ∧ computeValue s = some (toSpec d)`, we prove the
parser *realizes* those semantics — exactly CoStar++'s "faithfully realizes the actions."
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
`constraints` and `constraints'` first-class status rather than treating validation as a
bolt-on afterthought.

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
but `computeValue` (the VALUE function) is in the analyzable scalar DSL only for its supported
formulas. Calendar arithmetic (datetime → epoch-ms: `isLeapYear`, `daysInMonth`) and structured
collection reconstruction (IPv6 `::`) use typed value escapes. Non-recursive
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
in the design is Cedar-specific: the grammar/decoder roundtrip, scalar value DSL,
typed derivations, parser contracts, and printer certificates are all about *flat regular
string formats*. It applies to any Lean
project parsing scalars from strings — UUID, semver, ISO-8601, IPv4/v6, decimal/
currency, MAC, port, hex/base64, hostname. The deliverable:

> A reusable Lean library for **specifying and verifying flat string-format
> parsers** — the layer CoStar++ *delegates to you* (semantic actions/predicates
> over scalars) and Narcissus targets in *binary*. It fills the "verified textual
> scalar parsing in Lean" niche, which neither occupies. Write a one-line grammar →
> get `IsWf`, `IsValid`, `computeValue`, decidability, and a verified parser, with
> typed escapes for semantics outside the scalar DSL and explicit contracts for
> external parsers and canonical serializers.

Novelty = "occupies an empty, practically-important niche," not "new metatheory."

## 15. Strategic deployment choice

Triptych supports **verify what is shipped**: keep Cedar's hand-written extension parsers,
generate an independent reference parser and specification, and prove the external
implementations agree. If a project instead wants to replace a production parser, it should
evaluate a production-oriented verified generator and its performance model. Triptych's
generated parser remains a correct reference implementation, not a claim of streaming,
error-recovering, or complexity-bounded production parsing.

## 16. The implemented `triptych` DSL

`Triptych/Architecture/Syntax.lean` is the source of truth for this surface.

### 16.1 Generated predicates and value function

Constraints are split by whether they explicitly reference the final `value`:

```lean
IsWf                  s : Prop  -- grammar plus capture-only constraints
SatisfiesConstraints  s : Prop  -- final-value constraints, when present
IsValid               s : Prop  -- IsWf, or IsWf ∧ SatisfiesConstraints
computeValue          s : Option β
```

Empty phases are omitted. Without capture constraints, `IsWf` aliases the start-production
predicate. Without final-value constraints, `IsValid` aliases `IsWf`. The generated parser is
the executable `isValid` guard applied to `computeValue`, with an optional `ofSpec` conversion.
`IsValid_equiv`, `computeValue_eq`, and the parser contracts connect the readable and engine
layers.

`Denotes g accept valFn s v` is the value/string relation: some full parse of `s` has capture
map `m`, `accept m` holds, and `valFn m = v`. When static capture functionality succeeds, the
DSL emits `parse_iff_denotes`; with `ofSpec`, its relational reader is `ofSpec ∘ valFn`.

### 16.2 Decidability

`IsWf`, `SatisfiesConstraints`, and `IsValid` are decidable for accepted DSL inputs.
The grammar and scalar constraint ASTs have executable Boolean interpretations, while each
`constraints'` entry is supplied as a Boolean function. Thus `decide (IsValid s)` is a
provably connected executable validator, independent of any external parser.

### 16.3 Sections and clauses

Section names are local tokens inside the `triptych` command, not global Lean keywords.
The implemented order is `grammar`, one of `value`/`value'`, `constraints`, `constraints'`,
`parser`, `printer`, and `to`.

```lean
triptych IPv4 where
  grammar
    V4Net  ::= V4Addr | V4Addr "/" Prefix
    V4Addr ::= Oct1 "." Oct2 "." Oct3 "." Oct4
    Oct1   ::= digit{1,3}
    Oct2   ::= digit{1,3}
    Oct3   ::= digit{1,3}
    Oct4   ::= digit{1,3}
    Prefix ::= digit{1,2}
  value'
    toIPv4Net Oct1 Oct2 Oct3 Oct4 Prefix
  constraints
    noLeadingZero Oct1
    nat Oct1 ∈ [0, 255]
    noLeadingZero Prefix
    nat Prefix ∈ [0, 32]
  parser ipv4Only
  printer ipNetToStr
  to "Outputs/IPv4"
```

- **`grammar`** defines a non-recursive DAG of productions with concatenation, finite
  alternatives, optional symbols, token runs, and separated group repetition. It generates
  readable predicates, the executable decoder, and typed derivation trees.
- **`constraints`** is the analyzable constraint AST. Capture-only entries contribute to
  `IsWf`; entries that mention `value` contribute to `SatisfiesConstraints`. Forms include
  `noLeadingZero`, string equality, arithmetic comparisons/ranges, and cardinality.
- **`constraints'`** applies arbitrary Boolean Lean functions to scalar capture strings and,
  with `[X]`, ordered lists of repeated captures. Scalar and list arguments may be mixed.
- **`value`** is the scalar `Int` expression AST described below.
- **`value'`** applies an arbitrary typed Lean function to scalar capture strings and,
  with `[X]`, ordered lists of repeated captures.
- **`parser`** names an external `String → Option δ` implementation to validate.
- **`printer`** names a canonical serializer, or `printer auto` requests synthesis for a
  supported invertible scalar pattern.

### 16.4 Scalar values and typed escapes

The deep `ValExpr` AST is intentionally small. It returns `Int` and supports integer literals;
`nat X`, `int X`, `len X`, and `count X`; dedicated sign captures; unary negation; and
`+`, `-`, `*`, and `^`. It does not currently contain conditionals, comparisons, constructors,
or local helper definitions.

| Surface | Result | Analysis and reconciliation |
|---|---|---|
| `value <expr>` | `Int` | inspectable `ValExpr`; surface/engine value agreement generated |
| `value' f X [Y]` | any type | arbitrary Lean function; agreement generated because both layers use `f` |
| `constraints <expr>` | `Prop`/`Bool` interpretation | inspectable constraint AST; equivalence generated |
| `constraints' f X Y` | `Bool` | arbitrary Lean predicate; equivalence generated from the shared function |

The prime marks an escape from the small AST, not an unverified value contract. Grammar
recognition, decidability, typed views, and value reconciliation remain automatic. What is
not inferred from an arbitrary `value'` function is its inverse: a canonical printer still
needs an explicit `encode_view` proof or a `DerivationPrinter` certificate.

### 16.5 IPAddr as the boundary case

The IP grammars exercise both structural and semantic boundaries:

1. CIDR **prefix** spelling and bounds are capture constraints (`0..32` or `0..128`).
2. An absent prefix is interpreted by `toIPv4Net`/`toIPv6Net` as the full-width prefix.
3. IPv4 octet bounds and canonical decimal spelling remain analyzable constraints.
4. IPv6 `::` uses optional left/right separated repetitions and the analyzable
   `count H16L + count H16R < 8` rule.
5. Both formats use `value'` to construct a single structured `IPNet`; IPv6 receives repeated
   hextets as `List String`.
6. Both declare Cedar family parsers and canonical serializers, and all generated scaffold
   obligations are discharged.

The generated capture name is `Prefix`, matching Cedar's CIDR terminology. Lean fields that
would otherwise be named `prefix` are emitted as `«prefix»` because `prefix` is a Lean keyword.

### 16.6 Value and domain types

There is no universal `computeValue : String → Int`. The generated type follows the selected
value tier:

```lean
-- scalar `value`
computeValue : String → Option Int

-- structured `value'`
computeValue : String → Option β
```

The scalar DSL computes in arbitrary-precision `Int`, allowing Decimal and Duration overflow
to be expressed as final-value constraints. `ofSpec : β → δ` optionally maps an accepted scalar
spec value into the generated parser's domain result. `toSpec : δ → β` maps a domain or external
parser result back for comparison. Their accepted-range inverse obligation prevents lossy
conversions such as unchecked `Int64.ofInt` wrapping.

Structured values need no per-component surrogate. IPv4 and IPv6 construct `IPNet` directly in
`value'`, so their `computeValue` is `String → Option IPNet`; the omitted `toSpec` defaults to
`id` when comparing Cedar's external result with that same value.

### 16.7 Closed analysis, open semantics

The small scalar AST exists so recurring arithmetic can be inspected and synthesized. The
escape sections preserve generality without pretending arbitrary Lean code is analyzable:

- use `value`/`constraints` for supported scalar operations;
- use `value'`/`constraints'` for arbitrary typed semantics;
- add a DSL constructor only when an operation recurs and has useful generic laws;
- provide an explicit printer proof or derivation certificate when inversion is semantic.

This division is visible in the Cedar examples: Decimal and Duration stay in the scalar tier;
Datetime uses both escapes; IPv4 and IPv6 use structured `value'`; all still receive generated
recognition, decidability, typed-view, value-agreement, and verified-parser theorems.
