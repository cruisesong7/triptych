/-
Triptych documentation -- Chapter 5: next steps.
-/
import VersoManual
import Outputs.Decimal.parser

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "Next steps" =>

%%%
tag := "next-steps"
shortTitle := "Next steps"
file := "next-steps"
%%%

```lean -show
open Triptych
open CedarExamples.Decimal
```

The previous chapter described Triptych's current boundary. This chapter turns that boundary
into three development tracks, ordered by how much of the system they change. Better automation
reduces proof effort around the existing artifacts. A faster backend changes parser execution
while preserving the same specification. Broader grammar coverage changes what the DSL can
express.

# Generalizing automation

The current tactics remove parser decomposition and bookkeeping after format-specific semantic
facts have been named. This track should broaden that reusable proof layer while keeping search
bounded and leaving domain meaning explicit:

1. add terminating registry rules for more common parser combinators while keeping search
   limits explicit;
2. provide reusable semantic components for bounded integers, separators, and canonical numeric
   text;
3. extend derivation-based printer synthesis beyond the first signed-decimal shape; and
4. report missing registry facts and generated proof obligations directly at the failed goal.

Each extension should have a focused theorem-level test and at least one complete format proof.
Success means fewer repeated proof steps and clearer failures, without changing the generated
parser or allowing automation to manufacture semantic facts.

# Faster executable parsers

The generated {lit}`parser.lean` names {lit}`decodeView`, {lit}`computeValue`, {lit}`parse`, and
their contracts. These definitions are executable, but the current engine is designed first as
a transparent reference decoder: it enumerates possible splits and chooses the first complete
parse. Its performance has not yet been characterized as an optimized parser.

The reference decoder exposes the bounds that make this search total:

```lean (name := budgetApi)
#check @Triptych.decodeBudget
#eval Triptych.decodeBudget Decimal.grammar "12.34"
```

{name}`Triptych.DecodeBudget.referenceDepth` counts grammar productions,
{name}`Triptych.DecodeBudget.repetitionDepth` is the input length, and
{name}`Triptych.DecodeBudget.terminalPrefixCandidates` is input length plus one. These are exact
search limits, not a runtime complexity theorem: separate choices can multiply into many
backtracking branches.

The current {lit}`parser_benchmark` smoke test repeatedly parses complete-graph inputs at orders
8 and 16. It detects gross execution failures but has no timing threshold. This track should:

1. establish reproducible benchmarks and performance thresholds;
2. specialize deterministic grammar fragments to avoid unnecessary split enumeration; and
3. prove that the optimized backend agrees with the same readable specification and parser
   contracts.

The reference decoder can then remain a simple executable oracle, while applications use the
optimized backend.

# Broader grammar coverage

The first two tracks improve formats that Triptych already supports. Grammar work changes the
accepted DSL itself, so it should proceed incrementally. Each step removes a different current
restriction and asks more of the parser backend and proof generator:

1. *Broader static certificates.* The conservative
   {name}`Triptych.Grammar.staticUnique` checker certifies deterministic fragments such as Graph
   and Decimal. Shared-prefix alternatives, nullable sequences, and more repetition shapes need
   broader capture-functionality certificates before they can receive the same premise-free
   roundtrip theorems.
2. *Character classes and repetition.* General Base64 needs user-defined finite character
   classes or unseparated repetition of a 64-way symbol, together with quartet and padding
   constraints. The value tier can already host a decoder once the grammar can split and
   validate the text.
3. *Dependent field boundaries.* Constraints can reject a decoded string but cannot change how
   it was split. Graph6 is a representative next case because its header determines the length
   of the following payload.
4. *Recursive productions.* JSON, s-expressions, and Cedar policies require recursive grammar
   support. Until it exists, these formats need a hand-written parser and a separately proved
   specification.

Recursive productions are the point where Triptych may need a different parsing model rather
than another local grammar extension. The design study should compare three relevant systems:

* [The verified LL(1) generator](https://doi.org/10.4230/LIPIcs.ITP.2019.24),
  *A Verified LL(1) Parser Generator* (Lasser et al., ITP 2019), restricts the grammar to obtain
  deterministic parsing and termination.
* [CoStar](https://doi.org/10.1145/3453483.3454053),
  *CoStar: A Verified ALL(\*) Parser* (Lasser et al., PLDI 2021), generates verified parsers for
  recursive grammars.
* [CoStar++](https://doi.org/10.1007/978-3-031-33170-1%5F25),
  *Verified ALL(\*) Parsing with Semantic Actions and Dynamic Input Validation*
  (Lasser et al., NFM 2023), also incorporates semantic actions and dynamic input-validation
  predicates.

The comparison should evaluate grammar coverage, generated-parser performance, extraction and
integration costs, the trust boundary for user-supplied semantics, and whether an approach can
verify an existing parser rather than only the parser it generates.
