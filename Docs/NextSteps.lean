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

The previous chapters described Triptych's current boundary and verified scanner backend. The
remaining work falls into two development tracks. Better automation reduces proof effort around
the existing artifacts. Broader grammar coverage changes what the DSL can express.

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

# Broader grammar coverage

Automation improves formats that Triptych already supports. Grammar work changes the accepted
DSL itself, so it should proceed incrementally. Each step removes a different current
restriction and asks more of the parser backend and proof generator:

1. *A complete unambiguity check.* The conservative
   {name}`Triptych.Grammar.staticUnique` checker certifies deterministic fragments such as
   Decimal, but not DIMACS or LRAT, whose whitespace runs and leading-zero numerals need more
   than one character of lookahead. Because the grammars are non-recursive, ambiguity is
   decidable: compile the grammar to a capture-tagged automaton whose paths correspond to the
   reference decoder's parses, and search its product with itself for two accepting paths on
   one input. The certificate would give every unambiguous grammar premise-free roundtrip and
   relational-parser theorems, and the same automaton supports a linear-time parser tier.
2. *Character classes and repetition.* Inclusive ASCII ranges, {lit}`oneOf`/{lit}`noneOf`
   character sets, and separator-free repetition are now supported. General Base64 still needs
   quartet and padding constraints over a 64-way symbol.
3. *Dependent field boundaries.* The public dependent-width form now generates the complete
   artifact family for multiple literal-delimited fields, including internal fields, as
   exercised by BitRows. The verified {name}`Triptych.scanDependent` architecture handles the
   broader header-selected-tail model, and Graph6 exercises that path. The next step is lowering
   delimiter-free boundaries and header alternatives to that staged engine while retaining the
   same readable predicates, views, derivations, and parser contracts.
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
