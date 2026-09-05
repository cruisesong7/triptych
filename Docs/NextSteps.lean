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

The previous chapter described Triptych's current boundary. This chapter records the completed
scanner replacement and then turns the remaining boundary into two development tracks. Better
automation reduces proof effort around the existing artifacts. Broader grammar coverage changes
what the DSL can express.

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

# Scanner backend and performance

The original executable engine was also the proof-oriented reference decoder. It materialized
lists containing every candidate split, filtered them for complete parses, and selected the
first result. That definition is easy to inspect, but it performs work and allocation that a
generated parser does not need.

Generated parsers now use {name}`Triptych.scan`. Its continuation-based search discards a failed
candidate immediately and stops at the first complete parse. It covers every current grammar
form, including quoted strings and separated repetition. Grammars accepted by
{name}`Triptych.Grammar.staticUnique` also receive a boundary-driven path that avoids candidate
prefix enumeration.

The old {name}`Triptych.decode` remains executable as an archived reference semantics. It is not
a runtime fallback. The replacement is justified by a grammar-generic theorem:

```lean (name := scannerAgreement)
#check @Triptych.scan_eq_decode
```

The proof first shows that scanning each symbol, sequence, and production is exactly ordered
{name}`List.findSome?` over the reference candidates. Therefore both engines choose the same
capture map, including for ambiguous grammars where ordering matters. Existing readable
specifications, values, constraints, and parser contracts are unchanged.

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

The scanner now also exposes a proof-only cost profile. It counts complete root candidates that
reach the final empty-suffix check. The profile is proved to return exactly the complete
scanner's result:

```lean (name := scannerProfileAgreement)
#check @Triptych.scanSearchProfile_result
```

For every grammar and input, the checked candidates are bounded by the finite candidate tree:

```lean (name := scannerCandidateBound)
#check @Triptych.scannerCandidateChecks_le
```

When the certified fast path succeeds, no complete-candidate backtracking occurs:

```lean (name := scannerFastPathCost)
#check @Triptych.scannerCandidateChecks_eq_zero_of_fastScan
```

This formalizes the search guarantee without hiding the hard case. An ambiguous grammar can
have an exponential candidate tree, so Triptych does not claim a grammar-wide polynomial bound.
The theorem is about scanner search choices, not compiler-specific wall-clock time or allocation;
those remain benchmarked empirically.

The paired benchmarks run the scanner and reference decoder on the same input and verify that
both accept the same number of iterations. One arm64 development-build run produced:

* Graph K8, 28 characters, 1,000 parses: 2,084 us versus 31,355 us, or 15.0x faster,
  with 0 of 28 complete candidates checked;
* Graph K16, 120 characters, 250 parses: 1,562 us versus 103,394 us, or 66.1x faster,
  with 0 of 120 complete candidates checked;
* Graph K32, 496 characters, 25 parses: 564 us versus 152,855 us, or 270.7x faster,
  with 0 of 496 complete candidates checked;
* Decimal, 1,000 parses: 2,876 us versus 18,660 us, or 6.4x faster, with 0 of 4
  complete candidates checked;
* full IPv6, 100 parses: 2,902 us versus 52,774 us, or 18.1x faster, with all 4
  complete candidates checked; and
* compressed IPv6, 100 parses: 16,445 us versus 20,679 us, or 1.2x faster, with all 13
  complete candidates checked.

Run {lit}`lake exe parser_benchmark` in {lit}`other-examples/` and
{lit}`lake exe scanner_benchmark` in {lit}`cedar-examples/` to reproduce the comparison.
Timings vary by machine and build mode, so CI treats these as smoke measurements rather than
fixed thresholds. The important correctness evidence is {name}`Triptych.scan_eq_decode`; the
measurements explain why the scanner is now the runtime engine.

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
