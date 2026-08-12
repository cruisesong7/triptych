/-
Triptych documentation -- Chapter 6: executable artifacts and foreign consumers.
-/
import VersoManual
import Outputs.Decimal.parser

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "Execution and export: what is standalone today" =>

%%%
tag := "execution"
shortTitle := "Execution and export"
file := "execution"
%%%

```lean -show
open Triptych
open CedarExamples.Decimal
```

Triptych already emits a specialized entry point for each value-producing format:

```lean (name := specializedParsers)
#check @Decimal.parse
```

Generated declarations have small public types such as
{lean}`(Decimal.parse : String → Option Int64)`. A caller does not pass
{name}`Decimal.grammar`, constraints, a value reader, or conversions.

# Specialized does not mean source-self-contained

The generated definition is intentionally short:

```
def Decimal.parse (s : String) :=
  Triptych.gatedParseOfSpec Decimal.IsValid Decimal.computeValue Int64.ofInt s
```

That is a specialized API, but not a single-file implementation. Its compiled dependency
closure still contains the generated grammar, decoder, validator, value function, and generic
Triptych runtime. Showing only this definition does not exhibit the whole executable needed to
parse.

There are three distinct artifacts:

1. *Specialized Lean function* -- available now as {lit}`<Name>.parse`.
2. *Linked Lean executable* -- straightforward to write as a small {lit}`main` importing one
   generated parser, but not yet emitted automatically per format.
3. *Flattened or foreign source implementation* -- not currently generated.

A compiled executable does not evaluate proofs at runtime; propositions and proof terms are
erased by Lean's compiler where computationally irrelevant. The proof remains valuable as the
kernel-checked certificate for the source function that was compiled.

# Readability of the emitted parser

The generated {lit}`parser.lean` is readable as a verification artifact: it names
{lit}`decodeView`, {lit}`computeValue`, {lit}`parse`, and their contracts. It is not an
optimized handwritten recursive-descent parser. The engine is a transparent reference decoder
that enumerates possible splits and chooses the first full parse.

For inspection, typed views and structural derivations are usually clearer than the raw engine.
For deployment, the public {lit}`parse` declaration is the intended boundary.

# Runtime budgets and benchmark evidence

The reference decoder is total. Its entry-point limits are exposed:

```lean (name := budgetApi)
#check @Triptych.decodeBudget
#eval Triptych.decodeBudget Decimal.grammar "12.34"
```

{name}`Triptych.DecodeBudget.referenceDepth` is the number of grammar productions,
{name}`Triptych.DecodeBudget.repetitionDepth` is the input length, and
{name}`Triptych.DecodeBudget.terminalPrefixCandidates` is input length plus one. These are
exact structural enumeration limits, not a polynomial total-runtime theorem: ambiguous
backtracking can still create many branches.

The Cedar-free {lit}`parser_benchmark` executable repeatedly parses complete-graph inputs at
orders 8 and 16. The checked smoke run accepts all 250 and 100 inputs respectively and reports
elapsed time with the three budgets. It has no timing threshold yet, so it detects gross
execution failures rather than promising a performance envelope.

# A standalone program

The next compiler artifact should package one format behind a stable protocol, for example:

```
stdin:  {"input":"1.5"}
stdout: {"ok":true,"value":15000}
```

Its reproducible test should compare the executable protocol with the in-Lean
{lit}`<Name>.parse` over a corpus. This validates packaging and serialization, which the
parser theorem itself does not mention.

The planned stages are:

1. retain the specialized Lean entry point already generated;
2. emit a per-format Lean executable with a stable text or JSON protocol;
3. add corpus equivalence tests between that executable and the in-process parser;
4. optionally expose the same entry point through a narrow C ABI;
5. provide a Rust consumer crate for that ABI.

# Rust and the trust boundary

Calling compiled Lean from Rust through a reverse FFI does not produce verified Rust code. The
Lean theorem verifies the semantics of the Lean parser definition. The following remain trusted
integration components:

- Lean code generation and runtime;
- executable or shared-library linking;
- the C ABI wrapper and memory ownership rules;
- marshaling between Lean, C, JSON, and Rust values;
- the Rust caller's use of returned data.

A corpus equivalence test can provide strong integration evidence, but it is not a universal
semantic proof. A verified FFI framework can reduce parts of this boundary by proving marshaling
and calling-convention obligations. It still needs a theorem connecting the extracted or linked
artifact to the source semantics; foreign execution does not inherit that theorem merely by
crossing the ABI.

Direct verified Rust extraction or translation is therefore a separate research track. The
practical near-term product is a verified Lean parser consumed through a small, carefully tested
foreign interface, described with an explicit trust boundary.
