/-
Triptych documentation -- verified scanner backend.
-/
import VersoManual
import Outputs.Decimal.parser
import Outputs.IPv6.parser
import Triptych.Theorems.Dependent

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "From reference decoder to verified scanner" =>

%%%
tag := "scanner"
shortTitle := "Verified scanner"
file := "scanner"
%%%

```lean -show
open Triptych
open CedarExamples
open CedarExamples.Decimal
```

```lean -show
private def decimalRootCandidates (input : String) : List (CaptureMap × String) :=
  match Decimal.grammar.startProd? with
  | none => []
  | some production =>
      (matchProd Decimal.grammar "" Decimal.grammar.prods.length
        production input.toList).map fun result =>
          (result.1, String.ofList result.2)
```

Triptych has two parsing implementations with different jobs. The archived reference decoder is
small and proof-oriented. The scanner is the runtime engine used by every generated parser. The
switch did not replace one trusted implementation with another: Triptych proves that the scanner
returns exactly the reference result, then proves that the generated parser has the same public
contract as before.

# Why the decoder came first

The reference {name}`Triptych.decode` function enumerates possible prefix matches, keeps the
complete parses, and returns the first one in source order. Its intermediate candidate lists make
the grammar semantics and ordering policy easy to inspect. They are also useful in roundtrip,
ambiguity, and capture-coherence proofs.

That transparency has a runtime cost. Variable-width terminals can produce many prefixes, and
alternatives, optionals, and repetitions can multiply those candidates. Most candidates are
allocated only to be discarded later.

The decoder now lives under {lit}`Triptych/Archive/ReferenceDecoder.lean`. The runtime scanner
implementation does not import it. Proof modules import it explicitly as an executable reference
semantics for verification, diagnostics, and differential benchmarks.

# The scanner

{name}`Triptych.scan` fuses matching with the continuation that consumes the rest of the grammar.
A failed split is discarded immediately, and a complete parse stops the search. It preserves the
decoder's source-ordered alternatives, present-before-absent optionals, and
stop-before-continue repetition policy.

For grammars accepted by the conservative {name}`Triptych.Grammar.staticUnique` checker, the
scanner first attempts a boundary-driven path. Fixed widths and following literals determine
field boundaries without enumerating every prefix. Unsupported shapes fall back to the complete
continuation scanner, not to the archived decoder.

# A concrete Decimal trace

Consider one valid input:

```
Decimal  ::= Sign Natural "." Fraction
Sign     ::= sign
Natural  ::= digit+
Fraction ::= digit{1,4}

input: -12.34
```

## Decoder: build the choices first

The decoder represents a partial match as a pair containing the captures found so far and the
unconsumed remainder. It explores the input from left to right:

1. {lit}`Sign` consumes {lit}`-`. Its absent alternative cannot continue because
   {lit}`Natural` requires a digit.
2. {lit}`Natural` can initially consume {lit}`1` or {lit}`12`. The {lit}`1` branch leaves
   {lit}`2.34`, so the following dot fails. The {lit}`12` branch reaches the dot.
3. {lit}`Fraction` can consume {lit}`3`, leaving {lit}`4`, or consume {lit}`34`, leaving
   nothing.

The following checked equation exposes the two candidates that reach the root:

```lean (name := decimalDecoderCandidates)
example :
    decimalRootCandidates "-12.34" =
      [([("Sign", "-"),
         ("Natural", "12"),
         ("Fraction", "3")],
        "4"),
       ([("Sign", "-"),
         ("Natural", "12"),
         ("Fraction", "34")],
        "")] := by
  native_decide
```

{name}`Triptych.decode` constructs this candidate list, keeps only entries with an empty
remainder, and returns the first one. The first candidate above is discarded; the second yields
the captures {lit}`Sign = "-"`, {lit}`Natural = "12"`, and {lit}`Fraction = "34"`.

## Scanner: ask the rest immediately

The complete scanner does not first construct that list. Whenever it finds a possible prefix, it
immediately calls the continuation for the rest of the grammar:

```
Natural = "1"  -> try "." next -> fail immediately
Natural = "12" -> try "." next -> continue
Fraction = "3" -> root sees remainder "4" -> fail immediately
Fraction = "34" -> root sees no remainder -> return success
```

This is the same ordered search, but failed choices are discarded as soon as their continuation
fails, and the successful choice stops the search.

Decimal also passes {name}`Triptych.Grammar.staticUnique`, so its normal runtime path is even
more direct. The scanner sees that {lit}`Natural` is followed by the literal dot, consumes the
digit run up to that dot, and then consumes the final fraction to the end of the input. It obtains
the successful captures without complete-candidate backtracking.

The two implementations therefore return exactly the same observable result:

```lean (name := decimalDecoderScannerResult)
example :
    decode Decimal.grammar "-12.34" =
      some
        [("Sign", "-"),
         ("Natural", "12"),
         ("Fraction", "34")] ∧
    scan Decimal.grammar "-12.34" =
      some
        [("Sign", "-"),
         ("Natural", "12"),
         ("Fraction", "34")] := by
  native_decide
```

The generated parser then checks the constraints and computes the value from this one capture
map. Neither the decoder nor the scanner itself decides what the Decimal value means.

# Correctness of the switch

The proof proceeds compositionally. Scanning a symbol, sequence, and production is proved equal
to ordered search over the corresponding reference candidates. At the root, the continuation
accepts only an empty suffix:

```lean (name := scannerEquivalence)
#check @Triptych.scanSymK_eq_matchSym
#check @Triptych.scanSeqK_eq_matchSeq
#check @Triptych.scanProdK_eq_matchProd
#check @Triptych.scanSearch_eq_decode
#check @Triptych.scan_eq_decode
```

The last theorem is the behavioral replacement guarantee:

```
∀ grammar input, Triptych.scan grammar input = Triptych.decode grammar input
```

It covers successful captures, rejection, and ambiguous grammars where choosing the same first
complete parse matters.

# One scan per generated parser

The former generated implementation first decided {name}`Decimal.IsValid`, then called
{name}`Decimal.computeValue`. Both operations could scan the same input. The current parser scans
once, checks every constraint against that capture map, and computes the result from those same
captures:

```lean (name := generatedParserDefinition)
#print Decimal.parse
```

The generated {name}`Decimal.parse_eq_gated` theorem proves that this implementation is
extensionally equal to the old, readable gated presentation:

```lean (name := generatedParserEquivalence)
#check @Decimal.parse_eq_gated
#check @Triptych.scannerParseMap_eq_gatedParseOfSpec
```

Soundness, completeness, exact rejection, typed-view equations, printer roundtrips, and external
parser equivalence are therefore unchanged. They now depend on the implementation only through
{name}`Decimal.parse_eq_gated`.

# Formal search-cost evidence

The proof-only scanner profile returns the parser result together with the exact number of
completed root candidates tested by the search phase:

```lean (name := scannerCostChecks)
#check @Triptych.scanProfile_result
#check @Triptych.scannerCandidateChecks_le
#check @Triptych.scannerCandidateChecks_eq_zero_of_fastScan
#check @Decimal.parse_profile_result
#check @Decimal.parse_candidateChecks_le
#check @Decimal.parse_candidateChecks_eq_zero_of_fastScan
```

These theorems establish three facts:

1. profiling does not describe a different parser;
2. every generated parse stays within the finite candidate-tree budget; and
3. a successful certified fast scan performs zero complete-candidate backtracking.

This is a formal search guarantee, not a blanket linear-time theorem. Ambiguous grammar choices
can still yield an exponential candidate tree, and user-supplied {lit}`value'` or
{lit}`constraints'` functions can perform arbitrary work. For a fixed deterministic generated
grammar, the fast path avoids root-candidate backtracking; wall-clock time and allocation remain
properties measured by benchmarks rather than hidden inside the theorem statement.

# Dependent continuation

Fixed grammar boundaries are not enough for formats whose header determines the payload shape.
Triptych now supports two increasingly general cases.

The public dependent-width form handles one final payload after a literal delimiter:

```
Graph ::= Order ":" Cells
Order ::= digit+
Cells ::= bit{upperTriangleSize Order}
```

The delimiter fixes where {lit}`Order` ends and {lit}`Cells` begins. Triptych scans the ordinary
lexical grammar and generates {lit}`cells.length = upperTriangleSize order` as an intrinsic
well-formedness condition. Because this path stays inside the ordinary generator, it receives
the normal readable predicates, typed view and derivation, parser contracts, and cost theorem.

The more general architecture API {name}`Triptych.scanDependent` scans a header prefix, passes
the resulting captures to a tail-grammar function, and requires that generated grammar to
consume the remaining input.

For example, the Graph6 architecture example decodes the one-, four-, or eight-character vertex
count header and constructs a payload grammar whose exact width is
{lit}`ceil(n(n-1)/2 / 6)`. The payload still runs through the ordinary verified scanner; the
dependent combinator changes which ordinary grammar is selected.

The proof follows the same reference/implementation pattern as the flat scanner:

```lean (name := dependentScannerChecks)
#check @Triptych.scanDependent_eq_decodeDependent
#check @Triptych.scanDependent_isSome_iff
#check @Triptych.dependentScanProfile_result
#check @Triptych.dependentCandidateChecks_le
```

The first theorem preserves the source-ordered reference result. The second characterizes
recognition independently of which successful captures are selected. The final two connect the
executable result to a profile and bound all completed header and tail candidates.

This staged form remains an architecture API. It is required when accepting or rejecting a tail
must make the parser try a different header candidate, as in Graph6's one-, four-, and
eight-character header alternatives. The {lit}`triptych` command does not yet generate the
combined view and derivation artifacts for that general case.

# Tradeoff

The two implementations are intentionally retained:

- The *reference decoder* favors semantic transparency. It materializes candidates, which makes
  induction and ordering arguments direct, but is allocation-heavy.
- The *scanner* favors execution. It performs the same ordered search lazily and has a certified
  deterministic path, but its continuation structure is less pleasant as the primary proof
  semantics.

Keeping the decoder as an archived model gives the scanner a simple independent specification.
Generated applications import and execute the scanner; proof and benchmark modules may import
{lit}`Triptych.Archive` when they need the reference model or cost profile.

# Measured evidence

The repository includes paired scanner/reference benchmarks for Graph, Decimal, and IPv6, plus
the Cedar conformance suite. In one local development build, the generated one-scan parser was
*2.8x* faster than the old gated parser for Decimal, *2.7x* faster for a full IPv6 address, and
*2.9x* faster for a compressed IPv6 address. The lower-level scanner/reference comparison ranged
from *1.2x* on compressed IPv6 to *270x* on the largest Graph case;
that wider range reflects how much candidate materialization each grammar triggers.

Run the same comparisons locally:

```
cd other-examples && lake exe parser_benchmark
cd cedar-examples && lake exe scanner_benchmark
cd cedar-examples && lake build ConformanceTests
```

Timings vary by machine and build mode, so CI does not enforce a fixed speedup. Each benchmark
checks that both engines accept the same number of iterations, while
{name}`Triptych.scan_eq_decode` and the generated parser contracts provide the machine-checked
correctness evidence.
