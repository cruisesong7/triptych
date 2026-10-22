/-
Triptych documentation -- verified scanner backend.
-/
import VersoManual
import Outputs.Decimal.parser
import Outputs.IPv6.parser
import Triptych.Backend.Verus.SemanticPlan
import Triptych.Runtime.Dependent.Proofs
import Triptych.Plan.SearchMachine.Proofs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "The proof-carrying parser engine" =>

%%%
tag := "scanner"
shortTitle := "Parser engine"
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

Triptych separates the engine into one reference semantics and two compiled execution tracks:

```
grammar
  |
  +-- reference decoder <-> complete continuation scanner
  |
  `-- ParsePlan
       |-- cursor: ScanPlan -> CursorProgram -> direct parser
       `-- search: SearchPlan -> SearchProgram -> SearchMachine -> direct parser

selected captures -> ExecutableSemanticPlan -> constraints, value, and domain result
```

The reference decoder is small and proof-oriented. The continuation scanner is the
complete executable specification. {name}`Triptych.ParsePlan` then chooses a straight-line
cursor compiler for a deterministic layout or an ordered search compiler for a supported
branching layout. Neither generated parser traverses the source grammar at runtime.

The search track resolves production references, fuses sequence continuations, reduces shared
prefixes, and lowers the result to callback-free states. The cursor track lowers known field
boundaries to direct operations. Checked equivalence theorems connect both tracks to the same
scanner and reference decoder, so the choice changes implementation strategy without changing
the public parser contract.

The compiler records this choice once as a {name}`Triptych.ParsePlan`. A {lit}`cursor` plan
contains the deterministic scan plan used for straight-line code generation. A {lit}`search`
plan contains a resolved ordered search for an acyclic branching grammar. A {lit}`scanner` plan
records why neither specialized compilation succeeded. It is a diagnostic result, not an emitted
runtime fallback: Lean and Verus reject generation with that reason. Both backends consume the
same decision, so they classify a grammar consistently. Lean emits cursor programs and
continuation-fused search programs directly. Verus emits cursor plans and callback-free
search-machine states directly. Lean stages a repetition's item parser as direct control flow;
Verus unrolls finite repetition states. Both preserve the ordered stopping policy and generated
count captures.

{name}`Triptych.ParsePlan.CertifiedFor` is the proof boundary. A search plan must structurally
mirror the grammar. A cursor plan additionally requires capture uniqueness and its local
certificate. The internal scanner case needs no extra premise, and the generic
{name}`Triptych.ParsePlan.decode_eq_scan` theorem covers all three constructors. Public emitters,
however, accept only certified cursor and search plans.

# Why the decoder came first

The reference {name}`Triptych.decode` function enumerates possible prefix matches, keeps the
complete parses, and returns the first one in source order. Its intermediate candidate lists make
the grammar semantics and ordering policy easy to inspect. They are also useful in roundtrip,
ambiguity, and capture-coherence proofs.

That transparency has a runtime cost. Variable-width terminals can produce many prefixes, and
alternatives, optionals, and repetitions can multiply those candidates. Most candidates are
allocated only to be discarded later.

The decoder now lives under {lit}`Triptych/Reference/Decoder.lean`. The runtime scanner
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
continuation scanner, not to the reference decoder.

# Certified parser plans

{name}`Triptych.compileParsePlan` first selects the implementation strategy. When specialization
succeeds, {name}`Triptych.ScanPlan` describes the grammar-facing structured scan and
{name}`Triptych.CursorProgram` contains its lower-level cursor operations. The {lit}`triptych`
command checks {name}`Triptych.ScanPlan.certifiedFor`, emits the plan as a literal value, and
constructs a
{name}`Triptych.ScanPlan.MirrorsGrammar` witness that Lean checks against the generated grammar.
It then lowers each operation to {name}`Triptych.CursorOp` and emits one direct Lean call per
operation. The generated function does not traverse a grammar or an instruction list at runtime.

Some acyclic grammars still require ordered choice. For example, in
{lit}`Root ::= Left Right` with both {lit}`Left ::= digit+` and {lit}`Right ::= digit+`, the
boundary between the two fields is not statically unique. A cursor plan cannot choose one split
without search.

For this middle tier, {name}`Triptych.SearchPlan` resolves and inlines production references,
precomputes capture keys, and retains alternatives, optionals, and repetitions as explicit
ordered nodes. Its continuation executor tries one split at a time and discards a failed branch
immediately. It performs no runtime production-name lookup and constructs no candidate list.
{name}`Triptych.lowerSearchPlan` then fuses sequence tails into
{name}`Triptych.SearchProgram`: literals, token runs, captures, choices, and repetitions point
directly to their continuation. A proof-preserving reduction then removes dead failure arms and
shares common literal and fixed-width token prefixes. It may also share a captured prefix when
{name}`Triptych.SearchCode.committed` certifies that the prefix has at most one successful
boundary. Theorems {name}`Triptych.SearchCode.runK_committed`,
{name}`Triptych.SearchCode.runK_merge`, and {name}`Triptych.SearchCode.runK_reduce` prove that
these rewrites preserve the exact source-ordered continuation result.
{name}`Triptych.SearchCode.nodeCount_reduce_le` additionally proves that reduction cannot
increase the number of staged control-flow nodes. This is a generated-code size guarantee, not a
runtime complexity bound.

Generated Lean parsers compile the reduced program into direct control flow. Repetition items are
staged as direct lambdas, so executable parser bodies do not dispatch through
{name}`Triptych.SearchCode.runK`; that function remains in the checked bridge theorem. The generic theorem
{name}`Triptych.SearchProgram.lowerSearchPlan_decode` connects the complete lowering to the exact
selected capture map for every input.

For example, Datetime has five root alternatives that begin with the same captured {lit}`Date`.
The reduced generated program parses that committed prefix once and branches only afterward. The
checker remains conservative: a variable-width token run is not committed merely because a later
delimiter appears to determine its boundary, so formats such as IPv4 and IPv6 retain those
branches until that stronger delimiter-uniqueness argument is certified.

{name}`Triptych.lowerSearchProgram` performs one more total lowering into
{name}`Triptych.SearchMachine`. Saved capture boundaries, capture closure, ordered choice, and
separated repetition are explicit machine states rather than semantic callbacks. The theorem
{name}`Triptych.SearchMachine.lowerSearchPlan_decode_eq_scan` proves that every certified machine
returns exactly the complete scanner result, including count captures and rejection. This is the
proof boundary for direct generated state functions. Regression tests also check that prefixes
removed by reduction are not reintroduced by this lowering.

For cursor plans, the Verus backend consumes the same nested
{name}`Triptych.ScanPattern`. Its generated success proof reconstructs each production predicate
from the captured spans, from inner productions to the root. Its completeness proof unpacks
those witnesses in the opposite direction and derives the cursor boundary for every literal,
optional literal, and token run. The proof scheme is structural; it is not tied to Decimal's
field names or layout.

For search plans, Verus hash-conses structurally identical machine suffixes and emits one
specification/executable function pair per state. Each executable state mutates one search state.
On failure it is proved to restore the exact input cursor, captures, and marker stack, so ordered
choice can try the next branch without copying the whole state. Capture closure inserts spans in
place; rollback removes those spans and restores the saved marker. Finite separated repetitions
are unrolled into item, separator, ordered-stop, and count-capture states. If direct rendering
cannot cover a selected search shape, generation reports the unsupported shape instead of
substituting a generic runtime parser.

The generated entry point computes the input character length and ASCII classification once.
Literal and token helpers use constant-time byte access when the input and literal are ASCII, with
a Unicode-correct fallback. A variable-width token state scans the maximal accepted prefix once,
then tests its scheduled widths against that prefix in the original source order. This removes
the former triangular rescanning while preserving exactly which continuation is tried first.
Capture and marker capacities and capture-slot positions are also fixed at generation time.

# Semantic compilation

Recognition produces source spans, not copied field strings. The generated semantic stage uses
those spans to check capture constraints, evaluate the declared {lit}`value`, and apply the
registered {lit}`ofSpec` conversion. {name}`Triptych.Backend.Verus.ExecutableSemanticPlan`
is the resolved backend-neutral representation of this work: capture names have become scanner
keys, and value readers and constraints are explicit typed operations.

The emitter turns that plan into straight-line code. It indexes all semantic captures in one
pass, evaluates repeated primitive expressions once, checks constraints, and constructs the
domain result. The current executable conversions cover the signed values and structured IPv4
and IPv6 values used by the Cedar examples. An unsupported conversion prevents final-value
parser emission rather than receiving an assumed Rust meaning; the verified grammar parser
remains available.

The main semantic optimizations are selected by expression shape, not by format or production
name:

- Any short decimal span uses a verified four-step decoder. This covers fields such as IPv4
  octets and date components. Longer spans use the exact checked decoder.
- The semantic compiler derives conservative ranges from fixed terminal widths. Nonnegative
  expressions that fit {lit}`u128` and use direct addition, subtraction, constant-scale
  multiplication, or conditionals lower to primitive arithmetic. Other expressions retain the
  exact checked representation.
- A hexadecimal-sequence reader computes its numeric value and segment count together. IPv6
  reuses these summaries for address construction and group-count constraints.
- Repeated readers and common expression subtrees are emitted once and reused by constraints and
  the returned value.
- Checked arithmetic remains fail-closed. The proof records the exact mathematical result even
  when a machine integer is unavailable.

The selected lowering also drives generated-code pruning. An IP parser receives the span and
unsigned arithmetic support it uses, but not the signed {lit}`SemanticInt` implementation.
Reader-specific helpers and semantic caches are emitted only when the plan references them.
This keeps the generated source closer to the actual parser while Verus still checks the
remaining declarations as one proof-carrying module.

These optimizations preserve the same generated semantic predicates. They are reusable across
every grammar that uses the corresponding DSL operation, although the currently registered
domain conversions are narrower than the grammar language itself.

# Semantic success and rejection

Grammar scanning and semantic evaluation have separate certificates. The candidate parser is
unconditionally sound, complete, and exact on rejection. The final-value parser then evaluates
the generated value expression, checks constraints, and performs the declared conversion.

For the scanner-selected candidate, the generated Verus contract states:

```
Some value -> candidate is valid and its denotation is value
None       -> no grammar candidate was selected,
              or the selected candidate is invalid,
              or candidate_runtime_safe does not hold
```

The direct fixed-point path states the same result using its selected typed view and
{lit}`view_runtime_safe`. Runtime safety is generated structurally from the value and constraint
expressions. It checks capture bounds, positive divisors, every checked intermediate against its
machine range, and the final conversion range.

This premise cannot be removed for arbitrary DSL arithmetic. For example, an intermediate can
overflow {lit}`i128` and a later subtraction can mathematically bring the final result back into
{lit}`i64`. A fail-closed executable must reject before that cancellation, so final-value
validity alone does not imply executable success. Formats whose grammar and constraints imply
the generated runtime-safety predicate obtain ordinary no-false-rejection as a direct
consequence.

For a certified plan, {name}`Triptych.CursorProgram.decode` is the complete generated parser.
Triptych proves both directions: every successful result agrees with the grammar, and every
reference parse is accepted by the direct cursor. Rejection therefore exits directly without
running {name}`Triptych.scanSearch`:

```lean (name := certifiedScanPlanEquivalence)
#check @Triptych.ScanPlan.decode_eq_decode
#check @Triptych.ScanPlan.decode_eq_none_iff
#check @Triptych.ScanPlan.decode_eq_some_iff
#check
  @Triptych.ScanPlan.decode_eq_decode_of_mirrors
#check @Triptych.CursorProgram.decode_eq_decode
#check @Triptych.CursorProgram.decode_eq_none_iff
#check @Triptych.CursorProgram.decode_eq_some_iff
#check
  @CursorProgram.decode_eq_decode_of_mirrors
#check @Triptych.compileScanPlan_decode_eq_decode
#check
  @Triptych.compileCursorProgram_decode_eq_decode
#check @Triptych.SearchPlan.decode_eq_scanSearch
#check
  @Triptych.SearchPlan.compileSearchPlan_decode_eq_decode
#check @Triptych.SearchCode.runK_committed
#check @Triptych.SearchCode.runK_merge
#check @Triptych.SearchCode.runK_reduce
#check @Triptych.SearchCode.nodeCount_reduce_le
#check @Triptych.SearchProgram.lowerSearchPlan_decode
#check @Triptych.SearchMachineCode.lowerSearchCode_lowers
#check @Triptych.SearchMachine.lowerSearchProgram_decode
#check
  @Triptych.SearchMachine.lowerSearchPlan_decode_eq_scan
#check @Triptych.ParsePlan.CertifiedFor
#check @Triptych.ParsePlan.decode_eq_scan
#check @Triptych.ParsePlan.compile_certifiedFor
#check @Triptych.ParsePlan.compile_decode_eq_scan
```

Cursor plans use {name}`Triptych.ScanPlan.MirrorsGrammar`, the generated
capture-functionality theorem, and a local plan certificate to justify direct soundness,
completeness, and exact rejection. Search plans use
{name}`Triptych.SearchPlan.MirrorsGrammar`; continuation fusion is then proved equal to that
resolved search, whose structural theorem proves exact equality with the complete ordered scanner
without requiring uniqueness. If neither specialized compiler accepts a grammar, code generation
fails with the recorded diagnostic. The source scanner remains proof-facing, and its equality
with the archive is proved separately.

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
#guard
    decimalRootCandidates "-12.34" ==
      [([("Sign", "-"),
         ("Natural", "12"),
         ("Fraction", "3")],
        "4"),
       ([("Sign", "-"),
         ("Natural", "12"),
         ("Fraction", "34")],
        "")]
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
more direct. Generation resolves the boundary after {lit}`Natural` from the following literal
dot and emits the corresponding cursor operations. At runtime the specialized parser executes
those known operations and obtains the captures without grammar traversal or complete-candidate
backtracking.

The two implementations therefore return exactly the same observable result:

```lean (name := decimalDecoderScannerResult)
#guard
    decode Decimal.grammar "-12.34" ==
      some
        [("Sign", "-"),
         ("Natural", "12"),
         ("Fraction", "34")] &&
    scan Decimal.grammar "-12.34" ==
      some
        [("Sign", "-"),
         ("Natural", "12"),
         ("Fraction", "34")]
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
{name}`Decimal.computeValue`. Both operations could scan the same input. The current parser
executes one specialized capture pass on successful deterministic inputs and stores captures as
source spans. Rejected inputs therefore allocate no captured strings. On success it projects the
spans directly into {name}`Decimal.View`; analyzable value constraints reuse the same
{name}`Decimal.View.denotation` result that the parser returns instead of evaluating the value
expression again:

```lean (name := generatedParserDefinition)
#print Decimal.parse
```

The generated {name}`Decimal.parse_eq_gated` theorem proves that this implementation is
extensionally equal to the old, readable gated presentation:

```lean (name := generatedParserEquivalence)
#check @Decimal.parse_eq_scanner
#check @Decimal.parse_eq_gated
#check @Triptych.decodedViewParse_eq_gatedParseOfSpec
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

The implementation strategy is therefore general across the supported grammar constructors, but
one benchmark result is not a complexity guarantee for every accepted declaration. Cursor plans
have a single staged path. Search plans scan each variable-width token prefix once per reached
state, but ordered alternatives can revisit later states. Triptych currently proves the finite
candidate budget and exact parser behavior; it does not yet emit a universal
{lit}`steps <= a * input.length + b` certificate.

# Dependent continuation

Fixed grammar boundaries are not enough for formats whose header determines the payload shape.
Triptych now supports two increasingly general cases.

The public dependent-width form handles one or more fields whose widths come from earlier
captures. A final field needs a preceding literal delimiter:

```
Graph ::= Order ":" Cells
Order ::= digit+
Cells ::= bit{upperTriangleSize Order}
```

An internal dependent field additionally needs an immediate literal delimiter to fix its end:

```
Rows   ::= Width ":" First "/" Second
Width  ::= digit{1,2}
First  ::= bit{rowWidth Width}
Second ::= hexDigit{rowWidth Width}
```

Triptych scans an ordinary lexical over-approximation and generates both exact-width equations
as intrinsic well-formedness conditions. Because this path stays inside the ordinary generator,
it receives the normal readable predicates, typed view and derivation, parser contracts, and
cost theorem. {lit}`other-examples/Inputs/BitRows.lean` exercises multiple dependent fields and
the internal-field boundary.

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

This staged form remains an architecture API. It is required for delimiter-free boundaries or
when accepting or rejecting a tail must make the parser try a different header candidate, as in
Graph6's one-, four-, and eight-character header alternatives. The {lit}`triptych` command does
not yet generate the combined view and derivation artifacts for that general case.

# Engine roles

The representations are intentionally retained:

- The *reference decoder* favors semantic transparency. It materializes candidates, which makes
  induction and ordering arguments direct, but is allocation-heavy.
- The *generic scanner* favors complete execution. It performs the same ordered search lazily,
  and is the executable specification for compiled plans.
- The *resolved search plan* favors acyclic branching grammars. It removes production lookup and
  candidate lists while retaining the scanner's ordered backtracking.
- The *continuation-fused search program* favors code generation. It turns list-shaped sequences
  and alternatives into explicit control flow while preserving the search plan exactly.
- The *callback-free search machine* favors backend emission. It makes capture boundaries,
  alternatives, and repetitions explicit states whose shared suffixes can be generated once.
- The *staged cursor parser* favors generated runtime code. It removes grammar and instruction-list
  traversal for certified plans and rejects directly without invoking the generic scanner.

Keeping the decoder as a reference model gives the scanner a simple independent specification.
Generated Lean applications execute a cursor plan when available, otherwise a resolved search
program. The Verus backend emits cursor plans and supported search machines directly. Both
backends fail generation when specialized lowering or rendering cannot cover the grammar, rather
than silently changing to a generic runtime implementation.
Proof and benchmark modules may import {lit}`Triptych.Reference` when they need the reference model
or cost profile.

# Measured evidence

The repository includes staged-parser/scanner and scanner/reference benchmarks, plus the Cedar
conformance suite. The Lean backend defers captures as spans, projects typed views without a
generic capture map, and caches denotation used by both constraints and the returned value.

The Verus search-machine benchmark reports grammar scanning separately from semantic evaluation.
After transactional rollback, fixed capture slots, hoisted text invariants, one-pass token-prefix
scanning, and fixed-bound decoding for short natural fields, one warmed release run measured:

| Format | Scan | Full Triptych parser | Cedar production parser |
| --- | ---: | ---: | ---: |
| Decimal | {lit}`11.72 ns` | {lit}`24.24 ns` | {lit}`98.02 ns` |
| Duration | {lit}`68.44 ns` | {lit}`54.00 ns` | {lit}`234.55 ns` |
| Datetime | {lit}`94.65 ns` | {lit}`112.84 ns` | {lit}`300.86 ns` |
| IPv4 | {lit}`27.39 ns` | {lit}`48.26 ns` | {lit}`26.77 ns` |
| IPv6 | {lit}`145.32 ns` | {lit}`162.84 ns` | {lit}`105.17 ns` |

The full Decimal, Duration, and Datetime parsers were faster than Cedar's production parsers in
this run. IPv4 was {lit}`1.80x` slower and IPv6 {lit}`1.55x` slower. IPv6 slowed from
{lit}`112.60 ns` when literal-guided dispatch stopped trying the compressed {lit}`::` form
before the full form: that reordering could select a different parse than the Lean scanner for
ambiguous grammars, so dispatch now only skips an arm whose required literal is absent. A
verified disjointness certificate would make the faster order safe again for IPv6. Bounded
primitive lowering reduced the machinery emitted for IPv4 value arithmetic, but did not
materially change its end-to-end time because capture lookup and decimal decoding still
dominate. The isolated Duration scan is slower than its full parser because release inlining can
combine recognition and semantic evaluation and eliminate intermediate candidate
materialization. Timings still depend on the
format, input, machine, compiler, and build mode.

Run the same comparisons locally:

```
cd other-examples && lake exe parser_benchmark
cd cedar-examples && lake exe scanner_benchmark
cd cedar-examples && lake build ConformanceTests
cargo bench --manifest-path verus-experiments/cedar-ext/suite/Cargo.toml \
  --bench runtime --offline --locked
```

Timings vary by machine and build mode, so CI does not enforce a fixed speedup. Each benchmark
checks that both engines accept the same number of iterations, while
{name}`Triptych.scan_eq_decode` and the generated parser contracts provide the machine-checked
correctness evidence.
