/-
Triptych documentation — Chapter 1: motivation and overview.
-/
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "Introduction: one grammar, a coherent parser stack" =>

%%%
tag := "intro"
shortTitle := "Introduction"
file := "intro"
%%%

Triptych compiles a flat string grammar -- decimals, durations, timestamps, or IP addresses --
into a readable specification, a specialized executable parser, and the Lean theorems that
connect them. The generated parser is ordinary code with a small public signature such as
{lean}`String → Option Int64`. The proof layer establishes that it recognizes exactly the
specified language and returns exactly the specified denotation.

The compiler also emits typed views and structural derivation trees. These are the bridge
between generated parsing and later proof work: users reason about fields, options, and lists
instead of a raw capture map.

# Where this came from

Triptych grew out of verifying the [Cedar](https://www.cedarpolicy.com/) authorization
language's extension-type parsers: hand-written Lean functions that parse strings such as
{lit}`"-12.34"`, {lit}`"1d2h3m"`, and {lit}`"2024-10-15T11:38:02Z"`.

Proving a parser correct forces an uncomfortable question first: *correct against what?*
A correctness theorem needs a specification that is independent of the parser — otherwise the
theorem is circular. So for each format we wrote one by hand: a predicate saying which strings
are well-formed, and a function saying what value a well-formed string denotes, both phrased
as direct transcriptions of the format's grammar.

Doing that three times revealed two things. First, the hand-written spec is itself a place
for bugs to hide — a mis-transcribed field width or a forgotten sign case produces a theorem
that is *provable and wrong*. Second, the specs were almost entirely mechanical. Each one had
the same shape: an existential decomposition of the string into named fields, per-field
character-class predicates, numeric range constraints, and a value function over the captured
fields. The shape was dictated by the grammar; only the grammar itself carried information.

Anything mechanical should be generated. That is Triptych.

# The drift problem

The deeper motivation is older than any particular proof. Hand-written parsers drift from
their documentation. Someone tweaks the parser to fix a bug; the grammar in the comment above
it no longer holds; nothing catches it. The RFC says one thing, the regex says another, the
code says a third.

The usual fix is discipline. Triptych's fix is structural: the specification and parser are
generated from the same grammar, and their reconciliation theorem is kernel-checked. A grammar
change regenerates the proof-free specification and executable parser together. If a generated
theorem no longer elaborates, the build fails.

# One block in, up to three files out

A {lit}`triptych` block has a required grammar and optional value, constraint,
external-parser, and printer clauses. Here is the Cedar Decimal input:

```
triptych Decimal where
  grammar
    Decimal  ::= Sign Natural "." Fraction
    Sign     ::= sign
    Natural  ::= digit+
    Fraction ::= digit{1,4}
  value
    Sign * (nat Natural * 10 ^ 4 + nat Fraction * 10 ^ (4 - len Fraction))
    ofSpec Int64.ofInt
    toSpec Int64.toInt
  constraints
    value ∈ [Int64.MIN, Int64.MAX]
  parser Cedar.Spec.Ext.Decimal.parse
  printer decimalToStr
  to "Outputs/Decimal"
```

The source lives in {lit}`cedar-examples/Inputs/Decimal.lean`. Its output is split by role:

1. *{lit}`spec.lean` -- what a reviewer reads.* It contains the grammar value, per-production
   {lit}`IsWf` predicates, value and constraint functions, the overall {lit}`IsValid`
   predicate, a typed {lit}`View`, and typed {lit}`Derivation` trees. It contains no proofs.
2. *{lit}`parser.lean` -- what an application runs and the kernel checks.* It contains the
   generic engine instance, {lit}`decodeView`, {lit}`computeValue`, the specialized
   {lit}`parse`, and all compiler-discharged reconciliation and parser-contract theorems.
3. *{lit}`soundness.lean` -- the integration boundary.* This write-once scaffold appears
   only for an explicit external parser or serializer. It states the semantic facts that the
   compiler cannot infer from syntax.

All compiler-generated proofs use only {name}`propext`, {name}`Classical.choice`, and
{name}`Quot.sound`. The five shipped Cedar formats also contain completed integration
proofs: there are no placeholders in their output or proof modules.

# Generated facts and semantic facts

Triptych can prove facts whose ingredients it generated. For example, it proves that
{lit}`decodeView` agrees with the surface predicates and that {lit}`parse` is sound,
complete, and rejecting exactly the invalid strings.

It cannot infer that an unrelated hand-written parser implements this grammar, or that a chosen
serializer is canonical. A {lit}`parser` or explicit {lit}`printer` clause therefore emits
small typed obligations. Once users prove those semantic facts, Triptych derives the larger API:
external-parser views, parse/print roundtrips, injectivity, and normalization.

The Cedar examples provide concrete evidence for this division. The compiler generated the
bookkeeping theorems; format proofs supply the Cedar-specific semantics; the final modules are
checked without {name}`sorryAx`.

# What it is not

Triptych is not a general parser generator. Its grammar tier has concatenation, finite
alternation, optional items, three built-in token classes, and separated repetition, but no
recursion or data-dependent field boundaries. JSON and length-prefixed payloads are out of
scope. General Base64 is not yet expressible because the grammar has no user-defined character
class or unseparated repetition of a nonterminal.

That narrowness is what buys full automation. Within the class, everything is generated and
proven with zero obligations; at the boundary, escape hatches let the *accepted* language be
any decidable predicate and the parsed *value* be any type, at the cost of a small manual
contract. A later chapter maps the gradient in detail.

# Reading this book

This book is built with [Verso](https://github.com/leanprover/verso). Its Lean snippets import
the actual generated Decimal and IPv6 modules. If a declaration is renamed or a theorem changes
type, {lit}`lake build docs` from {lit}`cedar-examples/` fails.

Next: Decimal end to end, including the generated typed view and the checked external parser.
