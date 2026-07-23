/-
Triptych documentation — Chapter 1: motivation and overview.
-/
import VersoManual

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Introduction: one grammar, three artifacts that can't drift" =>

%%%
tag := "intro"
shortTitle := "Introduction"
file := "intro"
%%%

Triptych is a Lean 4 library that compiles a grammar for a flat string format — decimals,
durations, timestamps, IP addresses — into three artifacts at once: a *readable specification*
you can cite, a *verified parser* you can run, and a *machine-checked proof* that the two
describe exactly the same language and compute exactly the same values. The proof is emitted
automatically and checked by the Lean kernel, so the spec and the parser cannot silently
disagree.

This chapter explains why the tool exists and what it produces. Later chapters walk through a
complete example, the obligations that remain for a human, and where the expressive ceiling
sits.

# Where this came from

Triptych grew out of verifying the [Cedar](https://www.cedarpolicy.com/) authorization
language's extension-type parsers — the hand-written Lean functions that parse strings like
`"-12.34"`, `"1d2h3m"`, and `"2024-10-15T11:38:02Z"` into decimals, durations, and datetimes.

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

The usual fix is discipline. Triptych's fix is structural: the spec and the parser are both
*generated from the same grammar*, and a reconciliation proof between them is generated and
kernel-checked at the same time. There is no step at which they can be edited apart — a change
to the grammar regenerates all three artifacts together, and a generated proof that no longer
holds fails the build.

# One block in, three files out

A `format_spec` block is a grammar plus optional value and constraint clauses. Here is the
decimal format — a signed integer part, a dot, and one to four fraction digits, denoting a
fixed-point value with four decimal places:

```
format_spec Decimal where
  grammar
    Decimal  ::= Sign Integer "." Fraction
    Sign     ::= sign
    Integer  ::= digit+
    Fraction ::= digit{1,4}
  value
    Sign * (nat Integer * 10 ^ 4 + nat Fraction * 10 ^ (4 - len Fraction))
  constraints
    value ∈ [Int64.MIN, Int64.MAX]
  to "Triptych/Examples/Decimal"
```

Elaborating this block writes generated Lean modules next to it, split by audience:

1. *`spec.lean` — what you cite.* Each production becomes a readable well-formedness
   predicate written as a plain existential over the named captures, so you can put it
   side-by-side with the grammar and check it says the same thing. Plus the value function
   and the overall acceptance predicate `IsValid`. This file is deliberately proof-free —
   it is the specification, in the sense that a human can audit it by reading.
2. *`parser.lean` — what you run and trust.* An executable engine (a total,
   capture-extracting decoder, a decidable validator, and `computeValue`), the generated
   correct-by-construction parser `parse`, and the reconciliation proofs: the engine accepts
   a string if and only if the readable spec says it is well-formed (`IsWf_equiv`), the two
   compute the same value (`computeValue_eq`), and the parser satisfies its contract
   (`parse_sound`, `parse_complete`, `parse_reject`) — all discharged automatically.
3. *`soundness.lean` — what stays human.* Emitted only when the block also names an
   *external* parser or printer (more below).

Every generated proof depends only on Lean's three standard axioms — `propext`,
`Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`, no custom axioms,
ever. That invariant is checked, not aspirational.

# The seams that stay human

Some claims have no formal oracle, and Triptych is honest about them. If you declare that
an *existing, hand-written* parser — say Cedar's real `Decimal.parse` — conforms to the
generated spec, that is a claim about code the generator did not produce and cannot inspect.
Likewise, declaring that some `toString` is *the* canonical serializer for the format is a
design choice, not a derivable fact.

For these, the block takes `parser` and `printer` clauses, and the generator emits
`soundness.lean`: a small, explicit set of obligations stated against the generated spec,
each left as a typed `sorry` for you to prove. In exchange, the theorems you actually want —
parse/print roundtripping, printer injectivity, normalization — are *derived automatically*
from those obligations. The generator draws the trust boundary precisely: everything provable
from the grammar is proven for you; the handful of claims only a human can make are the only
proofs left.

# What it is not

Triptych is not a general verified parser generator, and the scope is deliberately narrow.
The grammar tier is a strict subclass of the regular languages: concatenation, finite
alternation, optional items, character-class token runs, and separated repetition — no
recursion, no data-dependent lengths. JSON is out of scope; so is anything with a
length-prefixed payload.

That narrowness is what buys full automation. Within the class, everything is generated and
proven with zero obligations; at the boundary, escape hatches let the *accepted* language be
any decidable predicate and the parsed *value* be any type, at the cost of a small manual
contract. A later chapter maps the gradient in detail.

# Reading this book

This book is built with [Verso](https://github.com/leanprover/verso), which type-checks the
Lean code it renders as part of building the site. The walkthrough chapters pull the *actual*
generated definitions out of the Triptych library — if a rendered theorem stops compiling,
the book stops building. The documentation inherits the same anti-drift property the library
exists to provide.

Next: the Decimal walkthrough, end to end — from the block above to the generated
predicates, the verified parser, and the bridge to Cedar's real one.
