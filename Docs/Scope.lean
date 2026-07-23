/-
Triptych documentation — Chapter 4: the scope gradient (what the DSL can and cannot say).
-/
import VersoManual
import Triptych.Examples.Graph.parser
import Triptych.Examples.IPv6.parser

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Scope: three tiers and a graceful exit" =>

%%%
tag := "scope"
shortTitle := "Scope"
file := "scope"
%%%

```lean -show
open Triptych
open Triptych.Examples.Graph
```

Triptych's expressiveness is layered on purpose. The grammar tier is kept small enough
that everything about it can be proven automatically; two further tiers let the *accepted
language* and the *parsed value* escape that class without giving up the automation where it
still applies. This chapter maps the ceiling of each tier and what degrades — gracefully —
when you cross it.

# Tier one: the grammar

The grammar language is a strict subclass of the regular languages:

- concatenation and finite alternation (`|`),
- optional items (`[x]`) and the `sign` terminal,
- character-class token runs — `digit`, `hexDigit`, `bit` — with length specs
  (`{n}`, `{lo,hi}`, `+`),
- separated group repetition: `rep <item> sepBy "<sep>" <len>`.

No recursion — the nonterminal dependency graph must be a DAG, so the language is not even
context-free — and no data-dependent lengths. The payoff for this austerity: the denotation
of any such grammar collapses to a finite first-order formula with bounded quantifiers, which
is why the generator can emit the readable existential predicates of chapter 2 *and* prove
them equivalent to the executable decoder, mechanically, for every grammar in the class.

IPv6 shows the repetition form — eight hex groups joined by colons is one line:

```
V6Addr ::= rep H16 sepBy ":" {8}
H16    ::= hexDigit{1,4}
```

```lean (name := ipv6Check)
#check @IPv6.IsWf_equiv
```

# Tier two: constraints — the accepted language escapes

Constraints conjoin extra conditions onto the grammar. The DSL forms cover arithmetic
comparisons over captures and cardinality; beyond that, the `constraints'` escape accepts
*any decidable Lean predicate* over the captures. Since the final accepted language is
grammar ∩ constraint, this tier lifts the accepted language out of the regular class
entirely — while the grammar-level reconciliation from tier one still holds and is still
auto-proven.

The Graph example leans on this. The SAT community encodes a simple graph as the upper
triangle of its adjacency matrix, flattened to a bit string. One grammar covers graphs of
*every* order:

```
Adj   ::= Cells
Cells ::= bit+
```

The grammar over-approximates: any non-empty bit string. A `constraints'` escape carves out
the valid ones — the length must be a triangular number `n(n-1)/2` (else the bits are not a
complete upper triangle of any order). "The set of strings whose length is triangular" is
not a regular language; no grammar in tier one could express it. The constraint tier does
not care.

# Tier three: values — the output type escapes

The scalar `value` DSL computes an `Int` from sign, magnitude, and length readers. The
`value'` escape replaces it with any Lean function of the captures, returning *any type*.
Graph uses it to produce an actual structure — vertex count plus edge list — recovering the
order from the string length:

```lean (name := graphEvals)
#eval Graph.computeValue "101"     -- path on 3 vertices
#eval Graph.computeValue "111111"  -- K₄
#eval Graph.computeValue "11"      -- 2 not triangular
```

The three tiers compose into a clean division of labor, visible in this one example: the
*grammar over-approximates* (any bit string), the *constraints carve* (triangular length),
and the *value interprets* (bits → graph). Asking "don't we need a separate grammar for each
graph order?" gets the answer *no* — the order is data, checked by a constraint and recovered
by the value function, which is exactly what those layers are for.

# What escapes cost

The degradation is deliberate and partial. With a `value'` or `constraints'` escape:

- *still auto-proven*: the grammar reconciliation (`IsWf_equiv`), decidability of the
  surface predicates, and the parser's contract theorems — tier one does not know or care
  what sits in the escape;
- *no longer auto-proven*: anything about the escape's *content*. The generator treats the
  escaped function as opaque; if you want theorems about `toGraph` itself, you write them.

This is the same philosophy as chapter 3's obligation surface: automation up to exactly the
point where the claim stops being the generator's to make.

# Out of scope, honestly

Some formats fall outside all three tiers, and the right answer is a hand-written decoder —
not a DSL contortion. The canonical example is graph6, the dense on-disk graph format: its
header encodes the vertex count, and the *length of the rest of the input* depends on that
value. Data-dependent length is precisely what tier one's regular skeleton cannot express,
and no constraint can rescue it, because constraints only restrict what the grammar already
parses — they cannot change how the string is *split*.

Similarly out of scope: anything recursive (JSON, s-expressions, Cedar's own policy
language), length-prefixed binary payloads, and formats whose field boundaries require
lookahead beyond the grammar class. For these, Triptych's honest contribution is the
*specification vocabulary* — you can still write the spec-side predicates by hand in the
same style, but the reconciliation proof is yours.

# The gradient, summarized

1. *Flat-regular grammar + arithmetic value + comparison constraints* — everything
   generated, everything proven, zero obligations. (Decimal, IPv4, IPv6.)
2. *Escapes* — grammar reconciliation and decidability still free; the escaped
   value/constraint content is opaque and yours to reason about. (Graph, Datetime's
   day-of-month bound.)
3. *External parser / printer clauses* — the conformance claims of chapter 3, stated
   precisely and left as the only `sorry`s in the system. (Decimal, Duration, Datetime.)
4. *Out of scope* — hand-written decode, spec vocabulary reusable, proofs manual. (graph6.)

Each step down the gradient trades automation for expressiveness in a controlled way, and —
the design's central promise — nothing you got for free at a higher tier is taken away.
