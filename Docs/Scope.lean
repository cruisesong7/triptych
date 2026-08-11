/-
Triptych documentation -- Chapter 5: the scope gradient.
-/
import VersoManual
import Outputs.IPv6.parser

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "Scope: three tiers and an explicit boundary" =>

%%%
tag := "scope"
shortTitle := "Scope"
file := "scope"
%%%

```lean -show
open Triptych
open CedarExamples.IPv6
```

Triptych's expressiveness is layered. The grammar tier remains small enough for generated
reconciliation proofs; constraints can narrow its language; value escapes can return arbitrary
types. This chapter marks both the useful boundary and the current missing features.

# Tier one: flat grammar

The grammar language is a strict subclass of the regular languages:

- concatenation and finite alternatives;
- optional items and the dedicated {lit}`sign` terminal;
- built-in {lit}`digit`, {lit}`hexDigit`, and {lit}`bit` runs with
  {lit}`{n}`, {lit}`{lo,hi}`, or {lit}`+` lengths;
- separated repetition such as {lit}`rep H16 sepBy ":" {8}`.

The nonterminal graph must be acyclic, and field boundaries cannot depend on values parsed
earlier. This restriction lets Triptych emit readable predicates, executable decoding, and
their equivalence mechanically.

IPv6 uses the repetition form:

```
Full ::= rep H16 sepBy ":" {8}
H16  ::= hexDigit{1,4}
```

```lean (name := ipv6Check)
#check @IPv6.IsWf_equiv
```

The complete IPv6 input also supports {lit}`::` compression and an optional CIDR prefix
length. In {lit}`2001:db8::/64`, {lit}`/64` is lexically appended to the address, but the
semantic term is *prefix length*: it says how many leading address bits identify the network.
The Cedar API accordingly uses names such as {name}`Cedar.Spec.Ext.IPAddr.IPv6Prefix`.

# Tier two: accepted-language constraints

Constraints conjoin conditions with the grammar. The analyzable DSL covers arithmetic
comparisons, lengths, numeric values, canonical decimal spelling, and {lit}`count X`.
The {lit}`constraints'` escape accepts any Boolean Lean predicate over scalar captures and
repeated-capture {lean}`List String` arguments.

Because the final language is grammar intersection constraint, this tier can describe
non-regular subsets while preserving the grammar-level reconciliation theorem.

The Cedar-free Graph example accepts a nonempty bit string at the grammar tier:

```
Adj   ::= Cells
Cells ::= bit+
```

Its {lit}`constraints'` predicate requires the length to be triangular,
{lit}`n(n-1)/2`. The set of triangular-length strings is not regular, but the grammar can
over-approximate and the constraint can carve out the intended language.

# Tier three: arbitrary values

The analyzable {lit}`value` DSL computes an {name}`Int` from sign, magnitude, length, and
count readers. The {lit}`value'` escape accepts an ordinary Lean function and can return any
type. Graph uses it to return a structure containing a vertex count and edge list.
For example, {lit}`"101"` denotes a path on three vertices, while {lit}`"11"` is rejected
because length two is not triangular.

In one example, the grammar over-approximates, the constraint validates a complete upper
triangle, and the value function interprets its bits as edges.

With {lit}`value'` or {lit}`constraints'`, Triptych still proves grammar reconciliation,
decidability, typed-view equations, and generated-parser contracts. It treats the escaped
function's internal semantics as a named user fact.

# Ambiguity and static certificates

The grammar class permits ambiguous alternatives and token splits. The reference decoder
enumerates full parses and chooses the first, so recognition alone does not imply that captures
or values are grammar-determined.

{name}`Triptych.GrammarCaptureFunctional` states the needed semantic property. A conservative
{name}`Triptych.Grammar.staticUnique` checker proves it for deterministic fragments such as
Graph and Decimal. When certification succeeds, Triptych emits premise-free decode/render,
view/render, value-coherence, and relational-parser theorems.

General shared-prefix alternatives, nullable sequences, and repetition functionality remain
future certificate work. Structural derivation membership is still generated for grammars that
do not pass the conservative checker; only exact first-decode roundtrip retains an explicit
capture-functionality premise.

# Current boundary: Base64

General Base64 is not currently a direct Triptych grammar. Its alphabet needs either a
user-defined character class or unseparated repetition of a 64-way symbol, and its last quartet
has padding rules. Triptych currently has three built-in token classes, while {lit}`rep`
requires a nonempty separator.

A useful extension would add user-defined finite character classes, unseparated bounded
repetition, and analyzable quartet/padding constraints. The value tier can already host a Base64
decoder once the grammar can split and validate the text.

# Dependent layouts and recursion

Constraints can reject a fully decoded string, but they cannot change how it was split. Formats
whose later field length depends on an earlier value therefore remain out of scope. The same is
true for recursive formats such as JSON, s-expressions, and Cedar policies.

Graph6 is a representative boundary case: its header determines the length of the following
payload. A hand-written decoder is the right implementation until Triptych has dependent
boundaries.

# The gradient

1. *Flat grammar, analyzable value, analyzable constraints* -- generated and proved with no
   semantic obligations.
2. *Value or constraint escapes* -- parser coherence remains generated; escaped semantics are
   supplied by users.
3. *External parser or explicit printer* -- Triptych states the semantic contract and derives
   its consequences. All shipped Cedar contracts are complete.
4. *Recursive or dependent layout* -- use a hand-written parser and a separately proved
   specification.

Each step trades automation for expressiveness without weakening the theorems already obtained
at an earlier tier.
