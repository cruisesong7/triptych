/-
Triptych documentation -- Chapter 4: supported scope and current boundaries.
-/
import VersoManual
import Triptych.Architecture.Syntax

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "Scope: supported tiers and current boundaries" =>

%%%
tag := "scope"
shortTitle := "Scope"
file := "scope"
%%%

```lean -show
open Triptych
```

Triptych's expressiveness is layered. The grammar tier remains small enough for generated
reconciliation proofs, constraints can narrow its language, and value escapes can return
arbitrary types. This chapter describes the supported surface and the boundary of the current
compiler.

*Supported now.* Triptych generates readable specifications, executable parsers, and
reconciliation proofs for acyclic, non-recursive grammars built from literals, finite
alternatives, optional items, {lit}`sign`, built-in digit, hexadecimal, and bit runs, inclusive
ASCII ranges, separated repetition, and delimiter-bounded final payloads whose exact width is
computed from earlier captures. Values and constraints may use the
analyzable DSLs or user-supplied escape functions. Declared external parsers and printers receive
explicit proof contracts.

*Not currently supported.* The generated grammar surface does not directly support the
arbitrary character predicates or unseparated repetition needed by general Base64,
delimiter-free or internal capture-dependent boundaries, or recursive formats such as JSON,
s-expressions, and Cedar policies. The scanner architecture supports a header-selected tail
grammar through {name}`Triptych.scanDependent`, and the Graph6 example exercises that API, but
automatic specification, view, and derivation generation for that general staged form remains
future work.

# Grammar

The grammar language is a strict subclass of the regular languages:

- concatenation and finite alternatives;
- optional items and the dedicated {lit}`sign` terminal;
- built-in {lit}`digit`, {lit}`hexDigit`, and {lit}`bit` runs with
  {lit}`{n}`, {lit}`{lo,hi}`, or {lit}`+` lengths;
- inclusive ASCII ranges such as {lit}`ascii[63,126]{1}`;
- separated repetition such as {lit}`rep H16 sepBy ":" {8}`.
- a final named terminal such as {lit}`Cells ::= bit{upperTriangleSize Order}`, when a
  literal delimiter fixes its boundary and the start rule captures {lit}`Order` first.

Triptych checks the complete nonterminal graph during elaboration. If it detects a cycle, for
example {lit}`A -> B -> A`, it rejects the declaration and reports the cycle. This check enforces
the current non-recursive boundary. With an acyclic graph and field boundaries fixed by grammar
structure, Triptych can emit readable predicates, executable decoding, and their equivalence
mechanically.

## Sized final payloads

The first dependent surface form covers a common binary and SAT/SMT layout: a header declares
the exact size of the final payload.

```lean
def upperTriangleSize (order : String) : Nat :=
  let vertices := Triptych.readNat order
  vertices * (vertices - 1) / 2

def toGraph (order cells : String) : Nat × String :=
  (Triptych.readNat order, cells)

triptych Graph where
  grammar
    Graph ::= Order ":" Cells
    Order ::= digit+
    Cells ::= bit{upperTriangleSize Order}
  value'
    toGraph Order Cells
```

For {lit}`"3:101"`, {lit}`Order` is {lit}`"3"` and the required payload width is three.
{lit}`"3:10"` and {lit}`"3:1010"` are rejected. Triptych represents the lexical payload as
zero-or-more bits and generates the exact-width equation as part of {lit}`IsWf`. It therefore
emits the same readable specification, typed {lit}`View`, structural {lit}`Derivation`,
executable parser, parser contracts, and search-cost theorem as for an ordinary declaration.
The derivation's structural validity checks the lexical bit shape; the generated
{lit}`IsWf` and {lit}`View.Valid` additionally enforce the dependent width.

The width function is specification code: Lean checks its type and definition, while the author
is responsible for ensuring that it expresses the intended format rule. The current surface form
is deliberately limited to one final, delimiter-bounded payload. Formats in which width
validation must make the parser reconsider the header use the staged architecture API described
in the scanner chapter.

# Values and constraints

The analyzable {lit}`value` DSL computes an {name}`Int` from sign, magnitude, length, and
count readers. The analyzable {lit}`constraints` DSL narrows the grammar with arithmetic
comparisons, lengths, numeric values, canonical decimal spelling, and {lit}`count X`.

For semantics outside those DSLs, {lit}`value'` accepts an ordinary Lean function returning any
type, while {lit}`constraints'` accepts any Boolean Lean predicate. Both can receive scalar
captures or repeated-capture {lean}`List String` arguments. Either value form may use
{lit}`ofSpec` and {lit}`toSpec` to expose a different application-facing parser result type.

The Cedar-independent Graph example uses {lit}`value'` to produce a structured result:

```
structure Graph where
  order : Nat
  edges : List (Nat × Nat)

triptych Graph where
  grammar
    Graph ::= Order ":" Cells
    Order ::= digit+
    Cells ::= bit{upperTriangleSize Order}
  value'
    toGraph Order Cells
```

{lit}`toGraph : String -> String -> Graph` converts the captured order and exact-width cell
payload into a vertex count and edge list. A {lit}`constraints'` function can similarly add any
decidable format-specific condition that is not expressible in the analyzable constraint DSL.

With {lit}`value'` or {lit}`constraints'`, Triptych still proves grammar reconciliation,
decidability, typed-view equations, and generated-parser contracts against the supplied
functions. Those functions become part of the trusted specification: Lean checks their
definitions, but users must ensure that they correctly represent the intended value and
constraint.

# Ambiguity and static certificates

The grammar class permits ambiguous alternatives and token splits. The runtime scanner preserves
the archived reference decoder's source order and chooses the same first complete parse, so
recognition alone does not imply that captures or values are grammar-determined.

{name}`Triptych.GrammarCaptureFunctional` states the needed semantic property. A conservative
{name}`Triptych.Grammar.staticUnique` checker proves it for deterministic fragments such as
Decimal. When certification succeeds, Triptych emits premise-free decode/render, view/render,
value-coherence, and relational-parser theorems.

Structural derivation membership is still generated when the conservative checker cannot
certify a grammar. In that case, exact first-decode roundtrip retains an explicit
capture-functionality premise.
