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
alternatives, optional items, {lit}`sign`, built-in digit, hexadecimal, and bit runs, and
separated repetition. Values and constraints may use the analyzable DSLs or user-supplied escape
functions. Declared external parsers and printers receive explicit proof contracts.

*Not currently supported.* The generated grammar surface does not directly support the
user-defined character classes or unseparated repetition needed by general Base64, field
boundaries that depend on earlier values such as Graph6, or recursive formats such as JSON,
s-expressions, and Cedar policies. These formats currently require a hand-written parser and a
separately proved specification. The next chapter describes the planned extensions.

# Grammar

The grammar language is a strict subclass of the regular languages:

- concatenation and finite alternatives;
- optional items and the dedicated {lit}`sign` terminal;
- built-in {lit}`digit`, {lit}`hexDigit`, and {lit}`bit` runs with
  {lit}`{n}`, {lit}`{lo,hi}`, or {lit}`+` lengths;
- separated repetition such as {lit}`rep H16 sepBy ":" {8}`.

Triptych checks the complete nonterminal graph during elaboration. If it detects a cycle, for
example {lit}`A -> B -> A`, it rejects the declaration and reports the cycle. This check enforces
the current non-recursive boundary. With an acyclic graph and field boundaries fixed by grammar
structure, Triptych can emit readable predicates, executable decoding, and their equivalence
mechanically.

# Values and constraints

The analyzable {lit}`value` DSL computes an {name}`Int` from sign, magnitude, length, and
count readers. The analyzable {lit}`constraints` DSL narrows the grammar with arithmetic
comparisons, lengths, numeric values, canonical decimal spelling, and {lit}`count X`.

For semantics outside those DSLs, {lit}`value'` accepts an ordinary Lean function returning any
type, while {lit}`constraints'` accepts any Boolean Lean predicate. Both can receive scalar
captures or repeated-capture {lean}`List String` arguments. Either value form may use
{lit}`ofSpec` and {lit}`toSpec` to expose a different application-facing parser result type.

The Cedar-independent Graph example uses both escapes:

```
structure Graph where
  order : Nat
  edges : List (Nat × Nat)

triptych Graph where
  grammar
    Adj   ::= Cells
    Cells ::= bit+
  value'
    toGraph Cells
  constraints'
    isTriangular Cells
```

The grammar accepts any nonempty bit string. {lit}`isTriangular : String -> Bool` restricts its
length to {lit}`n(n-1)/2`, so the final accepted language is non-regular even though the grammar
is regular. {lit}`toGraph : String -> Graph` constructs the vertex count and edge list. For
example, {lit}`"101"` denotes a path on three vertices, while {lit}`"11"` is rejected because
length two is not triangular.

With {lit}`value'` or {lit}`constraints'`, Triptych still proves grammar reconciliation,
decidability, typed-view equations, and generated-parser contracts against the supplied
functions. Those functions become part of the trusted specification: Lean checks their
definitions, but users must ensure that they correctly represent the intended value and
constraint.

# Ambiguity and static certificates

The grammar class permits ambiguous alternatives and token splits. The reference decoder
enumerates full parses and chooses the first, so recognition alone does not imply that captures
or values are grammar-determined.

{name}`Triptych.GrammarCaptureFunctional` states the needed semantic property. A conservative
{name}`Triptych.Grammar.staticUnique` checker proves it for deterministic fragments such as
Graph and Decimal. When certification succeeds, Triptych emits premise-free decode/render,
view/render, value-coherence, and relational-parser theorems.

Structural derivation membership is still generated when the conservative checker cannot
certify a grammar. In that case, exact first-decode roundtrip retains an explicit
capture-functionality premise.
