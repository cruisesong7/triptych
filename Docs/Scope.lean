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
ASCII ranges, character sets, separated and separator-free repetition, and delimiter-bounded
fields whose exact widths are computed from earlier captures. Several dependent fields may occur in one start rule; an internal field
must be followed immediately by a nonempty literal delimiter. Values and constraints may use the
analyzable DSLs or user-supplied escape functions. Declared external parsers and printers receive
explicit proof contracts.

*Not currently supported.* The generated grammar surface does not directly support arbitrary
character predicates, delimiter-free capture-dependent boundaries, or recursive formats such as
JSON, s-expressions, and Cedar policies. The scanner architecture supports a header-selected tail
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
- character sets {lit}`oneOf " \t\r\n"+` (any listed character) and {lit}`noneOf "\n"+`
  (any other character, such as the rest of a line);
- separated repetition such as {lit}`rep H16 sepBy ":" {8}`;
- separator-free repetition such as {lit}`rep Clause +`, whose item must consume input on every
  match, so the item count remains recoverable.
- named dependent terminals such as {lit}`Cells ::= bit{upperTriangleSize Order}`, when earlier
  captures determine the width and literal delimiters fix the field boundaries.

Triptych checks the complete nonterminal graph during elaboration. If it detects a cycle, for
example {lit}`A -> B -> A`, it rejects the declaration and reports the cycle. This check enforces
the current non-recursive boundary. With an acyclic graph and field boundaries fixed by grammar
structure, Triptych can emit readable predicates, executable decoding, and their equivalence
mechanically.

## Sized fields

The dependent surface form covers common binary and SAT/SMT layouts where a header declares
later field sizes.

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
parser contracts, and verified parser as an ordinary grammar. Several sized fields may use the
same header. An internal field is supported when an immediate literal delimiter fixes its end,
as demonstrated by {lit}`other-examples/Inputs/BitRows.lean`.
The derivation's structural validity checks the lexical bit shape; the generated
{lit}`IsWf` and {lit}`View.Valid` additionally enforce the dependent width.

The width function is specification code: Lean checks its type and definition, while the author
is responsible for ensuring that it expresses the intended format rule. The current surface form
requires literal-delimited boundaries and a single start alternative. Formats in which width
validation must make the parser reconsider the header use the staged architecture API described
in the scanner chapter.

# Values and constraints

The analyzable {lit}`value` DSL computes an {name}`Int` from sign, magnitude, length, and
count readers, or a list through the comprehension {lit}`[P ↦ body]`: one element per occurrence
of the repeated production {lit}`P`, with {lit}`body` evaluated inside that occurrence. The body
is a scalar expression or another comprehension. The analyzable {lit}`constraints` DSL narrows
the grammar with arithmetic comparisons, lengths, numeric values, canonical decimal spelling,
{lit}`count X`, and {lit}`forall P, c`, which requires {lit}`c` inside every occurrence of
{lit}`P` while reading captures outside {lit}`P` from the whole input.

DIMACS CNF, the SAT solver input format, is expressible entirely in these analyzable forms:

```lean
triptych Dimacs where
  grammar
    File     ::= [Comments] Header [Clauses] [Ws]
    Comments ::= rep Comment +
    Comment  ::= "c" [Text] "\n"
    Text     ::= noneOf "\n"+
    Header   ::= "p" Blank "cnf" Blank Vars Blank Count
    Vars     ::= digit+
    Count    ::= digit+
    Clauses  ::= rep Clause +
    Clause   ::= [Lits] Ws "0"
    Lits     ::= rep WsLit +
    WsLit    ::= Ws Lit
    Lit      ::= Sign Var
    Sign     ::= sign
    Var      ::= NonZero [Digits]
    NonZero  ::= ascii[49,57]{1}
    Digits   ::= digit+
    Blank    ::= oneOf " \t"+
    Ws       ::= oneOf " \t\r\n"+
  value
    [Clause ↦ [Lit ↦ Sign * nat Var]]
  constraints
    count Clause == nat Count
    forall Lit, nat Var ≤ nat Vars
```

```lean (name := dimacsParse)
#eval Dimacs.parse "c example\np cnf 3 2\n1 -3 0\n2 3\n -1 0\n"
```

```leanOutput dimacsParse
some [[1, -3], [2, 3, -1]]
```

Each token is preceded by whitespace, so the terminator {lit}`0` cannot run into a following
literal, and literal magnitudes start with a non-zero digit. The comprehension produces the
clause list directly, and the two constraints check the header's counts. The full example in
{lit}`other-examples/Inputs/Dimacs.lean` round-trips formulas printed by
{lit}`Std.Sat.CNF.dimacs`, the printer {lit}`bv_decide` uses.

For semantics outside those DSLs, {lit}`value'` accepts an ordinary Lean function returning any
type, while {lit}`constraints'` accepts any Boolean Lean predicate. Both can receive scalar
captures, repeated-capture {lean}`List String` arguments, or groups {lit}`[P ⟨a, …⟩]` that pass
one tuple of the arguments {lit}`a, …` per occurrence of {lit}`P`. The LRAT example in
{lit}`other-examples/Inputs/Lrat.lean` uses nested groups to build Lean's own LRAT action type and
agrees with {lit}`Std`'s text-format parser on its test corpus. Either value form may use
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
the reference decoder's source order and chooses the same first complete parse, so
recognition alone does not imply that captures or values are grammar-determined.

{name}`Triptych.GrammarCaptureFunctional` states the needed semantic property. A conservative
{name}`Triptych.Grammar.staticUnique` checker proves it for deterministic fragments such as
Decimal. When certification succeeds, Triptych emits premise-free decode/render, view/render,
value-coherence, and relational-parser theorems.

The checker is a set of conservative syntactic fragments. It does not yet certify DIMACS or
LRAT, although both are unambiguous: deciding where a whitespace run or a leading-zero numeral
ends needs more than one character of lookahead. A complete decision procedure for this
grammar class is possible, because grammars are non-recursive, and is the next planned step.

Structural derivation membership is still generated when the conservative checker cannot
certify a grammar. In that case, exact first-decode roundtrip retains an explicit
capture-functionality premise.
