/-
Triptych documentation — Chapter 2: the Decimal walkthrough (live generated declarations).
-/
import VersoManual
import Outputs.Decimal.soundness
import Proofs.Decimal.StructuralDerivation

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "Walkthrough: the Decimal format, end to end" =>

%%%
tag := "walkthrough"
shortTitle := "Decimal walkthrough"
file := "walkthrough"
%%%

This chapter follows Cedar Decimal from its {lit}`triptych` input to the generated surface,
typed view, parser, and integration theorems. Every Lean block is elaborated against the
current generated files when this book builds.

```lean -show
open Triptych
open CedarExamples.Decimal
```

# The format

A Cedar decimal is a signed fixed-point number with up to four fraction digits:
{lit}`"1.5"`, {lit}`"-12.34"`, or {lit}`"922337203685477.5807"`. Cedar stores the
value times 10^4 in an {name}`Int64`, so {lit}`"1.5"` denotes {lit}`15000`.

Three concerns, one per DSL clause:

- *Shape* — an optional minus sign, one or more natural digits, a dot, one to four fraction
  digits. This is the grammar.
- *Meaning* — sign times (natural part scaled by 10⁴ plus fraction part scaled to fill four
  places). This is the value clause.
- *Bounds* — the value must fit in `Int64`. This is the constraint clause.

The authored block is in {lit}`cedar-examples/Inputs/Decimal.lean`:

```anchor decimalTriptychSource (module := Inputs.Decimal) (project := ".")
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

Two details worth pausing on before we look at the output:

*Named sign capture.* Triptych does not allow {lit}`sign` anonymously inside another production.
It must have its own named rule, such as {lit}`Sign ::= sign`, so the value expression can read it.

*The conversion pair.* The surface value is an {name}`Int`. {lit}`ofSpec Int64.ofInt`
converts that value to the generated parser's domain type, while
{lit}`toSpec Int64.toInt` maps a domain value back to the specification. These conversions
belong to the value boundary; the {lit}`parser` clause only names the external parser. The
range constraint makes {name}`Int64.ofInt` faithful on every accepted value.

# Artifact one: the readable spec

Elaboration writes {lit}`Outputs/Decimal/spec.lean`. Each production becomes a plain
predicate over strings. Here is the generated sign predicate:

```lean (name := isWfSign)
#print Decimal.IsWf.Sign
```

```leanOutput isWfSign
def Decimal.IsWf.Sign : String → Prop :=
fun s => s = "-" ∨ s = ""
```

The top-level predicate composes them along the concatenation structure — one existentially
quantified variable per named capture, one conjunct per production:

```lean (name := isWfDecimal)
#print Decimal.IsWf.Decimal
```

```leanOutput isWfDecimal
def Decimal.IsWf.Decimal : String → Prop :=
fun s =>
  ∃ «sign» natural fraction,
    ((s = «sign» ++ natural ++ "." ++ fraction ∧ Decimal.IsWf.Sign «sign») ∧ Decimal.IsWf.Natural natural) ∧
      Decimal.IsWf.Fraction fraction
```

The root predicate composes the productions, and {name}`Decimal.IsValid` conjoins shape with
the final-value range:

```lean (name := isValidCheck)
#print Decimal.IsValid
```

```leanOutput isValidCheck
@[reducible] def Decimal.IsValid : String → Prop :=
fun s => Decimal.IsWf s ∧ Decimal.SatisfiesConstraints s
```

## A typed field view

After parsing {lit}`"-12.34"`, most code wants the useful pieces: the sign {lit}`"-"`, the
natural digits {lit}`"12"`, and the fraction digits {lit}`"34"`. It should not need to understand
how the parser stores captures or records grammar choices.

The generated {name}`Decimal.View` packages those pieces as named fields. Its {lit}`input` field
keeps the original string, while the other fields contain the text matched by the grammar's
named productions:

```lean
example : Decimal.View :=
  {
    input := "-12.34"
    «sign» := "-"
    natural := "12"
    fraction := "34"
  }

example (view : Decimal.View) : String :=
  view.natural ++ "." ++ view.fraction
```

Code using a view can simply write {lit}`view.natural` or {lit}`view.fraction`. Without this
record, each caller would have to inspect the parser's generic capture map and know how the
grammar match was represented internally.

## A structural derivation

A view deliberately forgets how the grammar matched. That keeps ordinary field access simple,
but printer and roundtrip proofs need the missing structure: which alternative was selected,
which optional pieces were present, and how repeated or referenced productions were built.

A derivation preserves that evidence as a tree. This gives a printer a grammar-shaped target:
construct a valid derivation for a domain value, then turn the derivation into text. Its
constructor records the chosen alternative, while its children record how each referenced
production matched. For Decimal, the root constructor has children for {lit}`Sign`,
{lit}`Natural`, and {lit}`Fraction`. The dot is a fixed literal, so it does not need its own
field:

```lean
example
    (signTree : Decimal.Derivation.Sign)
    (natural : Decimal.Derivation.Natural)
    (fraction : Decimal.Derivation.Fraction) :
    Decimal.Derivation.Decimal :=
  .alt0 signTree natural fraction
```

## Rendering for verified printers

Parsing moves from text to a derivation and its fields.
{name}`Decimal.Derivation.Decimal.render` performs the tree-to-text direction: it concatenates
the terminal strings stored in a derivation and inserts the grammar's fixed literals.

```lean
example :
    decimalDerivation =
      .alt0
        (.alt0 (some ()))
        (.alt0 "12")
        (.alt0 "34") := by
  rfl
```

Evaluating rendering and validity together makes their separate roles visible:

```lean (name := renderDerivation)
#eval
  (decimalDerivation.render,
    decide decimalDerivation.Valid)
```

```leanOutput renderDerivation
("-12.34", true)
```

Crucially, {name}`Decimal.Derivation.Decimal.render` does not validate the tree. Terminal nodes
store ordinary strings, so rendering also serializes a Natural node whose text violates the
grammar:

```lean (name := invalidNatural)
#eval
  let tree := Decimal.Derivation.Natural.alt0 "abc"
  (tree.render, decide tree.Valid)
```

```leanOutput invalidNatural
("abc", false)
```

The text {lit}`"abc"` is still rendered; the separate {name}`Decimal.Derivation.Natural.Valid`
predicate rejects it.

Therefore {name}`Decimal.Derivation.Decimal.render` is not itself a verified Decimal printer. A
printer certificate chooses a derivation for each domain value and proves that the tree is valid
and denotes that value; {name}`Decimal.Derivation.Decimal.render` performs only the final
tree-to-string step. For valid derivations, later engine theorems prove that decoding the rendered
text recovers the tree's captures and typed view.

*Note:* {name}`Decimal.Derivation.Decimal.Valid` checks only that the derivation is well-formed
according to the grammar, corresponding to the string-level {name}`Decimal.IsWf`.
{name}`Decimal.IsValid` checks both {name}`Decimal.IsWf` and
{name}`Decimal.SatisfiesConstraints`; for Decimal, the semantic constraint requires the computed
value to fit in {name}`Int64`.

# Artifact two: the engine and the verified parser

The second generated file turns the readable specification into executable operations. Three
predicates describe whether an input may be parsed:

- {name}`Decimal.IsWf` checks the grammar shape and any capture-only constraints.
- {name}`Decimal.SatisfiesConstraints` checks semantic constraints on the final value. For
  Decimal, this is the {name}`Int64` range check.
- {name}`Decimal.IsValid` requires both.

These uppercase names are both the readable interface and the public executable interface.
Generated decision procedures connect them to the generic Triptych interpreter internally, so
there is no separate format-specific lowercase predicate. They can be executed through
{name}`decide`:

```lean (name := validityEvals)
#eval
  (decide (Decimal.IsValid "3.14"),
    decide (Decimal.IsValid "3.14159"))
```

```leanOutput validityEvals
(true, false)
```

The engine begins by decoding the grammar. {name}`decode` returns the named captures:

```lean (name := decodeEval)
#eval decode Decimal.grammar "1.5"
```

```leanOutput decodeEval
some [("Sign", ""), ("Natural", "1"), ("Fraction", "5")]
```

## Computing the specification value

{name}`Decimal.computeValue` evaluates the value expression and returns its specification-level
{name}`Int`. It does not apply the semantic constraint or convert the result to {name}`Int64`:

```lean (name := computeValueDefinition)
#print Decimal.computeValue
```

```leanOutput computeValueDefinition
def Decimal.computeValue : String → Option Int :=
fun s => computeValue Decimal.grammar Decimal.valueExpr s
```

For {lit}`"1.5"`, the fixed-point specification value is {lit}`15000`:

```lean (name := computeValueEval)
#eval Decimal.computeValue "1.5"
```

```leanOutput computeValueEval
some 15000
```

An out-of-range value can still be computed because range checking belongs to
{name}`Decimal.IsValid`, not to {name}`Decimal.computeValue`:

```lean (name := outOfRangeValueEval)
#eval Decimal.computeValue "922337203685477.5808"
```

```leanOutput outOfRangeValueEval
some 9223372036854775808
```

## The generated parser

{name}`Decimal.parse` combines validity, value computation, and the declared {lit}`ofSpec`
conversion:

```lean (name := parseDefinition)
#print Decimal.parse
```

```leanOutput parseDefinition
def Decimal.parse : String → Option Int64 :=
fun s => gatedParseOfSpec Decimal.IsValid Decimal.computeValue Int64.ofInt s
```

Here {name}`Decimal.IsValid` gates acceptance, {name}`Decimal.computeValue` produces the
specification {name}`Int`, and {name}`Int64.ofInt` converts it to the parser's result type.
Only after seeing that definition do the examples become meaningful:

```lean (name := parseEvals)
#eval
  (Decimal.parse "1.5",
    Decimal.parse "-0.15")
```

```leanOutput parseEvals
(some 15000, some (-1500))
```

Grammar and constraint failures both appear as {name}`Option.none`:

```lean (name := rejectEvals)
#eval
  (Decimal.parse "1.x",
    Decimal.parse "922337203685477.5808")
```

```leanOutput rejectEvals
(none, none)
```

# The typed executable view

The generated view theorems remove capture-map bookkeeping. Surface validity is equivalent to
the existence of a valid decoded view, and denotation factors through that same view:

```lean (name := viewChecks)
#check @Decimal.decodeView_input
#check @Decimal.IsValid_view
#check @Decimal.computeValue_view
#check @Decimal.parse_eq_some_iff_view
#check @Decimal.parse_eq_none_iff_view
```

The generated engine also connects structural derivations to executable decoding.
{name}`Decimal.Derivation.Decimal.matches` proves that a valid derivation matches the root
production, and {name}`Decimal.Derivation.Decimal.mem_fullParses` records its captures as a
complete parse of the grammar. The Decimal grammar passes the conservative all-input uniqueness
checker, so {name}`Decimal.Derivation.Decimal.decode_render` proves that the decoder recovers
those captures without an ambiguity premise. Finally,
{name}`Decimal.Derivation.Decimal.decodeView_render` proves that decoding recovers the same typed
view:

```lean (name := derivationChecks)
#check @Decimal.Derivation.Decimal.matches
#check @Decimal.Derivation.Decimal.mem_fullParses
#check @Decimal.Derivation.Decimal.decode_render
#check @Decimal.Derivation.Decimal.decodeView_render
#eval
  CedarExamples.Decimal.Decimal.Derivation.Decimal.render
    CedarExamples.Decimal.decimalDerivation
```

# Reconciliation and parser contracts

So far this looks like any parser generator. The difference is that `parser.lean` also
contains machine-checked proofs that the two artifacts above agree — emitted and discharged
automatically, with no human in the loop.

Recognition agrees between the surface predicate and executable engine:

```lean (name := equivCheck)
#check @Decimal.IsWf_equiv
```

```leanOutput equivCheck
Decimal.IsWf_equiv : ∀ (s : String), Decimal.IsWf s ↔ isWf Decimal.grammar Decimal.constraints s
```

The parser contract says every success is valid and correctly valued, every valid matching
value succeeds, and rejection is exactly invalidity:

```lean (name := contractChecks)
#check @Decimal.parse_sound
#check @Decimal.parse_complete
#check @Decimal.parse_reject
```

Compiler-generated theorems use only {name}`propext`, {name}`Classical.choice`, and
{name}`Quot.sound`.

# The bridge to Cedar's real parser

Before any static Cedar proof, Triptych emits a checked wrapper. It preserves an external
result only when the generated specification validates the same input and denotation:

```lean (name := checkedExternal)
#check @Decimal.checkedExtParse
#check @Decimal.checkedExtParse_eq_some_iff
#check @Decimal.checkedExtParse_sound_view
```

The unwrapped Cedar parser needs semantic agreement proofs. Decimal discharges all of them:

```lean (name := extChecks)
#check @Decimal.extparse_sound
#check @Decimal.extparse_complete
#check @Decimal.extparse_reject
```

```leanOutput extChecks
Decimal.extparse_sound : ∀ (s : String) (d : Cedar.Spec.Ext.Decimal),
  Cedar.Spec.Ext.Decimal.parse s = some d → Decimal.IsValid s ∧ Decimal.computeValue s = some (Int64.toInt d)
```

{name}`Decimal.extparse_sound` relates Cedar's parser to Triptych's generated
{name}`Decimal.IsValid`, {name}`Decimal.computeValue`, and
{name}`Decimal.View`. Its proof uses the parser-rule registry and the bounded
{lit}`triptych_auto` tactic. The next chapter explains that automation before the book
returns to the remaining semantic boundary.
