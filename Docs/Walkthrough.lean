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

- *Shape* — an optional minus sign, one or more integer digits, a dot, one to four fraction
  digits. This is the grammar.
- *Meaning* — sign times (integer part scaled by 10⁴ plus fraction part scaled to fill four
  places). This is the value clause.
- *Bounds* — the value must fit in `Int64`. This is the constraint clause.

The authored block is in {lit}`cedar-examples/Inputs/Decimal.lean`:

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

Two details worth pausing on before we look at the output:

*The dedicated sign production.* {lit}`Sign ::= sign` gives the optional minus sign its own
capture. The decoder records named productions, so an anonymous optional literal would not be
available to the value expression. The DSL rejects the unsafe sign shape.

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

The root predicate composes the productions, and {name}`Decimal.IsValid` conjoins shape with
the final-value range:

```lean (name := isValidCheck)
#check (Decimal.IsValid : String → Prop)
```

The same proof-free file also contains typed structures. {name}`Decimal.View` has
{lit}`input`, {lit}`sign`, {lit}`natural`, and {lit}`fraction` fields. The root
derivation mirrors grammar structure: alternatives become constructors and the optional sign
becomes an {name}`Option`.

```lean (name := typedSurface)
#check Decimal.View
#check Decimal.Derivation.Decimal
#check @Decimal.Derivation.Decimal.render
#check @Decimal.Derivation.Decimal.Valid
```

# Artifact two: the engine and the verified parser

The second generated file contains the executable side. {name}`decode` walks the grammar
and extracts named captures:

```lean (name := decodeEval)
#eval decode Decimal.grammar "1.5"
```

```leanOutput decodeEval
some [("Sign", ""), ("Natural", "1"), ("Fraction", "5")]
```

{name}`Decimal.computeValue` evaluates the specification value. The specialized
{name}`Decimal.parse` gates that computation on validity and maps the result through
{name}`Int64.ofInt`:

```lean (name := parseEvals)
#eval Decimal.computeValue "1.5"  -- spec value: ×10⁴
#eval Decimal.parse "1.5"         -- as a Decimal
#eval Decimal.parse "-0.15"       -- sign corner case
```

Grammar and constraint failures both appear as {name}`Option.none`:

```lean (name := rejectEvals)
#eval Decimal.parse "1.x"    -- not the grammar
#eval Decimal.parse "922337203685477.5808"  -- overflows
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

A structural derivation can be rendered and decoded back exactly. The Decimal grammar passes
the conservative all-input uniqueness checker, so its roundtrip theorem needs no ambiguity
premise:

```lean (name := derivationChecks)
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
Decimal.IsWf_equiv : ∀ (s : String), Decimal.IsWf s ↔ Decimal.isWf s
```

The parser contract says every success is valid and correctly valued, every valid matching
value succeeds, and rejection is exactly invalidity:

```lean (name := contractChecks)
#check @Decimal.parse_sound
#check @Decimal.parse_complete
#check @Decimal.parse_reject
```

The readable predicates are decidable:

```lean (name := decideEval)
#eval decide (Decimal.IsValid "3.14")
#eval decide (Decimal.IsValid "3.14159")
```

```leanOutput decideEval
true
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
