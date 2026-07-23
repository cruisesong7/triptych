/-
Triptych documentation — Chapter 2: the Decimal walkthrough (live generated declarations).
-/
import VersoManual
import Triptych.Examples.Decimal.soundness

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Walkthrough: the Decimal format, end to end" =>

%%%
tag := "walkthrough"
shortTitle := "Decimal walkthrough"
file := "walkthrough"
%%%

This chapter follows one format — Cedar's `decimal` extension type — from its `format_spec`
block to every artifact the compiler generates from it. Everything shown in a Lean code block
below is *live*: it is elaborated against the actual Triptych library when this book is
built, so the outputs and theorem statements you see are the real ones.

```lean -show
open Triptych
open Triptych.Examples.Decimal
```

# The format

A Cedar decimal is a signed fixed-point number with up to four fraction digits: `"1.5"`,
`"-12.34"`, `"922337203685477.5807"`. Cedar stores it as an `Int64` holding the value times
10⁴, so `"1.5"` denotes `15000` and the extreme representable values are
`±922337203685477.580x`.

Three concerns, one per DSL clause:

- *Shape* — an optional minus sign, one or more integer digits, a dot, one to four fraction
  digits. This is the grammar.
- *Meaning* — sign times (integer part scaled by 10⁴ plus fraction part scaled to fill four
  places). This is the value clause.
- *Bounds* — the value must fit in `Int64`. This is the constraint clause.

The block from `Triptych/Examples/Decimal/grammar.lean`:

```
format_spec Decimal where
  grammar
    Decimal  ::= Sign Integer "." Fraction
    Sign     ::= sign
    Integer  ::= digit+
    Fraction ::= digit{1,4}
  value
    Sign * (nat Integer * 10 ^ 4 + nat Fraction * 10 ^ (4 - len Fraction))
    lift Int64.ofInt
  constraints
    value ∈ [Int64.MIN, Int64.MAX]
  parser Cedar.Spec.Ext.Decimal.parse projection Int64.toInt
  printer decimalToStr
  to "Triptych/Examples/Decimal"
```

Two details worth pausing on before we look at the output:

*The dedicated sign production.* `Sign ::= sign` gives the optional minus sign its own named
production. This is not decoration — the decoder records captured substrings under
production names, so a bare optional `"-"` inline in the `Decimal` production would match but
be captured *nowhere*, and the value function could never read it. (An earlier version of the
Duration example had exactly this bug; conformance testing against Cedar's parser caught it,
and the `sign` terminal now enforces the safe shape by construction.) In the value clause, a
bare capture name like `Sign` denotes its ±1 sign; `nat`/`len` read magnitudes and lengths of
ordinary captures.

*The `lift`/`projection` pair.* The spec's value DSL computes an `Int`. Cedar's parser returns
`Decimal` (an `Int64` wrapper). The two clauses bridge the types in opposite directions:
`lift Int64.ofInt` upgrades the *generated* parser's output from `Int` to `Decimal`, and
`projection Int64.toInt` reads the *external* parser's output back down to `Int` so its
contract can be stated against the spec. The constraint `value ∈ [Int64.MIN, Int64.MAX]` is
what makes this honest — more on that in the next chapter.

# Artifact one: the readable spec

Elaborating the block writes `spec.lean` beside it. Each production becomes a plain predicate
over strings, written as an existential decomposition you can compare with the grammar line
by line. The leaf predicates say exactly what you would write by hand — here is the actual
generated `Sign` predicate:

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

and `IsValid` conjoins the well-formedness predicate with the constraints:

```lean (name := isValidCheck)
#check (Decimal.IsValid : String → Prop)
```

This file is deliberately proof-free. It is the *specification* — the thing a human audits by
reading, and the thing every theorem below is stated against.

# Artifact two: the engine and the verified parser

The second file, `parser.lean`, contains the executable side. `decode` walks the grammar over
an input and extracts the named captures:

```lean (name := decodeEval)
#eval decode Decimal.grammar "1.5"
```

```leanOutput decodeEval
some [("Sign", ""), ("Integer", "1"), ("Fraction", "5")]
```

`computeValue` evaluates the value clause over those captures, and `parse` — the generated,
correct-by-construction parser — gates it on the decidable validity check and lifts the
result to `Decimal` via `Int64.ofInt`:

```lean (name := parseEvals)
#eval Decimal.computeValue "1.5"  -- spec value: ×10⁴
#eval Decimal.parse "1.5"         -- as a Decimal
#eval Decimal.parse "-0.15"       -- sign corner case
```

Rejections come in two flavors — a string can fail the *grammar* or fail the *constraint* —
but the parser is a single total function; there is no separate validation pass to forget:

```lean (name := rejectEvals)
#eval Decimal.parse "1.x"    -- not the grammar
#eval Decimal.parse "922337203685477.5808"  -- overflows
```

# Artifact three: the reconciliation proofs

So far this looks like any parser generator. The difference is that `parser.lean` also
contains machine-checked proofs that the two artifacts above agree — emitted and discharged
automatically, with no human in the loop.

Recognition agrees — the engine's deep-embedded grammar denotation accepts exactly the
strings the readable predicate describes:

```lean (name := equivCheck)
#check @Decimal.IsWf_equiv
```

```leanOutput equivCheck
Decimal.IsWf_equiv : ∀ (s : String), IsWf Decimal.grammar s ↔ Decimal.IsWf.Decimal s
```

The parser satisfies its three-part contract — everything it accepts is valid and correctly
valued (*sound*), it accepts everything valid (*complete*), and it returns `none` exactly on
invalid input (*reject*):

```lean (name := contractChecks)
#check @Decimal.parse_sound
#check @Decimal.parse_complete
#check @Decimal.parse_reject
```

And the readable predicates are decidable, so `IsValid` — a `Prop` built from existentials —
can nevertheless be *evaluated*:

```lean (name := decideEval)
#eval decide (Decimal.IsValid "3.14")
#eval decide (Decimal.IsValid "3.14159")
```

```leanOutput decideEval
true
```

All of this is axiom-clean: every proof in `spec.lean` and `parser.lean` depends only on
`propext`, `Classical.choice`, and `Quot.sound`.

# The bridge to Cedar's real parser

The `parser Cedar.Spec.Ext.Decimal.parse projection Int64.toInt` clause declares that an
*external*, hand-written parser — the one actually shipped in cedar-lean — conforms to this
spec. That claim cannot be auto-discharged (the generator did not produce Cedar's parser), so
it is emitted into the third file, `soundness.lean`, as explicit obligations. For Decimal
they have been proven, by bridging to Cedar's own parser-correctness theorems:

```lean (name := extChecks)
#check @Decimal.extparse_sound
#check @Decimal.extparse_complete
#check @Decimal.extparse_reject
```

```leanOutput extChecks
Decimal.extparse_sound : ∀ (s : String) (d : Cedar.Spec.Ext.Decimal),
  Cedar.Spec.Ext.Decimal.parse s = some d → Decimal.IsValid s ∧ Decimal.computeValue s = some (Int64.toInt d)
```

Read `extparse_sound` carefully: it relates *Cedar's* parser to *Triptych's* generated
`IsValid` and `computeValue`. Together with the generated parser's own contract, the two
parsers are provably extensionally equal — they accept the same strings and produce the same
values. The next chapter examines these obligations, and the printer theorems that come with
them, in detail.
