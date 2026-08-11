/-
Triptych documentation -- Chapter 4: the integration obligation surface.
-/
import VersoManual
import Outputs.Decimal.soundness

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "The obligation surface: what stays semantic" =>

%%%
tag := "obligations"
shortTitle := "Obligations"
file := "obligations"
%%%

```lean -show
open Triptych
open CedarExamples.Decimal
```

The previous chapters separated generated proof plumbing from format semantics. This chapter
describes the integration obligations in {lit}`soundness.lean` and what Triptych derives
after they are proved.

# No formal oracle, no invented proof

Facts in {lit}`spec.lean` and {lit}`parser.lean` relate artifacts that Triptych generated.
The compiler knows their definitions and can emit a proof plan with the code.

An unrelated parser or serializer is different. The claim that Cedar's parser implements this
grammar is exactly the conformance theorem being sought. The choice of one canonical spelling is
also a format decision. Triptych therefore states these semantic claims as typed goals and
derives the surrounding API from their proofs. A new scaffold initially contains placeholders;
the five shipped Cedar formats have replaced every placeholder with a checked proof.

# A checked parser before static proof

When the specification value has decidable equality, a {lit}`parser` clause immediately
generates {name}`Decimal.checkedExtParse`. It retains an external result only when the
generated specification accepts the input and computes the same denotation.

```lean (name := checkedParser)
#check @Decimal.checkedExtParse_eq_some_iff
#check @Decimal.checkedExtParse_sound
#check @Decimal.checkedExtParse_sound_view
```

This wrapper is useful before the external implementation has been verified. Once static
soundness is proved, {name}`Triptych.checkedExternalParse_eq_of_sound` shows that checking
does not change the external parser's behavior.

# The external parser contract

A {lit}`parser p` clause names a function with the shape
{lit}`p : String → Option δ`. The value section's
{lit}`toSpec` conversion maps domain values back to the specification type when necessary.
Three static obligations say that {lit}`p` recognizes exactly the specified language and
computes exactly its denotation:

```lean (name := extTrio)
#check @Decimal.extparse_sound
#check @Decimal.extparse_complete
#check @Decimal.extparse_reject
```

Decimal, Duration, Datetime, IPv4, and IPv6 all discharge this contract. Their proofs combine
named format semantics with the parser registries from the previous chapter. Generated
{lit}`extparse_eq_some_iff_view` and {lit}`extparse_eq_none_iff_view` theorems then expose
the external parser through typed views.

# The printer witness

A {lit}`printer toStr` clause names one canonical serializer. Its central obligation is one
typed witness:

```lean (name := encodeObl)
#check @Decimal.encode_view
```

{name}`Decimal.encode_view` says that every serialized value decodes to a valid view whose
converted denotation is the original domain value. Triptych derives acceptance and
specification-value projections for compatibility:

```lean (name := encodeDerived)
#check @Decimal.encode_accepted
#check @Decimal.encode_value
```

Which accepted spelling is canonical -- {lit}`"1.5"` or {lit}`"1.5000"` -- cannot be
inferred from the recognizing grammar.

# Conversion guards and the silent-wrap trap

Decimal uses {lit}`ofSpec Int64.ofInt` and {lit}`toSpec Int64.toInt`. The generated parser
returns the domain type, while the readable specification remains an {name}`Int` fixed-point
value. One accepted-value obligation guards the potentially lossy direction:

```lean (name := conversionObls)
#check @Decimal.toSpec_ofSpec
#check @Decimal.parse_sound_toSpec
```

{name}`Decimal.toSpec_ofSpec` states
{lit}`Int64.toInt (Int64.ofInt v) = v` only for a value computed from an accepted input.
The range constraint makes that statement true. {name}`Decimal.parse_sound_toSpec` is
derived from it.

Delete the range constraint and the grammar still elaborates, but the conversion obligation
becomes unprovable: a wrapped out-of-range value cannot acquire a false correctness theorem.
The elaborator also warns when {lit}`ofSpec` appears with no value constraint.

The reverse law follows from the serializer witness for domain values:

```lean (name := reverseConversion)
#check @Decimal.ofSpec_toSpec
```

# What the obligations buy

From {name}`Decimal.encode_view`, Triptych derives the generated parser's printer API:

```lean (name := printerThms)
#check @Decimal.parse_toString_roundtrip
#check @Decimal.toString_injective
#check @Decimal.normalize_eq_iff_parse_eq
```

From the external contract and the same witness, it derives the corresponding Cedar theorems:

```lean (name := extPrinterThms)
#check @Decimal.extparse_toString_roundtrip
#check @Decimal.extparse_toString_injective
#check @Decimal.extparse_normalize_eq_iff_parse_eq
```

These are generated proof terms, not additional obligations. A short semantic boundary unlocks
the full parser and printer API.

# Write-once scaffolding

{lit}`soundness.lean` holds user proofs, so it is written once and never overwritten.
{lit}`spec.lean` and {lit}`parser.lean` are regenerated on each DSL elaboration, but only
over files carrying the Triptych sentinel header. Delete {lit}`soundness.lean` deliberately
to re-scaffold it.

Staleness is structural rather than procedural: the soundness file imports generated
definitions. A grammar change retargets its goals, and an obsolete proof stops compiling.

The scaffold has two sections:

- *generated parser* -- {lit}`toSpec_ofSpec` and {lit}`encode_view` when required,
  followed by conversion and {lit}`parse_toString_*` theorems;
- *external parser* -- the {lit}`extparse_*` contract and its typed-view and printer
  consequences.

A block with only an explicit printer gets the first section; only a parser gets the second.
{lit}`printer auto` needs neither because its structural certificate is synthesized and
proved inside {lit}`parser.lean`.
