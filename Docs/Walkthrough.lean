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

# Artifact two: the executable parser

The readable specification says which strings are valid and what they mean. The generated
{lit}`parser.lean` turns that interface into a function that returns a domain value.

## The generated parser

```lean (name := parseDefinition)
#print Decimal.parse
```

```leanOutput parseDefinition
def Decimal.parse : String → Option Int64 :=
fun s => gatedParseOfSpec Decimal.IsValid Decimal.computeValue Int64.ofInt s
```

Read this definition as a pipeline:

1. {name}`gatedParseOfSpec` uses the generated decision procedure for
   {name}`Decimal.IsValid` to check both the grammar and its semantic constraints.
2. An invalid input returns {name}`Option.none`.
3. For a valid input, {name}`Decimal.computeValue` computes the specification-level {name}`Int`.
4. {name}`Int64.ofInt` converts that value to the parser's {name}`Int64` result.

The first two inputs below succeed. The third violates the grammar, while the fourth has the
right shape but denotes a value outside the {name}`Int64` range:

```lean (name := parseEvals)
#eval
  (Decimal.parse "1.5",
    Decimal.parse "-0.15",
    Decimal.parse "1.x",
    Decimal.parse "922337203685477.5808")
```

```leanOutput parseEvals
(some 15000, some (-1500), none, none)
```

## Executing validity

The generated decision procedure makes the readable predicates directly executable with
{name}`decide`. This separates a grammar failure from a semantic-constraint failure:

```lean (name := validityEvals)
#eval
  let tooLarge := "922337203685477.5808"
  (decide (Decimal.IsWf "3.14159"),
    decide (Decimal.IsWf tooLarge),
    decide (Decimal.SatisfiesConstraints tooLarge),
    decide (Decimal.IsValid tooLarge))
```

```leanOutput validityEvals
(false, true, false, false)
```

The first string fails {name}`Decimal.IsWf` because it has five fraction digits. The second
string is well-formed, but it fails {name}`Decimal.SatisfiesConstraints`, so
{name}`Decimal.IsValid` also returns false.

## Decoding the grammar

Before a value can be computed, the generated engine decodes the input into the grammar's named
captures:

```lean (name := decodeEval)
#eval decode Decimal.grammar "1.5"
```

```leanOutput decodeEval
some [("Sign", ""), ("Natural", "1"), ("Fraction", "5")]
```

This capture map is an engine representation. Ordinary clients use the typed
{name}`Decimal.View` introduced in the next section instead of looking up these string keys.

## Computing the specification value

{name}`Decimal.computeValue` decodes the input and evaluates the DSL's {lit}`value` expression.
Its result is still the specification-level {name}`Int`; it neither applies the semantic
constraint nor converts the result to {name}`Int64`:

```lean (name := computeValueDefinition)
#print Decimal.computeValue
```

```leanOutput computeValueDefinition
def Decimal.computeValue : String → Option Int :=
fun s => computeValue Decimal.grammar Decimal.valueExpr s
```

The distinction is visible in these three results. A valid decimal computes normally, the
well-formed but out-of-range decimal still computes an {name}`Int`, and malformed text cannot be
decoded:

```lean (name := computeValueEvals)
#eval
  (Decimal.computeValue "1.5",
    Decimal.computeValue "922337203685477.5808",
    Decimal.computeValue "1.x")
```

```leanOutput computeValueEvals
(some 15000, some 9223372036854775808, none)
```

## The typed executable view

The engine stores captures in a generic string-keyed map. Without a typed view, every client
proof would have to unfold that representation and reason about lookups such as
{lit}`"Natural" ↦ "12"` and {lit}`"Fraction" ↦ "34"`. The view theorems perform that translation
once: client code obtains a {name}`Decimal.View` and works directly with fields such as
{lit}`v.natural`, {lit}`v.fraction`, and {lit}`v.denotation`.

Surface validity is then equivalent to the existence of a valid decoded view, and value
computation and parser results factor through that same record:

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

## Generated parser contracts

Beyond the executable function, {lit}`parser.lean` contains machine-checked contracts emitted
and proved automatically. Every success is valid and correctly valued, every valid input with a
matching value succeeds, and rejection is exactly invalidity:

```lean (name := contractChecks)
#check @Decimal.parse_sound
#check @Decimal.parse_complete
#check @Decimal.parse_reject
```

Compiler-generated theorems use only {name}`propext`, {name}`Classical.choice`, and
{name}`Quot.sound`.

## Why the parser is correct by construction

Triptych does not generate a format-specific parsing algorithm and then ask the user to prove it
correct. It generates {name}`Decimal.IsValid` and {name}`Decimal.computeValue` from the same DSL
description, then instantiates the already-proved {name}`Triptych.gatedParseOfSpec` combinator
with those two definitions.

The generated contracts are direct applications of generic theorems about that combinator. For
example, the complete proof of the generated parser's soundness has this form:

```lean
example (s : String) (i : Int64) :
    Decimal.parse s = some i →
      Decimal.IsValid s ∧
        (Decimal.computeValue s).map Int64.ofInt = some i :=
  Triptych.gatedParseOfSpec_sound _ _ _ s i
```

The same construction supplies completeness and rejection. When the generated file builds,
Lean checks the parser definition and each proof term together. If the emitted parser no longer
has the behavior required by a generic theorem, the proof does not typecheck.

Here, *correct by construction* has a precise boundary: for every input, the generated parser
implements the authored Triptych validity and value specification. It does not by itself prove
that the human-authored grammar is an accurate transcription of Cedar's intended format. The
independent corpus check at the end of this chapter addresses that separate question.

## The runtime-checked Cedar parser

Before any format-specific proof about Cedar's implementation, {lit}`parser.lean` generates
{name}`Decimal.checkedExtParse`. It first runs Cedar's parser. If Cedar returns a value, the
checked parser keeps that result only when {name}`Decimal.IsValid` accepts the same input and
{name}`Decimal.computeValue` computes the same value after conversion; otherwise it returns
{name}`Option.none`:

```lean (name := checkedExternal)
#check @Decimal.checkedExtParse
#check @Decimal.checkedExtParse_eq_some_iff
#check @Decimal.checkedExtParse_sound_view
```

This provides runtime soundness without first proving Cedar's parser correct. It does not repair
a false rejection: if Cedar returns {name}`Option.none`, the checked parser also returns
{name}`Option.none`.

# Artifact three: proof obligations

{lit}`Outputs/Decimal/soundness.lean` is the write-once third artifact. It contains the
format-specific facts that Triptych cannot infer from the grammar alone. These fall into two
separate groups.

## Generated parser and serializer

The generated {name}`Decimal.parse` needs no parser-correctness proof from the user:
{name}`Decimal.parse_sound`, {name}`Decimal.parse_complete`, and
{name}`Decimal.parse_reject` were already generated and proved in Artifact 2.

Two surrounding choices still require evidence. First, the declared {lit}`ofSpec` and
{lit}`toSpec` functions must be inverse on accepted specification values. For Decimal, the
range constraint makes the potentially lossy {name}`Int64.ofInt` conversion faithful:

```anchor decimalToSpecOfSpecProof (module := Outputs.Decimal.soundness) (project := ".")
theorem Decimal.toSpec_ofSpec (s : String) (v : Int) :
    Decimal.IsValid s → Decimal.computeValue s = some v → Int64.toInt (Int64.ofInt v) = v := by
  intro hvalid hvalue
  obtain ⟨view, hview, hvalidView⟩ := (Decimal.IsValid_view s).mp hvalid
  have hdenotation : Decimal.View.denotation view = v := by
    rw [Decimal.computeValue_view, hview] at hvalue
    exact Option.some.inj hvalue
  have hbounds :
      (-9223372036854775808 : Int) ≤ v ∧ v ≤ (9223372036854775807 : Int) := by
    unfold Decimal.View.Valid Decimal.View.Constraints Decimal.Constraints at hvalidView
    change
      (-9223372036854775808 : Int) ≤ Decimal.View.denotation view ∧
        Decimal.View.denotation view ≤ (9223372036854775807 : Int) at hvalidView
    rw [hdenotation] at hvalidView
    exact hvalidView
  exact Int64.toInt_ofInt_of_le (by omega) (by omega)
```

Second, the declared serializer {name}`decimalToStr` requires one proof obligation,
{name}`Decimal.encode_view`. It says that serializing any {name}`Int64` produces text whose
decoded view is valid and whose specification value, converted with {name}`Int64.ofInt`, equals
the original value:

```anchor decimalEncodeViewProof (module := Outputs.Decimal.soundness) (project := ".")
theorem Decimal.encode_view (i : Int64) :
    ∃ v : Decimal.View,
      Decimal.decodeView (decimalToStr i) = some v ∧
      Decimal.View.Valid v ∧
      Int64.ofInt (Decimal.View.denotation v) = i := by
  triptych_encode [Cedar.Thm.Decimal.parse_toString_roundtrip,
    Decimal.RuleRegistrySoundness.parser_agrees, Decimal.IsValid_view,
    Decimal.computeValue_view, Int64.ofInt_toInt i]
```

This is the single {lit}`toString` obligation. From it, Triptych derives acceptance, value
preservation, generated-parser roundtrip, serializer injectivity, and normalization. For
example:

```anchor decimalParseRoundtripProof (module := Outputs.Decimal.soundness) (project := ".")
theorem Decimal.parse_toString_roundtrip (i : Int64) :
    Decimal.parse (decimalToStr i) = some i :=
  Triptych.parse_toString_roundtrip_of_encodeView
    Decimal.parse_eq_some_iff_view Decimal.encode_view i
```

## External parser

The {lit}`parser Cedar.Spec.Ext.Decimal.parse` clause names an implementation that Triptych did
not generate. Using it directly therefore requires three separate agreement proofs:

- {name}`Decimal.extparse_sound`: every external success is valid and has the specified value.
- {name}`Decimal.extparse_complete`: every valid input with that value is accepted externally.
- {name}`Decimal.extparse_reject`: the external parser returns {name}`Option.none` exactly for
  invalid inputs.

The stronger {name}`Decimal.RuleRegistrySoundness.parser_agrees` theorem is proved separately by
decomposing Cedar's executable parser with reusable parser rules. The generated soundness
obligation is then a direct projection:

```anchor decimalExtparseSoundProof (module := Outputs.Decimal.soundness) (project := ".")
theorem Decimal.extparse_sound (s : String) (d : Cedar.Spec.Ext.Decimal) :
    Cedar.Spec.Ext.Decimal.parse s = some d →
      Decimal.IsValid s ∧ Decimal.computeValue s = some (Int64.toInt d) := by
  simpa only using (Decimal.RuleRegistrySoundness.parser_agrees s d).mp
```

Once those parser obligations and the shared {name}`Decimal.encode_view` serializer certificate
are available, the external parser receives its own roundtrip theorem:

```anchor decimalExtparseRoundtripProof (module := Outputs.Decimal.soundness) (project := ".")
theorem Decimal.extparse_toString_roundtrip (i : Int64) :
    Cedar.Spec.Ext.Decimal.parse (decimalToStr i) = some i :=
  Triptych.parse_toString_roundtrip Decimal.extparse_complete Decimal.encode_accepted
    Decimal.encode_value i
```

This external roundtrip is derived, not a fourth external-parser obligation. It reuses the same
serializer certificate that proves the generated-parser roundtrip. Reusable registry rules help
prove the substantive {name}`Decimal.RuleRegistrySoundness.parser_agrees` theorem, but that
format-specific theorem is not itself registered. Soundness and completeness apply its two
directions directly; the view theorem uses {lit}`simp` with the reusable optional-witness rule
to compose it with generated view facts.

# Independent check against Cedar's test corpus

The generated proof covers every string relative to the Triptych specification. A finite test
suite answers a different question: does that authored specification agree with Cedar on the
cases Cedar's developers chose to test?

{lit}`cedar-examples/ConformanceTests.lean` carries over every valid and invalid parser case from
Cedar's relevant Decimal, Duration, Datetime, and IP address unit-test suites. It also includes
IP strings used by Cedar's rendering, loopback, range, equality, and symbolic tests, plus focused
grammar-boundary cases.

The suite compares:

- the generated parser with Cedar's parser for Decimal, Duration, Datetime, IPv4, and IPv6;
- the readable {lit}`IsValid` specifications with Cedar for IPv4 and IPv6;
- each runtime-checked Cedar parser with Cedar's original parser, confirming that the runtime
  check retains every Cedar result in the corpus; and
- generated and Cedar IPv6 printer roundtrips.

This is 13 suites and 882 checks. All currently pass, and
{lit}`lake build ConformanceTests` fails if any comparison diverges.

The corpus has already exposed a distinction that the construction proof cannot. An early
Duration grammar put the optional minus sign in an anonymous position. The generated parser was
proved correct relative to that grammar, but the grammar computed a negative duration as
positive. Cedar's independently authored cases found the value mismatch. The fix made the sign
a named production and taught the DSL to reject that unsafe shape.

The two layers therefore support different claims:

- the Lean proof establishes parser correctness for all inputs relative to the authored
  specification;
- the Cedar corpus increases confidence that the authored specification matches Cedar, but it
  remains finite test evidence rather than a universal proof.
