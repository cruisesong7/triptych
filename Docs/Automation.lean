/-
Triptych documentation -- Chapter 3: discharging proof obligations.
-/
import VersoManual
import Outputs.Decimal.soundness

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "Automation: discharging proof obligations" =>

%%%
tag := "automation"
shortTitle := "Automation"
file := "automation"
%%%

```lean -show
open Triptych
open CedarExamples.Decimal
```

Triptych separates three kinds of proof work:

1. Facts determined by the grammar and value clauses are generated and proved outright.
2. Repeated parser plumbing is handled by typed views, rule registries, and bounded tactics.
3. Format-specific semantic facts remain named premises.

Triptych discharges the first two categories; users supply the third because external code and
domain semantics cannot be determined from the DSL.

# Generated proof interfaces

The previous chapter introduced the two interfaces used by the automation. A typed view hides
the string-keyed capture map and exposes the fields used by values and constraints. Its generated
normal forms connect that record to acceptance, denotation, parser success, and rejection.

A structural derivation retains the grammar choices that a view deliberately forgets. Valid
derivations can be rendered and connected back to decoding, which makes them useful inputs to
printer and roundtrip proofs. Automation works through these generated interfaces rather than
unfolding the generic decoder.

# Two parser registries

External parser libraries are normalized through two extensible attributes:

- {lit}`@[triptych_parser]` contains terminating successful-path simplification rules;
- {lit}`@[triptych_parser_search =]` contains equality or equivalence facts suitable for
  bounded E-matching.

Decimal registers its successful-parser characterization in both:

Its source declaration begins with
{lit}`@[triptych_parser, triptych_parser_search =] theorem parse_eq_some_iff_parts`.

The first attribute gives {lit}`simp` a directed rewrite from parser success to the component
facts. The {lit}`=` in {lit}`triptych_parser_search =` is not assignment syntax: it registers
the theorem as an equality or equivalence rule for {lit}`grind`'s E-matching, which may use it
in either direction.

{lit}`triptych_sound [defs] at h` uses the first registry. In Decimal's
{name}`Decimal.RuleRegistrySoundness.parser_agrees` proof, this one line replaces a raw Cedar
parser equation with the sign, natural-part, fraction-part, and range witnesses proved by
{name}`Decimal.RuleRegistryProof.parse_eq_some_iff_parts`:

```lean (name := decimalParserRegistryUse)
example {s : String} {d : Cedar.Spec.Ext.Decimal}
    (hparse : Cedar.Spec.Ext.Decimal.parse s = some d) :
    ∃ sgn natural fraction,
      (sgn = "-" ∨ sgn = "") ∧
      s = sgn ++ natural ++ "." ++ fraction ∧
      Triptych.IsDigits natural ∧
      Triptych.IsDigitsBetween 1 4 fraction ∧
      Int64.ofInt?
          (Decimal.value sgn natural fraction) =
        some d := by
  triptych_sound at hparse
  obtain
      ⟨sgn, hsign, natural, fraction,
        hs, hnatural, hfraction, hvalue⟩ :=
    hparse
  exact
    ⟨sgn, natural, fraction, hsign, hs,
      hnatural, hfraction, hvalue⟩
```

Without the registration, that proof would have to invoke the long
{name}`Decimal.RuleRegistryProof.parse_eq_some_iff_parts` theorem explicitly at every use
site. The theorem's parser analysis is proved once in {lit}`RuleRegistryProof.lean`; later
proofs consume only its grammar-shaped result.

The second registration matters when proof search needs the equivalence in the other direction.
Here the component facts are enough for {lit}`grind` to recover parser success:

```lean (name := decimalParserSearchUse)
example {s : String} {d : Cedar.Spec.Ext.Decimal}
    (hparts :
      ∃ sgn natural fraction,
        (sgn = "-" ∨ sgn = "") ∧
        s = sgn ++ natural ++ "." ++ fraction ∧
        Triptych.IsDigits natural ∧
        Triptych.IsDigitsBetween 1 4 fraction ∧
        Int64.ofInt?
            (Decimal.value sgn natural fraction) =
          some d) :
    Cedar.Spec.Ext.Decimal.parse s = some d := by
  grind only [triptych_parser_search]
```

{lit}`triptych_auto [local]` first uses the explicitly supplied definitions or facts, normalizes
with the terminating registry, and then runs bounded {lit}`grind` search with the second
registry. The bracketed list is local to that invocation; it does not register its contents.
When a supplied theorem already rewrites the goal, ordinary {lit}`simp` is the clearer proof.

For example, Datetime's
{lit}`Datetime.RuleRegistryProof.parts_of_parse_eq_some` is closed by
{lit}`triptych_auto [datetimeMillis]`: the local definition connects the returned Cedar value to
epoch milliseconds, while the registries supply the reusable parser decomposition and bounded
search. The tactic combines registered facts; it does not invent Datetime semantics.

# Printer automation

An explicit serializer has one central obligation, {lit}`encode_view`: its output decodes to
a valid typed view whose converted denotation is the original domain value.

The automation does not prove arbitrary serializer behavior. Each route starts from evidence
that matches how the serializer was developed, then removes the repeated work of constructing
the existential view witness.

## Existing external parser: {lit}`triptych_encode`

Use {lit}`triptych_encode` when an existing serializer already roundtrips through an external
parser and that parser has an agreement theorem. Decimal supplies exactly those facts:

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

The tactic combines Cedar's serializer roundtrip, Decimal parser agreement, the generated view
normal forms, and the {name}`Int64` conversion inverse. From this one witness, Triptych derives
{name}`Decimal.parse_toString_roundtrip`, serializer injectivity, and normalization results.

## Direct generated-spec facts: {lit}`triptych_encode_direct`

Use {lit}`triptych_encode_direct` when there is no external parser to reconcile. Its inputs say
directly that the serializer output is accepted by the generated specification and computes the
intended value:

```anchor triptychEncodeDirectUse (module := Triptych.Automation.ExternalParserTests) (project := ".")
private theorem triptychEncodeDirect_identity (n : Nat) :
    ∃ view,
      encodeDecodeView (encodePrinter n) = some view ∧
      encodeValid view ∧
      view.denotation = n := by
  triptych_encode_direct [encodePrinter_accepted n, encodePrinter_roundtrip n,
    encodeAccepted_view, encodeValue_view]
```

This regression test has a serializer and generated-spec-style parser but no parser-agreement
theorem. The tactic turns the direct acceptance and value facts into the same {lit}`encode_view`
obligation expected by downstream roundtrip theorems.

## Structural printer: {lit}`triptych_encode_derivation`

Use {lit}`triptych_encode_derivation` when the serializer naturally constructs a grammar
derivation. The proof supplies a valid root tree for each domain value; the generated
{lit}`decodeView_render` theorem projects that tree to the flat view:

```anchor triptychEncodeDerivationUse (module := Triptych.Automation.ExternalParserTests) (project := ".")
private theorem triptychEncodeDerivation_identity (n : Nat) :
    ∃ view,
      encodeDecodeView (encodePrinter n) = some view ∧
      encodeValid view ∧
      view.denotation = n := by
  triptych_encode_derivation [EncodeTree.decodeView_render, encodeDerivation]
```

This route avoids separately proving string-level acceptance and value equations, because those
facts follow from the valid derivation and its rendering theorem.

## Fully synthesized printer: {lit}`printer auto`

{lit}`printer auto` goes one step further: for supported value expressions, Triptych synthesizes
the serializer and its {name}`Triptych.DerivationPrinter` certificate together. The signed-integer
syntax test checks both the emitted spelling and the generated roundtrip theorem:

```anchor printerAutoUse (module := Triptych.Architecture.SyntaxTests) (project := ".")
triptych SignedInteger where
  grammar
    Root   ::= Sign Digits
    Sign   ::= sign
    Digits ::= digit+
  value
    Sign * nat Digits
  printer auto

#guard SignedInteger.toString 0 = "0"
#guard SignedInteger.toString 42 = "42"
#guard SignedInteger.toString (-42) = "-42"
#guard SignedInteger.parse (SignedInteger.toString (-42)) = some (-42)
```

Its current proved rule covers total signed decimal integers with no constraints or domain
conversion. Unsupported constrained, {lit}`ofSpec`, and opaque {lit}`value'` cases fail with
source-located diagnostics instead of emitting an unjustified theorem.
