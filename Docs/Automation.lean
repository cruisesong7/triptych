/-
Triptych documentation -- Chapter 3: generated proof interfaces and bridge automation.
-/
import VersoManual
import Outputs.Decimal.soundness
import Outputs.IPv6.soundness
import Proofs.Decimal.StructuralDerivation
import Proofs.IPv6.StructuralDerivation

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "Automation: from parser plumbing to semantic facts" =>

%%%
tag := "automation"
shortTitle := "Automation"
file := "automation"
%%%

```lean -show
open Triptych
open CedarExamples.Decimal
open CedarExamples.IPv6
```

Triptych separates three kinds of proof work:

1. Facts determined by the grammar and value clauses are generated and proved outright.
2. Repeated parser plumbing is handled by typed views, rule registries, and bounded tactics.
3. Format-specific semantic facts remain named premises.

This boundary matters. Automation should remove decomposition and bookkeeping without pretending
to discover what an external primitive means.

# Typed views are the proof interface

The raw decoder returns a {name}`Triptych.CaptureMap`. Generated
{name}`Decimal.View` and {name}`IPv6.View` structures expose only the fields used by values
and constraints. Their field types follow the grammar:

- a required scalar capture is {name}`String`;
- an optional scalar capture is {lean}`Option String`;
- a repeated capture requested as {lit}`[H16]` is {lean}`List String`.

The generated normal forms connect those views to acceptance, denotation, success, and rejection:

```lean (name := generatedViewApi)
#check @Decimal.IsValid_view
#check @Decimal.computeValue_view
#check @Decimal.parse_eq_some_iff_view
#check @Decimal.parse_eq_none_iff_view
#check @IPv6.extparse_eq_some_iff_view
```

The external-parser theorem at the end has the shape users usually need: a Cedar success is
equivalent to a decoded, valid view with the expected denotation. Proofs downstream do not need
to unfold the generic decoder.

# Two parser registries

External parser libraries are normalized through two extensible attributes:

- {lit}`@[triptych_parser]` contains terminating successful-path simplification rules;
- {lit}`@[triptych_parser_search]` contains facts suitable for bounded E-matching.

{lit}`triptych_sound [defs] at h` unfolds named parser definitions and inverts a successful
{name}`Option` path. The built-in rules cover bind, map, filter, guards, alternatives,
conditionals, and list traversal. Backends add facts for their own primitives.

{lit}`triptych_auto [facts]` first normalizes with the terminating registry and then runs
bounded {lit}`grind` search with the second registry. Its limits are explicit: six case
splits, E-matching depth four, and 256 instances. Failure leaves a normalized residual goal
instead of launching unbounded search.

Here is the live proof pattern used for Decimal external-parser soundness:

```lean (name := automationExample)
example (s : String) (d : Cedar.Spec.Ext.Decimal) :
    Cedar.Spec.Ext.Decimal.parse s = some d ->
      Decimal.IsValid s ∧
        Decimal.computeValue s = some (Int64.toInt d) := by
  triptych_auto [
    Decimal.RuleRegistrySoundness.parser_agrees]
```

The tactic did not invent decimal semantics. The named
{name}`Decimal.RuleRegistrySoundness.parser_agrees` theorem is the format-specific fact; the
registry composes it with the generated specification.

# Structural derivations

Every production also receives a typed derivation tree. Alternatives become constructors,
optionals become {name}`Option`, and separated repetitions become {name}`List`. Generated
{lit}`render`, {lit}`Valid`, and {lit}`capturesWith` functions preserve syntax and exact
captures.

```lean (name := derivationApi)
#check @Decimal.Derivation.Decimal.mem_fullParses
#check @Decimal.Derivation.Decimal.decodeView_render
#check @IPv6.Derivation.V6Net.mem_fullParses
#eval CedarExamples.IPv6.IPv6.Derivation.V6Net.render
  CedarExamples.IPv6.ipv6CompressedDerivation
```

The last evaluation renders {lit}`"2001:db8::1/64"` from a tree whose two compressed sides
are lists. This is useful for printer proofs: construct syntax directly, prove its structural
validity, and project it to the flat view.

# Printer automation

An explicit serializer has one central obligation, {lit}`encode_view`: its output decodes to
a valid typed view whose converted denotation is the original domain value.

```lean (name := printerApi)
#check @Decimal.encode_view
#check @Decimal.parse_toString_roundtrip
#check @Decimal.toString_injective
#check @Decimal.normalize_eq_iff_parse_eq
```

Three deterministic tactics build that witness from different evidence:

- {lit}`triptych_encode` combines a serializer roundtrip, parser agreement, and generated
  view facts;
- {lit}`triptych_encode_direct` starts from direct generated-spec acceptance and value facts;
- {lit}`triptych_encode_derivation` starts from a valid root derivation.

These tactics compose named theorems; they do not search for serializer semantics. Decimal's
completed witness is a one-command composition:

```
triptych_encode [Cedar.Thm.Decimal.parse_toString_roundtrip,
  Decimal.RuleRegistrySoundness.parser_agrees,
  Decimal.IsValid_view, Decimal.computeValue_view,
  Int64.ofInt_toInt i]
```

{lit}`printer auto` goes one step further and synthesizes a
{name}`Triptych.DerivationPrinter` certificate. Its current proved rule covers total signed
decimal integers with no constraints or domain conversion. Unsupported constrained,
{lit}`ofSpec`, and opaque {lit}`value'` cases fail with source-located diagnostics instead
of emitting an unjustified theorem.

```lean (name := derivationPrinterApi)
#check @Triptych.DerivationPrinter
#check @Triptych.DerivationPrinter.encodeView
#check @Triptych.encodeView_of_derivation
```

# Evidence and next generalizations

The automation is exercised at three levels:

- unit tests cover successful paths through {name}`Option.bind`, map, filter, guards,
  alternatives, list traversal, converted denotations, direct printer proofs, and structural
  derivations;
- Decimal, Duration, Datetime, IPv4, and IPv6 use the registries in their checked proof modules;
- every shipped Cedar {lit}`soundness.lean` file is placeholder-free and builds with the
  standard accepted axioms only.

The next useful generalizations are stronger rules for common parser combinators, diagnostics
that identify a missing registry fact, automatic obligation counts, and reusable semantic
components for bounded integers and separators. Those extensions preserve the same rule:
automation may compose semantic facts, but it must never manufacture them.
