/-
Triptych documentation — Chapter 3: the obligation surface (soundness.lean in depth).
-/
import VersoManual
import Triptych.Examples.Decimal.soundness

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The obligation surface: what stays human, and why" =>

%%%
tag := "obligations"
shortTitle := "Obligations"
file := "obligations"
%%%

```lean -show
open Triptych
open Triptych.Examples.Decimal
```

The previous chapter ended at `soundness.lean`, the third generated file. This chapter is
about its design: which claims the generator refuses to prove for you, why each one is
genuinely a human's claim, and what you get in exchange for proving them.

# The principle: no formal oracle, no auto-proof

Everything in `spec.lean` and `parser.lean` is auto-discharged because both sides of every
theorem are things the generator built — it is reconciling itself with itself, and it can
plan the proof while emitting the definitions. The obligations in `soundness.lean` are
different in kind: each one relates a generated artifact to something *supplied from
outside* — a hand-written parser, a chosen serializer, a chosen pair of type conversions.
For those there is no oracle. The statement "Cedar's parser matches this grammar" is exactly
the format-conformance claim you set out to verify; if the generator could prove it, it would
have to already contain a verified model of Cedar's parser, which is circular.

So the generator does the next best thing: it *states* the obligations precisely, as typed
`sorry`s against the generated spec, and derives everything else from them. The trust
boundary becomes a short, auditable list.

# The external parser trio

A `parser <p> projection <π>` clause names an external parser `p : String → Option δ` and a
projection `π : δ → β` reading its domain values down to the spec's value type. The generator
emits three obligations, jointly saying `p` decides exactly the specified language and
computes exactly the specified value:

```lean (name := extTrio)
#check @Decimal.extparse_sound
#check @Decimal.extparse_complete
#check @Decimal.extparse_reject
```

For Decimal these are proven (not `sorry`d) — discharged by bridging to cedar-lean's own
parser-correctness theorems. Duration's and Datetime's are still open; they are the honest
statement of what remains unverified about those parsers.

# The printer obligations

A `printer <toStr>` clause names one canonical serializer over the domain type. Two encode
obligations state that it hits the spec:

```lean (name := encodeObls)
#check @Decimal.encode_accepted
#check @Decimal.encode_value
```

`encode_accepted` says every serialized value is accepted by the spec; `encode_value` says
parsing a serialized value recovers exactly that value. Together they make `toStr` a right
inverse of the parser — which is precisely what "canonical serializer" should mean, and
precisely what no generator can know without being told, since *which* string form is
canonical (`"1.5"` or `"1.50"`?) is a design decision.

# The lift guards: sections, retractions, and the silent-wrap trap

Decimal's block contains both `lift Int64.ofInt` (upgrading the generated parser's `Int` to
`Decimal`) and `projection Int64.toInt` (reading Cedar's `Decimal` down to `Int`). These are
opposite maps, and two obligations pin down how faithful the round trip is:

```lean (name := liftObls)
#check @Decimal.lift_section
#check @Decimal.lift_faithful
```

`lift_section` (`σ ∘ π = id`) is unconditional: converting an `Int64` to `Int` and back is
the identity. Its dual `lift_faithful` (`π ∘ σ = id`) is *not* unconditional — `Int64.ofInt`
wraps on overflow, so `toInt (ofInt v) = v` holds only when `v` is in `Int64` range. The
obligation is therefore stated *on accepted values only*, and it is provable exactly because
the block's constraint `value ∈ [Int64.MIN, Int64.MAX]` pins every accepted value inside the
faithful domain.

This is a designed trap. Delete the range constraint and the grammar still elaborates, the
parser still runs — but `lift_faithful` becomes unprovable, and the silent-wrap bug (a
too-large decimal quietly wrapping to a wrong `Int64`) surfaces as a permanent `sorry` you
cannot discharge instead of a runtime surprise. The elaborator additionally lints when `lift`
appears with no value constraint at all.

# What the obligations buy

Discharging the obligations is not an end in itself — each one unlocks derived theorems the
generator *can* then prove. From the encode pair and `lift_section`, the printer theorems for
the generated parser:

```lean (name := printerThms)
#check @Decimal.parse_toString_roundtrip
#check @Decimal.toString_injective
#check @Decimal.normalize_eq_iff_parse_eq
```

From `lift_faithful`, the projection-view soundness of the generated parser:

```lean (name := soundProj)
#check @Decimal.parse_sound_proj
```

And from the external trio, the same printer theorems for the *external* parser — Cedar's
`parse_toString_roundtrip` and friends, recovered for free:

```lean (name := extPrinterThms)
#check @Decimal.extparse_toString_roundtrip
#check @Decimal.extparse_toString_injective
#check @Decimal.extparse_normalize_eq_iff_parse_eq
```

The division of labor is strict: the derived theorems are never `sorry`d themselves — they
carry incompleteness only transitively, through the obligations they cite. Prove the
obligations and the whole surface becomes axiom-clean at once.

# Write-once scaffolding

`soundness.lean` holds *your* proofs, so unlike `spec.lean` and `parser.lean` — which are
regenerated on every elaboration — it is written once and never overwritten (delete it to
re-scaffold). This raises an obvious worry: does the file go stale when the grammar changes?

No, and the reason is structural rather than procedural: the obligations are stated against
definitions *imported from* `parser.lean`. Change the grammar and those definitions change
underneath the obligations — proofs that relied on the old shape fail to compile, loudly. The
generator also refuses to overwrite any file that lacks its `Generated by Triptych`
sentinel header, so it can never clobber a hand-written file that happens to share a name.

# Reading a soundness file

The file is partitioned into two banner-delimited sections, generated parser first:

- *soundness · generated parser* — the shared obligations (`encode_*`, `lift_section`, and
  with a lift+projection pair, `lift_faithful`), followed by the derived `parse_toString_*`
  theorems about the generated `parse`.
- *soundness · external parser* — the `extparse_*` trio, followed by the derived
  `extparse_toString_*` theorems about the real external parser (these reuse the generated
  section's `encode_*`, which is why that section comes first).

A block with only a `printer` clause gets just the first section; only a `parser` clause,
just the second. The next chapter turns from the trust story to the expressiveness story:
what the DSL can and cannot say.
