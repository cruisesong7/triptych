/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Triptych.Architecture.Grammar
import Triptych.Architecture.Denote
import Triptych.Architecture.Constraint
import Triptych.Architecture.Decode
import Triptych.Architecture.Value

/-!
# Assembling the bundled spec

The `triptych` command emits the *ingredients* — the grammar, the constraint list,
and the value expression. This module bundles them into the named predicates of the
design-note contract (§16.1):

* `isWf`                — grammar well-formedness ∧ the string-only (`wfPart`) constraints
* `satisfiesConstraints` — the value-dependent (`valPart`) constraints

The generated spec bundles these two as `isValid := isWf ∧ satisfiesConstraints` (⟺ the
parser accepts the string); see `Emit.lean`.

Both are phrased against the capture environment produced by `decode`. Constraints
of a not-well-formed string are vacuously satisfied (`decode` fails ⟹ no env ⟹ the
constraint list is checked against the empty environment, matching "constraints only
constrain well-formed strings").

Note: these use `decode` (executable, `partial`) for the environment, so they are
definitions for *running*/bundling, not yet the proof-facing forms. The proof-facing
`IsWf` lives in `Denote`; relating the two is part of the contract-theorem milestone.
-/

namespace Triptych

/-- The capture environment `decode` assigns to `s` (empty if not well-formed). -/
def envOf (g : Grammar) (s : String) : Env :=
  match decode g s with
  | some m => m.toEnv
  | none   => fun _ => none

/-- The matched substring of capture `c` in `s`, as a plain `String` — `""` if the capture
    is absent (an omitted optional) or `s` is not well-formed. This is the READABLE
    component reader the generated surface `SatisfiesConstraints` uses, so the spec never
    mentions the internal `Env`/`Option`/`getD` plumbing: `component g s "Integer"` instead
    of `(envOf g s "Integer").getD ""`. Definitionally the latter, so no proof gap. -/
def component (g : Grammar) (s : String) (c : String) : String := (envOf g s c).getD ""

/-- Well-formedness: the grammar recognizes `s` AND every string-only constraint
    (`wfPart`) holds on its capture environment. -/
def isWf (g : Grammar) (cs : List ConstraintEntry) (s : String) : Prop :=
  (decode g s).isSome = true ∧ ∀ c ∈ cs, c.wfPart (envOf g s)

/-- The value-dependent constraints hold on `s`'s capture environment. -/
def satisfiesConstraints (g : Grammar) (cs : List ConstraintEntry) (s : String) : Prop :=
  ∀ c ∈ cs, c.valPart (envOf g s)

instance (g : Grammar) (cs : List ConstraintEntry) (s : String) :
    Decidable (isWf g cs s) := by unfold isWf; infer_instance
instance (g : Grammar) (cs : List ConstraintEntry) (s : String) :
    Decidable (satisfiesConstraints g cs s) := by unfold satisfiesConstraints; infer_instance

/-! ## Contract obligations

The statements of the parser-correctness theorems (design note §16.1). They relate an
*external, hand-written* parser `parse : String → Option α` to the generated spec, via a
projection `π : α → Int` that reads the parsed value's `Int` denotation back out (for a
scalar type `α`; e.g. a `Decimal` projects to its stored `Int`).

**Stated over the SURFACE spec** (not the engine bundle): the acceptance predicate is
passed as an abstract `accepted : String → Prop` and the value function as
`value : String → Option Int`. The generated command instantiates these with the READABLE
`<Name>.IsValid` and `<Name>.computeValue` — so the human-facing contract says exactly
"the real parser accepts iff the readable spec is valid, with matching value". The proof is
still discharged operationally by bridging the surface `IsValid` to `decode` via
`<Name>.IsWf_equiv` (the surface `SatisfiesConstraints` is already decode-based); i.e. the
statement is surface-level, the proof drops to the engine where it is tractable.

These are the theorem *statements* the command emits as `sorry`d obligations — the
proof-facing deliverable. They are parameterized over arbitrary `accepted`/`value`/`parse`/
`π`, so there is nothing to prove generically (the content is per-parser).

The value denotation type `β` is arbitrary (not just `Int`): `val : String → Option β` and
the projection `π : α → β` read the parser's value into that same type. For a scalar format
`β = Int` (the parser's `α` projects to its stored `Int`); for a structured format `β` is the
structured value itself (`SimpleGraph`, adjacency matrix, `IPNet`), often with `α = β` and
`π = id`. -/

variable {α β : Type}

/-- Soundness: if the external `parse` accepts `s` as `a`, then `s` is accepted by the
    (surface) spec and the parsed value's projection equals the spec's value. -/
def SoundStmt (accepted : String → Prop) (val : String → Option β)
    (parse : String → Option α) (π : α → β) : Prop :=
  ∀ s a, parse s = some a → accepted s ∧ val s = some (π a)

/-- Completeness (target-parametrized, matching Cedar's `parse_complete`): if `s` is accepted
    by the (surface) spec and its value equals the projection of a given `a`, then `parse`
    accepts `s` as exactly that `a`. (Cedar phrases the hypothesis with grammar-wf only,
    because its value is `Int64` so the range is implied by `val s = π a`; here `val` is
    arbitrary-precision — range is a separate constraint — so the hypothesis is the full
    `accepted`.) -/
def CompleteStmt (accepted : String → Prop) (val : String → Option β)
    (parse : String → Option α) (π : α → β) : Prop :=
  ∀ s a, accepted s → val s = some (π a) → parse s = some a

/-- Failure characterization: `parse` rejects exactly the strings the (surface) spec does
    not accept. -/
def RejectStmt (accepted : String → Prop) (parse : String → Option α) : Prop :=
  ∀ s, parse s = none ↔ ¬ accepted s

/-! ## The generated correct-by-construction parser

Unlike the `sorry`'d contracts above (which relate an *external* hand-written parser to the
spec), the tool can emit its OWN parser — `computeValue` gated on the decidable acceptance
predicate — and DISCHARGE its three contracts for free. So every generated spec ships a real
verified parser, not just an obligation surface. `gatedParse` yields the value exactly when
the string is accepted; with `π = id` the three `*Stmt`s become the lemmas below, whose only
per-spec input is `hsome` (accepted ⟹ value present), itself uniform (see `Syntax.lean`). -/

/-- The tool's own parser: yield the value exactly when `accepted` holds. -/
def gatedParse (accepted : String → Prop) [DecidablePred accepted]
    (val : String → Option β) (s : String) : Option β :=
  if decide (accepted s) then val s else none

theorem gatedParse_sound (accepted : String → Prop) [DecidablePred accepted]
    (val : String → Option β) :
    SoundStmt accepted val (gatedParse accepted val) id := by
  intro s a h
  unfold gatedParse at h
  simp only [decide_eq_true_eq] at h
  by_cases hv : accepted s
  · rw [if_pos hv] at h; exact ⟨hv, h⟩
  · rw [if_neg hv] at h; exact absurd h (by simp)

theorem gatedParse_complete (accepted : String → Prop) [DecidablePred accepted]
    (val : String → Option β) :
    CompleteStmt accepted val (gatedParse accepted val) id := by
  intro s a hv hval
  unfold gatedParse
  simp only [decide_eq_true_eq]
  rw [if_pos hv]; exact hval

theorem gatedParse_reject (accepted : String → Prop) [DecidablePred accepted]
    (val : String → Option β) (hsome : ∀ s, accepted s → (val s).isSome) :
    RejectStmt accepted (gatedParse accepted val) := by
  intro s
  unfold gatedParse
  simp only [decide_eq_true_eq]
  by_cases hv : accepted s
  · rw [if_pos hv]
    constructor
    · intro h; exact absurd (hsome s hv) (by rw [h]; simp)
    · intro h; exact absurd hv h
  · rw [if_neg hv]; simp [hv]

/-! ## The lifted generated parser: output the value type `δ`, not the spec's `Int`

The spec value type `β` (e.g. the fixed-point `Int`) is convenient for the affine value-DSL and
the overflow constraint, but a real parser should return the domain type `δ` (e.g. `Decimal`).
The user supplies a *lift* `σ : β → δ` (e.g. `Int64.ofInt`), a section of the external parser's
projection `π : δ → β` (`Int64.toInt`); the generated parser post-composes it:
`gatedParseLift = (gatedParse …).map σ`, yielding an `Option δ` identical in TYPE to the external
parser. Its three contracts are the σ-VIEW analogues — stated with `(val s).map σ` in place of
`val s` — which are exactly what `.map σ`-ing `gatedParse`'s contracts gives, with NO `π` and NO
range side-condition (so `lift` also works standalone, without any external parser). -/

variable {δ : Type}

/-- The tool's own parser, lifted to the domain type `δ`: yield `σ` of the value exactly when
    `accepted` holds. Type-identical to a real external parser `String → Option δ`. -/
def gatedParseLift (accepted : String → Prop) [DecidablePred accepted]
    (val : String → Option β) (σ : β → δ) (s : String) : Option δ :=
  (gatedParse accepted val s).map σ

/-- Soundness (σ-view): if the lifted parser accepts `s` as `d`, then `s` is accepted and the
    lifted value equals `some d` (`(val s).map σ = some d`). -/
theorem gatedParseLift_sound (accepted : String → Prop) [DecidablePred accepted]
    (val : String → Option β) (σ : β → δ) :
    ∀ s d, gatedParseLift accepted val σ s = some d → accepted s ∧ (val s).map σ = some d := by
  intro s d h
  unfold gatedParseLift at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨b, hb, hbd⟩ := h
  have hs := gatedParse_sound accepted val s b hb
  refine ⟨hs.1, ?_⟩
  rw [hs.2]; simp only [id_eq, Option.map_some]; rw [hbd]

/-- Completeness (σ-view): if `s` is accepted and the lifted value is `some d`, the lifted parser
    accepts `s` as `d`. -/
theorem gatedParseLift_complete (accepted : String → Prop) [DecidablePred accepted]
    (val : String → Option β) (σ : β → δ) :
    ∀ s d, accepted s → (val s).map σ = some d → gatedParseLift accepted val σ s = some d := by
  intro s d hacc hval
  unfold gatedParseLift
  rw [Option.map_eq_some_iff] at hval
  obtain ⟨b, hb, hbd⟩ := hval
  rw [gatedParse_complete accepted val s b hacc hb, Option.map_some, hbd]

/-- Failure characterization: the lifted parser rejects exactly the non-accepted strings
    (`σ` never introduces failure — `Option.map` preserves `none`). -/
theorem gatedParseLift_reject (accepted : String → Prop) [DecidablePred accepted]
    (val : String → Option β) (σ : β → δ) (hsome : ∀ s, accepted s → (val s).isSome) :
    ∀ s, gatedParseLift accepted val σ s = none ↔ ¬ accepted s := by
  intro s
  unfold gatedParseLift
  rw [Option.map_eq_none_iff]
  exact gatedParse_reject accepted val hsome s

/-- π-view soundness for the GENERATED lifted parser (the analogue of the external parser's
    `extparse_sound`): what the parser returns, projected back through `π`, IS the spec value
    (`val s = some (π d)`). `gatedParseLift_sound` alone gives only the σ-view
    (`(val s).map σ = some d`), which stays consistent even when `σ` WRAPS an out-of-range
    value — the σ-view can't tell. The upgrade needs `hFaith`, faithfulness of the lift on
    accepted values (`π (σ v) = v` — the dual of `lift_section`'s `σ (π d) = d`, restricted to
    the accepted language, where alone it can hold for a wrapping `σ` like `Int64.ofInt`).
    Emitted as the `lift_faithful` obligation: its proof is exactly what the range constraint
    (`value ∈ [lo, hi]`) exists to provide, so a missing constraint makes it UNPROVABLE —
    the silent-wrap trap surfaces as a permanent `sorry`. -/
theorem gatedParseLift_sound_proj (accepted : String → Prop) [DecidablePred accepted]
    (val : String → Option β) (σ : β → δ) (π : δ → β)
    (hFaith : ∀ s v, accepted s → val s = some v → π (σ v) = v) :
    ∀ s d, gatedParseLift accepted val σ s = some d → accepted s ∧ val s = some (π d) := by
  intro s d h
  obtain ⟨hacc, hmap⟩ := gatedParseLift_sound accepted val σ s d h
  rw [Option.map_eq_some_iff] at hmap
  obtain ⟨v, hv, hvd⟩ := hmap
  subst hvd
  exact ⟨hacc, by rw [hv, hFaith s v hacc hv]⟩

/-! ## The printer side: `toString` roundtrip / injectivity / normalization (δ-view)

The user supplies ONE canonical serializer `toStr : δ → String` over the DOMAIN type `δ` (e.g.
Cedar's `ToString Decimal`); a serializer can't be synthesized — the canonical form is a choice.
BOTH parsers return `Option δ`, so this single serializer drives the printer theorems for both,
stated in the clean δ-VIEW `parse (toStr d) = some d` (matching Cedar's `parse_toString_roundtrip`
exactly). Roundtrip is derived from the parser's `complete` (as Cedar does), given two encode
obligations phrased through the parser's own projection `π` (`accepted (toStr d)` and
`val (toStr d) = some (π d)`); injectivity and normalization then follow generically from the
roundtrip alone. -/

/-- Obligation 1: the serialized form of any domain value is accepted by the spec. -/
def EncodeAcceptedStmt (accepted : String → Prop) (toStr : δ → String) : Prop :=
  ∀ d, accepted (toStr d)

/-- Obligation 2 (π-view): serialize-then-evaluate recovers the value's projection
    (`val (toStr d) = some (π d)`). For the generated parser `π` is `σ`'s left inverse composed
    away — see `EncodeValueLiftStmt`. -/
def EncodeValueStmt (val : String → Option β) (toStr : δ → String) (π : δ → β) : Prop :=
  ∀ d, val (toStr d) = some (π d)

/-- δ-view roundtrip for an EXTERNAL parser: parsing a serialized `d` recovers `d`
    (`parse (toStr d) = some d`). Derived from the parser's `complete` + the two encode
    obligations — exactly Cedar's `parse_toString_roundtrip = parse_complete …`. -/
theorem parse_toString_roundtrip {accepted : String → Prop} {val : String → Option β}
    {parse : String → Option δ} {toStr : δ → String} {π : δ → β}
    (complete : ∀ s d, accepted s → val s = some (π d) → parse s = some d)
    (hAcc : EncodeAcceptedStmt accepted toStr) (hVal : EncodeValueStmt val toStr π) (d : δ) :
    parse (toStr d) = some d :=
  complete (toStr d) d (hAcc d) (hVal d)

/-- δ-view roundtrip for the GENERATED UNLIFTED parser (`β`-typed, the `σ = id` case):
    `gatedParse … (toStr b) = some b`. Just `gatedParse_complete` on the encode obligations
    (here `π = id`, so `EncodeValueStmt` reads `val (toStr b) = some b`). -/
theorem gatedParse_toString_roundtrip (accepted : String → Prop) [DecidablePred accepted]
    (val : String → Option β) {toStr : β → String}
    (hAcc : ∀ b, accepted (toStr b)) (hVal : ∀ b, val (toStr b) = some b) (b : β) :
    gatedParse accepted val (toStr b) = some b :=
  gatedParse_complete accepted val (toStr b) b (hAcc b) (hVal b)

/-- δ-view roundtrip for the GENERATED lifted parser: `gatedParseLift … (toStr d) = some d`.
    Uses `gatedParseLift_complete` + the encode obligations + a `section` fact `σ (π d) = d`
    (`lift_section` — for `Decimal`, `Int64.ofInt_toInt`, unconditional). -/
theorem gatedParseLift_toString_roundtrip {accepted : String → Prop} [DecidablePred accepted]
    {val : String → Option β} {toStr : δ → String} {π : δ → β} {σ : β → δ}
    (hAcc : EncodeAcceptedStmt accepted toStr) (hVal : EncodeValueStmt val toStr π)
    (hSec : ∀ d, σ (π d) = d) (d : δ) :
    gatedParseLift accepted val σ (toStr d) = some d := by
  apply gatedParseLift_complete accepted val σ (toStr d) d (hAcc d)
  rw [hVal d, Option.map_some, hSec d]

/-- The serializer is injective — distinct domain values serialize distinctly. Generic over any
    parser given its δ-view roundtrip. -/
theorem toString_injective {parse : String → Option δ} {toStr : δ → String}
    (rt : ∀ d, parse (toStr d) = some d) (d d' : δ) (h : toStr d = toStr d') : d = d' := by
  have r1 := rt d; have r2 := rt d'
  rw [h] at r1; exact Option.some.inj (r1.symm.trans r2)

/-- Normalization decides value-equality: `(parse s).map toStr` (the canonical-form map, Cedar's
    `normalize`) agrees iff the strings parse equally. Generic over any parser given its δ-view
    roundtrip (via serializer injectivity). -/
theorem normalize_eq_iff_parse_eq {parse : String → Option δ} {toStr : δ → String}
    (rt : ∀ d, parse (toStr d) = some d) (s s' : String) :
    (parse s).map toStr = (parse s').map toStr ↔ parse s = parse s' := by
  constructor
  · intro h
    cases hps : parse s with
    | none => cases hps' : parse s' with
      | none => rfl
      | some d' => rw [hps, hps'] at h; simp at h
    | some d => cases hps' : parse s' with
      | none => rw [hps, hps'] at h; simp at h
      | some d' => rw [hps, hps'] at h
                   simp only [Option.map_some, Option.some.injEq] at h
                   rw [toString_injective rt d d' h]
  · intro h; rw [h]

end Triptych
