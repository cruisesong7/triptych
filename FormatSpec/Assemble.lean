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

import FormatSpec.Grammar
import FormatSpec.Denote
import FormatSpec.Constraint
import FormatSpec.Decode
import FormatSpec.Value

/-!
# Assembling the bundled spec

The `format_spec` command emits the *ingredients* — the grammar, the constraint list,
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

namespace FormatSpec

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

/-! ## The printer side: `toString` roundtrip / injectivity / normalization

A `toString : α → String` (a serializer for the parsed value) can't be synthesized — it is
the value semantics run backwards, so it is USER-SUPPLIED, exactly like the external parser.
But given it and TWO obligations about it — that a serialized value is accepted, and that
serialize-then-`val` round-trips — the tool auto-derives the three printer theorems Cedar
proves (`parse_toString_roundtrip`, `toString_injective`, and the `normalize` equivalence),
via the target-parametrized `complete` (`π = id`; the DSL/escape parser has `val = parse`).

`normalize s := (parse s).map toString` is the canonical-form map. -/

/-- Obligation 1: the serialized form of any value is accepted by the spec. (Cedar's
    `toString_isWfStr`, lifted to the full acceptance predicate.) -/
def EncodeAcceptedStmt (accepted : String → Prop) (toStr : α → String) : Prop :=
  ∀ a, accepted (toStr a)

/-- Obligation 2: serialize-then-evaluate round-trips the value. (Cedar's
    `computeValue_toString`.) -/
def EncodeValueStmt (val : String → Option α) (toStr : α → String) : Prop :=
  ∀ a, val (toStr a) = some a

variable {accepted : String → Prop} [DecidablePred accepted] {val : String → Option α}
  {toStr : α → String}

/-- `parse (toString a) = some a` — parsing a serialized value returns it. Derived from the
    target-parametrized `gatedParse_complete` and the two encode obligations. -/
theorem gatedParse_toString_roundtrip
    (hAcc : EncodeAcceptedStmt accepted toStr) (hVal : EncodeValueStmt val toStr) (a : α) :
    gatedParse accepted val (toStr a) = some a :=
  gatedParse_complete accepted val (toStr a) a (hAcc a) (hVal a)

/-- `toString` is injective — distinct values serialize distinctly. Derived from roundtrip. -/
theorem toString_injective
    (hAcc : EncodeAcceptedStmt accepted toStr) (hVal : EncodeValueStmt val toStr)
    (a a' : α) (h : toStr a = toStr a') : a = a' := by
  have r1 := gatedParse_toString_roundtrip hAcc hVal a
  have r2 := gatedParse_toString_roundtrip hAcc hVal a'
  rw [h] at r1; rw [r1] at r2; exact Option.some.inj r2

/-- Normalization decides equality: two strings share a canonical form iff they parse equal.
    `normalize s := (gatedParse … s).map toStr`. Needs `toString` injective (from the encode
    obligations). -/
theorem normalize_eq_iff_parse_eq
    (hAcc : EncodeAcceptedStmt accepted toStr) (hVal : EncodeValueStmt val toStr) (s s' : String) :
    (gatedParse accepted val s).map toStr = (gatedParse accepted val s').map toStr
      ↔ gatedParse accepted val s = gatedParse accepted val s' := by
  constructor
  · intro h
    cases hps : gatedParse accepted val s with
    | none => cases hps' : gatedParse accepted val s' with
      | none => rfl
      | some d' => rw [hps, hps'] at h; simp at h
    | some d => cases hps' : gatedParse accepted val s' with
      | none => rw [hps, hps'] at h; simp at h
      | some d' => rw [hps, hps'] at h; simp only [Option.map_some, Option.some.injEq] at h
                   rw [toString_injective hAcc hVal d d' h]
  · intro h; rw [h]

end FormatSpec
