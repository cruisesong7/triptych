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
* `isAccepted`         — `isWf ∧ satisfiesConstraints` (⟺ the parser accepts the string)

All three are phrased against the capture environment produced by `decode`. Constraints
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

/-- The parser accepts `s`: well-formed and all constraints satisfied. -/
def isAccepted (g : Grammar) (cs : List ConstraintEntry) (s : String) : Prop :=
  isWf g cs s ∧ satisfiesConstraints g cs s

instance (g : Grammar) (cs : List ConstraintEntry) (s : String) :
    Decidable (isWf g cs s) := by unfold isWf; infer_instance
instance (g : Grammar) (cs : List ConstraintEntry) (s : String) :
    Decidable (satisfiesConstraints g cs s) := by unfold satisfiesConstraints; infer_instance
instance (g : Grammar) (cs : List ConstraintEntry) (s : String) :
    Decidable (isAccepted g cs s) := by unfold isAccepted; infer_instance

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

/-- Completeness: if `s` is accepted by the (surface) spec with value `v`, then `parse`
    accepts it as some `a` whose projection is `v`. -/
def CompleteStmt (accepted : String → Prop) (val : String → Option β)
    (parse : String → Option α) (π : α → β) : Prop :=
  ∀ s v, accepted s → val s = some v →
    ∃ a, parse s = some a ∧ π a = v

/-- Failure characterization: `parse` rejects exactly the strings the (surface) spec does
    not accept. -/
def RejectStmt (accepted : String → Prop) (parse : String → Option α) : Prop :=
  ∀ s, parse s = none ↔ ¬ accepted s

end FormatSpec
