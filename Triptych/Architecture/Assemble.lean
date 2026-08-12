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
and the value expression. This module defines the generic interpreter predicates:

* `isWf`                 — grammar well-formedness ∧ the `.wellFormed` constraints
* `satisfiesConstraints` — the final-value (`.value`) constraints

Generated formats expose readable capitalized predicates such as `<Name>.IsWf` and
`<Name>.IsValid`. Their reconciliation theorems connect them directly to these generic
interpreter applications; no format-specific lowercase aliases are generated.

Both are phrased against the complete capture map produced by `decode`; scalar entries project
its `Env` view and collection entries retain repeated spans. Constraints of a not-well-formed
string are vacuously satisfied (`decode` fails ⟹ the constraint list is checked against the
empty map, matching "constraints only constrain well-formed strings").

Note: these use `decode` (executable, `partial`) for the environment, so they are
definitions for *running*/bundling. The grammar-only `Triptych.IsWf` lives in `Denote`;
generated equivalence theorems relate it to both the readable layout predicate and the
full format-level `<Name>.IsWf`.
-/

namespace Triptych

/-- The complete capture map `decode` assigns to `s` (empty if not well-formed). -/
def captureMapOf (g : Grammar) (s : String) : CaptureMap :=
  (decode g s).getD []

/-- The scalar capture environment `decode` assigns to `s` (empty if not well-formed). -/
def envOf (g : Grammar) (s : String) : Env :=
  (captureMapOf g s).toEnv

/-- The matched substring of capture `c` in `s`, as a plain `String` — `""` if the capture
    is absent (an omitted optional) or `s` is not well-formed. This is the READABLE
    component reader the generated surface `SatisfiesConstraints` uses, so the spec never
    mentions the internal `Env`/`Option`/`getD` plumbing: `component g s "Integer"` instead
    of `(envOf g s "Integer").getD ""`. Definitionally the latter, so no proof gap. -/
def component (g : Grammar) (s : String) (c : String) : String := (envOf g s c).getD ""

/-- Every matched substring of capture `c` in `s`, in match order — `[]` if `s` is not
    well-formed. The list counterpart of `component`: a `rep`-repeated nonterminal yields one
    entry per iteration (the eight `H16` groups of an IPv6 address), a unique capture a
    singleton. This is the READABLE list reader a `value'` escape uses when it consumes a
    repeated capture as `List String`, so the spec never mentions the internal `CaptureMap`. -/
def componentList (g : Grammar) (s : String) (c : String) : List String :=
  (captureMapOf g s).toEnvList c

/-- Well-formedness: the grammar recognizes `s` AND every constraint that does not explicitly
    reference the final computed value holds on its capture environment. -/
def isWf (g : Grammar) (cs : List ConstraintEntry) (s : String) : Prop :=
  (decode g s).isSome = true ∧ ∀ c ∈ cs, c.wfPart (captureMapOf g s)

/-- The constraints explicitly assigned to the final-value phase hold. -/
def satisfiesConstraints (g : Grammar) (cs : List ConstraintEntry) (s : String) : Prop :=
  ∀ c ∈ cs, c.valPart (captureMapOf g s)

instance (g : Grammar) (cs : List ConstraintEntry) (s : String) :
    Decidable (isWf g cs s) := by unfold isWf; infer_instance
instance (g : Grammar) (cs : List ConstraintEntry) (s : String) :
    Decidable (satisfiesConstraints g cs s) := by unfold satisfiesConstraints; infer_instance

/-! ## Contract obligations

The statements of the parser-correctness theorems (design note §16.1). They relate an
*external, hand-written* parser `parse : String → Option α` to the generated spec, via a
conversion `toSpec : α → Int` that reads the parsed value's `Int` denotation back out (for a
scalar type `α`; e.g. a `Decimal` converts to its stored `Int`).

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
`toSpec`, so there is nothing to prove generically (the content is per-parser).

The value denotation type `β` is arbitrary (not just `Int`): `val : String → Option β` and
`toSpec : α → β` reads the parser's value into that same type. For a scalar format
`β = Int` (the parser's `α` converts to its stored `Int`); for a structured format `β` is the
structured value itself (`SimpleGraph`, adjacency matrix, `IPNet`), often with `α = β` and
`toSpec = id`. -/

variable {α β : Type}

/-- Soundness: if the external `parse` accepts `s` as `a`, then `s` is accepted by the
    (surface) spec and `toSpec a` equals the spec's value. -/
def SoundStmt (accepted : String → Prop) (val : String → Option β)
    (parse : String → Option α) (toSpec : α → β) : Prop :=
  ∀ s a, parse s = some a → accepted s ∧ val s = some (toSpec a)

/-- Completeness (target-parametrized, matching Cedar's `parse_complete`): if `s` is accepted
    by the (surface) spec and its value equals `toSpec a`, then `parse`
    accepts `s` as exactly that `a`. (Cedar phrases the hypothesis with grammar-wf only,
    because its value is `Int64` so the range is implied by `val s = toSpec a`; here `val` is
    arbitrary-precision — range is a separate constraint — so the hypothesis is the full
    `accepted`.) -/
def CompleteStmt (accepted : String → Prop) (val : String → Option β)
    (parse : String → Option α) (toSpec : α → β) : Prop :=
  ∀ s a, accepted s → val s = some (toSpec a) → parse s = some a

/-- Failure characterization: `parse` rejects exactly the strings the (surface) spec does
    not accept. -/
def RejectStmt (accepted : String → Prop) (parse : String → Option α) : Prop :=
  ∀ s, parse s = none ↔ ¬ accepted s

/-! ## The generated correct-by-construction parser

Unlike the `sorry`'d contracts above (which relate an *external* hand-written parser to the
spec), the tool can emit its OWN parser — `computeValue` gated on the decidable acceptance
predicate — and DISCHARGE its three contracts for free. So every generated spec ships a real
verified parser, not just an obligation surface. `gatedParse` yields the value exactly when
the string is accepted; with `toSpec = id` the three `*Stmt`s become the lemmas below, whose only
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

/-! ## Soundness-by-checking for an arbitrary external parser

Static verification of an arbitrary parser implementation is necessarily backend-specific.
`checkedExternalParse` provides the universal fallback: run the external parser, then retain its
result only when the generated reference parser accepts the same input with the same denotation.
The external implementation is therefore outside the trusted base. Completeness is deliberately
not claimed: a parser that rejects a valid string remains free to do so.
-/

/-- Validate an external parser result against the generated reference parser. -/
def checkedExternalParse (accepted : String → Prop) [DecidablePred accepted]
    [DecidableEq β] (val : String → Option β) (parse : String → Option α)
    (toSpec : α → β) (s : String) : Option α :=
  match parse s, gatedParse accepted val s with
  | some a, some b => if b = toSpec a then some a else none
  | _, _ => none

/-- Exact success characterization for `checkedExternalParse`. -/
theorem checkedExternalParse_eq_some_iff
    (accepted : String → Prop) [DecidablePred accepted] [DecidableEq β]
    (val : String → Option β) (parse : String → Option α) (toSpec : α → β)
    (s : String) (a : α) :
    checkedExternalParse accepted val parse toSpec s = some a ↔
      parse s = some a ∧ accepted s ∧ val s = some (toSpec a) := by
  by_cases hacc : accepted s
  · cases hp : parse s <;> cases hv : val s
    all_goals simp [checkedExternalParse, gatedParse, hacc, hp, hv]
    constructor
    · rintro ⟨hb, ha⟩
      subst a
      exact ⟨rfl, hb⟩
    · rintro ⟨ha, hb⟩
      subst a
      exact ⟨hb, rfl⟩
  · cases hp : parse s <;> simp [checkedExternalParse, gatedParse, hacc, hp]

/-- Every result returned by the checked wrapper satisfies the generated specification. -/
theorem checkedExternalParse_sound
    (accepted : String → Prop) [DecidablePred accepted] [DecidableEq β]
    (val : String → Option β) (parse : String → Option α) (toSpec : α → β) :
    SoundStmt accepted val (checkedExternalParse accepted val parse toSpec) toSpec := by
  intro s a h
  exact (checkedExternalParse_eq_some_iff accepted val parse toSpec s a).mp h |>.2

/-- Once the original parser is statically proved sound, checking is observationally free. -/
theorem checkedExternalParse_eq_of_sound
    (accepted : String → Prop) [DecidablePred accepted] [DecidableEq β]
    (val : String → Option β) (parse : String → Option α) (toSpec : α → β)
    (hsound : SoundStmt accepted val parse toSpec) :
    checkedExternalParse accepted val parse toSpec = parse := by
  funext s
  cases hp : parse s with
  | none => simp [checkedExternalParse, hp]
  | some a =>
      obtain ⟨hacc, hval⟩ := hsound s a hp
      have href := gatedParse_complete accepted val s (toSpec a) hacc hval
      simp [checkedExternalParse, hp, href]

/-! ## The domain-valued generated parser: output `δ`, not the spec value type

The spec value type `β` (e.g. the fixed-point `Int`) is convenient for the affine value-DSL and
the overflow constraint, but a real parser should return the domain type `δ` (e.g. `Decimal`).
The user supplies `ofSpec : β → δ` (e.g. `Int64.ofInt`), paired with the external parser's
`toSpec : δ → β` (`Int64.toInt`); the generated parser post-composes it:
`gatedParseOfSpec = (gatedParse …).map ofSpec`, yielding an `Option δ` identical in type to the
external parser. Its three contracts are stated with `(val s).map ofSpec` in place of `val s`.
They need no `toSpec` or range side-condition, so `ofSpec` also works without an external
parser. -/

variable {δ : Type}

/-- The tool's own domain-valued parser: apply `ofSpec` exactly when `accepted` holds.
    Type-identical to a real external parser `String → Option δ`. -/
def gatedParseOfSpec (accepted : String → Prop) [DecidablePred accepted]
    (val : String → Option β) (ofSpec : β → δ) (s : String) : Option δ :=
  (gatedParse accepted val s).map ofSpec

/-- Soundness (`ofSpec` view): if the parser accepts `s` as `d`, then `s` is accepted and
    `(val s).map ofSpec = some d`. -/
theorem gatedParseOfSpec_sound (accepted : String → Prop) [DecidablePred accepted]
    (val : String → Option β) (ofSpec : β → δ) :
    ∀ s d, gatedParseOfSpec accepted val ofSpec s = some d →
      accepted s ∧ (val s).map ofSpec = some d := by
  intro s d h
  unfold gatedParseOfSpec at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨b, hb, hbd⟩ := h
  have hs := gatedParse_sound accepted val s b hb
  refine ⟨hs.1, ?_⟩
  rw [hs.2]; simp only [id_eq, Option.map_some]; rw [hbd]

/-- Completeness (`ofSpec` view): if `s` is accepted and `(val s).map ofSpec = some d`, the
    parser accepts `s` as `d`. -/
theorem gatedParseOfSpec_complete (accepted : String → Prop) [DecidablePred accepted]
    (val : String → Option β) (ofSpec : β → δ) :
    ∀ s d, accepted s → (val s).map ofSpec = some d →
      gatedParseOfSpec accepted val ofSpec s = some d := by
  intro s d hacc hval
  unfold gatedParseOfSpec
  rw [Option.map_eq_some_iff] at hval
  obtain ⟨b, hb, hbd⟩ := hval
  rw [gatedParse_complete accepted val s b hacc hb, Option.map_some, hbd]

/-- Failure characterization: the domain-valued parser rejects exactly the non-accepted
    strings (`ofSpec` cannot introduce failure because `Option.map` preserves `none`). -/
theorem gatedParseOfSpec_reject (accepted : String → Prop) [DecidablePred accepted]
    (val : String → Option β) (ofSpec : β → δ)
    (hsome : ∀ s, accepted s → (val s).isSome) :
    ∀ s, gatedParseOfSpec accepted val ofSpec s = none ↔ ¬ accepted s := by
  intro s
  unfold gatedParseOfSpec
  rw [Option.map_eq_none_iff]
  exact gatedParse_reject accepted val hsome s

/-- `toSpec`-view soundness for the generated domain-valued parser. The conversion law
    `toSpec (ofSpec v) = v` is required only for values of accepted strings, allowing an
    otherwise lossy conversion such as `Int64.ofInt` when a range constraint protects it. -/
theorem gatedParseOfSpec_sound_toSpec (accepted : String → Prop) [DecidablePred accepted]
    (val : String → Option β) (ofSpec : β → δ) (toSpec : δ → β)
    (hToSpecOfSpec :
      ∀ s v, accepted s → val s = some v → toSpec (ofSpec v) = v) :
    ∀ s d, gatedParseOfSpec accepted val ofSpec s = some d →
      accepted s ∧ val s = some (toSpec d) := by
  intro s d h
  obtain ⟨hacc, hmap⟩ := gatedParseOfSpec_sound accepted val ofSpec s d h
  rw [Option.map_eq_some_iff] at hmap
  obtain ⟨v, hv, hvd⟩ := hmap
  subst hvd
  exact ⟨hacc, by rw [hv, hToSpecOfSpec s v hacc hv]⟩

/-! ## The printer side: view encoding / roundtrip / injectivity / normalization (δ-view)

The user supplies ONE canonical serializer `toStr : δ → String` over the DOMAIN type `δ` (e.g.
Cedar's `ToString Decimal`), or a `DerivationPrinter` certificate from which Triptych defines the
serializer as `render ∘ toDerivation`. Multiple certificates may expose different canonical
presentations of the same value. Such a certificate cannot be synthesized for every value
function: an arbitrary denotation need not have a right inverse. BOTH parsers return `Option δ`,
so a selected serializer drives the printer theorems for both, stated in the clean δ-VIEW
`parse (toStr d) = some d` (matching Cedar's `parse_toString_roundtrip` exactly).

For the generated parser, one proof-facing obligation says that serializing a domain value decodes
to a valid typed view with that value as its denotation. The generated parser's typed-view success
theorem turns this directly into roundtrip. Acceptance and value equations are projections of the
same witness, rather than independent printer obligations. External parsers retain the older
acceptance/value interface because their completeness contracts are stated at that boundary.
Injectivity and normalization follow generically from either parser's roundtrip. -/

variable {τ ν : Type}

/-- A serializer builds a valid typed parse view whose denotation is its input domain value.
    `denotation` may include a declared `ofSpec` conversion. -/
def EncodeViewStmt (decodeView : String → Option ν) (valid : ν → Prop)
    (denotation : ν → δ) (toStr : δ → String) : Prop :=
  ∀ d, ∃ v, decodeView (toStr d) = some v ∧ valid v ∧ denotation v = d

/-- A serializer is explained by a valid structural derivation whose rendered text is the
    serializer output and whose projected view denotes the original domain value. -/
def EncodeDerivationStmt (render : τ → String) (structuralValid : τ → Prop)
    (toView : τ → ν) (viewValid : ν → Prop) (denotation : ν → δ)
    (toStr : δ → String) : Prop :=
  ∀ d, ∃ tree, structuralValid tree ∧ render tree = toStr d ∧
    viewValid (toView tree) ∧ denotation (toView tree) = d

/-- A certified presentation policy for semantic values. Two values of this structure may choose
    different derivations (and therefore different strings) while independently proving the same
    parser roundtrip. Automatic printer synthesis is exactly the construction of this certificate. -/
structure DerivationPrinter
    (render : τ → String) (structuralValid : τ → Prop)
    (toView : τ → ν) (viewValid : ν → Prop) (denotation : ν → δ) where
  toDerivation : δ → τ
  structural : ∀ d, structuralValid (toDerivation d)
  valid : ∀ d, viewValid (toView (toDerivation d))
  rightInverse : ∀ d, denotation (toView (toDerivation d)) = d

namespace DerivationPrinter

/-- Render a semantic value according to this certified presentation policy. -/
def toString
    {render : τ → String} {structuralValid : τ → Prop}
    {toView : τ → ν} {viewValid : ν → Prop} {denotation : ν → δ}
    (printer : DerivationPrinter render structuralValid toView viewValid denotation)
    (d : δ) : String :=
  render (printer.toDerivation d)

/-- Every certified presentation policy supplies the structural encoding statement. -/
theorem encodeDerivation
    {render : τ → String} {structuralValid : τ → Prop}
    {toView : τ → ν} {viewValid : ν → Prop} {denotation : ν → δ}
    (printer : DerivationPrinter render structuralValid toView viewValid denotation) :
    EncodeDerivationStmt render structuralValid toView viewValid denotation
      printer.toString := by
  intro d
  exact ⟨printer.toDerivation d, printer.structural d, rfl,
    printer.valid d, printer.rightInverse d⟩

end DerivationPrinter

/-- Turn a structural serializer witness into the flat typed-view witness consumed by generated
    parser roundtrip. The generated `decodeView_render` theorem discharges `decodeRender`. -/
theorem encodeView_of_derivation
    {render : τ → String} {structuralValid : τ → Prop}
    {decodeView : String → Option ν} {toView : τ → ν}
    {viewValid : ν → Prop} {denotation : ν → δ} {toStr : δ → String}
    (decodeRender : ∀ tree, structuralValid tree →
      decodeView (render tree) = some (toView tree))
    (encodeDerivation :
      EncodeDerivationStmt render structuralValid toView viewValid denotation toStr) :
    EncodeViewStmt decodeView viewValid denotation toStr := by
  intro d
  obtain ⟨tree, hstructural, hrender, hvalid, hdenotation⟩ := encodeDerivation d
  refine ⟨toView tree, ?_, hvalid, hdenotation⟩
  rw [← hrender]
  exact decodeRender tree hstructural

/-- Project a certified presentation policy through the generated derivation roundtrip to obtain
    the typed-view witness consumed by parser roundtrip. -/
theorem DerivationPrinter.encodeView
    {render : τ → String} {structuralValid : τ → Prop}
    {decodeView : String → Option ν} {toView : τ → ν}
    {viewValid : ν → Prop} {denotation : ν → δ}
    (printer : DerivationPrinter render structuralValid toView viewValid denotation)
    (decodeRender : ∀ tree, structuralValid tree →
      decodeView (render tree) = some (toView tree)) :
    EncodeViewStmt decodeView viewValid denotation printer.toString :=
  encodeView_of_derivation decodeRender printer.encodeDerivation

/-- Directly turn generated-spec acceptance and value facts for a serialized domain value into
    the converted typed-view witness required by `EncodeViewStmt`. This route has no external
    parser premise. -/
theorem encodeView_of_validValue
    {accepted : String → Prop} {val : String → Option β}
    {toSpec : δ → β} {ofSpec : β → δ}
    {decodeView : String → Option ν} {valid : ν → Prop}
    {denotation : ν → β} {toStr : δ → String} {d : δ}
    (haccepted : accepted (toStr d))
    (hvalue : val (toStr d) = some (toSpec d))
    (acceptedView :
      ∀ s, accepted s ↔ ∃ v, decodeView s = some v ∧ valid v)
    (valueView : ∀ s, val s = (decodeView s).map denotation)
    (conversion : ofSpec (toSpec d) = d) :
    ∃ v, decodeView (toStr d) = some v ∧ valid v ∧ ofSpec (denotation v) = d := by
  obtain ⟨v, hview, hvalid⟩ := (acceptedView (toStr d)).mp haccepted
  refine ⟨v, hview, hvalid, ?_⟩
  have hdenotation : denotation v = toSpec d := by
    rw [valueView (toStr d), hview] at hvalue
    exact Option.some.inj hvalue
  rw [hdenotation, conversion]

/-- Identity-denotation specialization of `encodeView_of_validValue`. -/
theorem encodeView_of_validValue_id
    {accepted : String → Prop} {val : String → Option δ}
    {decodeView : String → Option ν} {valid : ν → Prop}
    {denotation : ν → δ} {toStr : δ → String} {d : δ}
    (haccepted : accepted (toStr d))
    (hvalue : val (toStr d) = some d)
    (acceptedView :
      ∀ s, accepted s ↔ ∃ v, decodeView s = some v ∧ valid v)
    (valueView : ∀ s, val s = (decodeView s).map denotation) :
    ∃ v, decodeView (toStr d) = some v ∧ valid v ∧ denotation v = d := by
  obtain ⟨v, hview, hvalid⟩ := (acceptedView (toStr d)).mp haccepted
  refine ⟨v, hview, hvalid, ?_⟩
  rw [valueView (toStr d), hview] at hvalue
  exact Option.some.inj hvalue

/-- Compose a printer roundtrip, parser/spec agreement, and the generated view theorems into
    the converted typed-view witness required by `EncodeViewStmt`. The conversion inverse is
    explicit because it is semantic information that cannot be inferred from either parser. -/
theorem encodeView_of_parserAgreement
    {parser : String → Option δ} {accepted : String → Prop}
    {val : String → Option β} {toSpec : δ → β} {ofSpec : β → δ}
    {decodeView : String → Option ν} {valid : ν → Prop}
    {denotation : ν → β} {toStr : δ → String} {d : δ}
    (printerRoundtrip : ∀ d, parser (toStr d) = some d)
    (parserAgrees :
      ∀ s d, parser s = some d ↔ accepted s ∧ val s = some (toSpec d))
    (acceptedView :
      ∀ s, accepted s ↔ ∃ v, decodeView s = some v ∧ valid v)
    (valueView : ∀ s, val s = (decodeView s).map denotation)
    (conversion : ofSpec (toSpec d) = d) :
    ∃ v, decodeView (toStr d) = some v ∧ valid v ∧ ofSpec (denotation v) = d := by
  obtain ⟨haccepted, hvalue⟩ :=
    (parserAgrees (toStr d) d).mp (printerRoundtrip d)
  exact
    encodeView_of_validValue
      haccepted hvalue acceptedView valueView conversion

/-- Identity-denotation specialization of `encodeView_of_parserAgreement`. -/
theorem encodeView_of_parserAgreement_id
    {parser : String → Option δ} {accepted : String → Prop}
    {val : String → Option δ} {decodeView : String → Option ν}
    {valid : ν → Prop} {denotation : ν → δ} {toStr : δ → String} {d : δ}
    (printerRoundtrip : ∀ d, parser (toStr d) = some d)
    (parserAgrees :
      ∀ s d, parser s = some d ↔ accepted s ∧ val s = some d)
    (acceptedView :
      ∀ s, accepted s ↔ ∃ v, decodeView s = some v ∧ valid v)
    (valueView : ∀ s, val s = (decodeView s).map denotation) :
    ∃ v, decodeView (toStr d) = some v ∧ valid v ∧ denotation v = d := by
  obtain ⟨haccepted, hvalue⟩ :=
    (parserAgrees (toStr d) d).mp (printerRoundtrip d)
  exact encodeView_of_validValue_id haccepted hvalue acceptedView valueView

/-- A typed-view success characterization and one `EncodeViewStmt` prove generated-parser
    roundtrip directly. -/
theorem parse_toString_roundtrip_of_encodeView
    {parse : String → Option δ} {decodeView : String → Option ν}
    {valid : ν → Prop} {denotation : ν → δ} {toStr : δ → String}
    (parseView :
      ∀ s d, parse s = some d ↔
        ∃ v, decodeView s = some v ∧ valid v ∧ denotation v = d)
    (encodeView : EncodeViewStmt decodeView valid denotation toStr) (d : δ) :
    parse (toStr d) = some d :=
  (parseView (toStr d) d).2 (encodeView d)

/-- Obligation 1: the serialized form of any domain value is accepted by the spec. -/
def EncodeAcceptedStmt (accepted : String → Prop) (toStr : δ → String) : Prop :=
  ∀ d, accepted (toStr d)

/-- Obligation 2 (`toSpec` view): serialize-then-evaluate recovers `toSpec d`. -/
def EncodeValueStmt (val : String → Option β) (toStr : δ → String)
    (toSpec : δ → β) : Prop :=
  ∀ d, val (toStr d) = some (toSpec d)

/-- δ-view roundtrip for an EXTERNAL parser: parsing a serialized `d` recovers `d`
    (`parse (toStr d) = some d`). Derived from the parser's `complete` + the two encode
    obligations — exactly Cedar's `parse_toString_roundtrip = parse_complete …`. -/
theorem parse_toString_roundtrip {accepted : String → Prop} {val : String → Option β}
    {parse : String → Option δ} {toStr : δ → String} {toSpec : δ → β}
    (complete : ∀ s d, accepted s → val s = some (toSpec d) → parse s = some d)
    (hAcc : EncodeAcceptedStmt accepted toStr)
    (hVal : EncodeValueStmt val toStr toSpec) (d : δ) :
    parse (toStr d) = some d :=
  complete (toStr d) d (hAcc d) (hVal d)

/-- δ-view roundtrip for the generated parser without `ofSpec` (`β`-typed):
    `gatedParse … (toStr b) = some b`. Just `gatedParse_complete` on the encode obligations
    (here `toSpec = id`, so `EncodeValueStmt` reads `val (toStr b) = some b`). -/
theorem gatedParse_toString_roundtrip (accepted : String → Prop) [DecidablePred accepted]
    (val : String → Option β) {toStr : β → String}
    (hAcc : ∀ b, accepted (toStr b)) (hVal : ∀ b, val (toStr b) = some b) (b : β) :
    gatedParse accepted val (toStr b) = some b :=
  gatedParse_complete accepted val (toStr b) b (hAcc b) (hVal b)

/-- δ-view roundtrip for the generated domain-valued parser. Besides the encode obligations,
    this requires `ofSpec (toSpec d) = d`. -/
theorem gatedParseOfSpec_toString_roundtrip
    {accepted : String → Prop} [DecidablePred accepted]
    {val : String → Option β} {toStr : δ → String}
    {toSpec : δ → β} {ofSpec : β → δ}
    (hAcc : EncodeAcceptedStmt accepted toStr)
    (hVal : EncodeValueStmt val toStr toSpec)
    (hOfSpecToSpec : ∀ d, ofSpec (toSpec d) = d) (d : δ) :
    gatedParseOfSpec accepted val ofSpec (toStr d) = some d := by
  apply gatedParseOfSpec_complete accepted val ofSpec (toStr d) d (hAcc d)
  rw [hVal d, Option.map_some, hOfSpecToSpec d]

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
