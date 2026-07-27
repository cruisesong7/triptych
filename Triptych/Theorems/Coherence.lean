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

import Triptych.Architecture.Decode
import Triptych.Theorems.Roundtrip

/-!
# Value coherence: the computed value is grammar-determined, not decoder-selected

`decode` (`Triptych.Architecture.Decode`) enumerates *every* full-consumption parse of the
start production and returns the FIRST one (`List.head?`); `computeValueF`/`computeValue` then
read the value off that one capture map. Recognition (`IsWf`) forgets captures entirely
(`decodeSome_iff_IsWf` quantifies the capture map away), so nothing in the roundtrip forces an
*ambiguous* grammar's several parses to agree on their captures — the returned value is, in
general, **decoder-selected**: an artefact of the `head?` choice.

This module makes that boundary precise and supplies the theorem that erases it *when it can
be erased*. The grammar class admits ambiguity (production alternation, optional items,
backtracking token splits), so coherence cannot be proved unconditionally. Instead:

* `fullParses g s` — the capture maps of every full parse (`decode = head?` of these).
* `CaptureCoherent` / `ValueCoherent` — the hypothesis that all full parses agree (on captures,
  resp. on the computed value). `ValueCoherent` is the weaker, sufficient one.
* `computeValueF_coherent` — THE payoff: under coherence, `computeValueF g valFn s` equals
  `valFn` of **any** full parse's environment. So the value is a property of the grammar +
  string, not of `decode`'s enumeration order.
* `DecodeUnique g s := (fullParses g s).length ≤ 1` — a **decidable** sufficient condition
  (`decide`-able at a concrete grammar/string), letting the tool certify coherence per parse.

None of this weakens the shipped examples: their grammars are unambiguous, so `DecodeUnique`
holds at every accepted string (each `#eval` below returns a one-element `fullParses`). What was
missing — and is provided here — is the *theorem* connecting "one parse" to "the value is
determined", so a future ambiguity check has a proved consequence to attach to.
-/

namespace Triptych

open List

/-- The capture maps of every full-consumption parse of `s` by the start production, in the
    order `decode` enumerates them. `decode g s` is exactly `(fullParses g s).head?` — see
    `decode_eq_head`. Empty when there is no start production or no full parse. -/
def fullParses (g : Grammar) (s : String) : List CaptureMap :=
  match g.startProd? with
  | none   => []
  | some p =>
      ((matchProd g "" g.prods.length p s.toList).filter (fun (_, rem) => rem.isEmpty)).map (·.1)

/-- `decode` returns the FIRST full parse: `decode g s = (fullParses g s).head?`. This is the
    single place the decoder's selection policy (`head?`) is exposed; every coherence result
    below is about when that selection cannot matter. -/
theorem decode_eq_head (g : Grammar) (s : String) :
    decode g s = (fullParses g s).head? := by
  unfold decode fullParses
  cases g.startProd? with
  | none   => rfl
  | some p => exact (List.head?_map).symm

/-- Whatever `decode` returns is one of the full parses. -/
theorem decode_mem_fullParses (g : Grammar) (s : String) {m : CaptureMap}
    (h : decode g s = some m) : m ∈ fullParses g s := by
  rw [decode_eq_head] at h
  exact List.mem_of_head? h

/-- `decode` succeeds iff there is at least one full parse. -/
theorem decode_isSome_iff (g : Grammar) (s : String) :
    (decode g s).isSome = true ↔ fullParses g s ≠ [] := by
  rw [decode_eq_head]
  cases hl : fullParses g s with
  | nil       => simp
  | cons a as => simp

/-! ## Coherence predicates -/

/-- The grammar decodes `s` **capture-coherently**: every full parse yields the same capture
    ENVIRONMENT (`toEnv`). Under this, no value/constraint reader — all of which factor through
    `toEnv` — can tell the parses apart, so `decode`'s first-match choice is immaterial. -/
def CaptureCoherent (g : Grammar) (s : String) : Prop :=
  ∀ m ∈ fullParses g s, ∀ m' ∈ fullParses g s, m.toEnv = m'.toEnv

/-- The grammar decodes `s` **value-coherently** under `valFn`: every full parse yields the same
    value. Weaker than `CaptureCoherent` (two environments may differ only on keys `valFn`
    ignores), and the exact hypothesis `computeValueF_coherent` needs. -/
def ValueCoherent {α : Type} (g : Grammar) (valFn : Env → α) (s : String) : Prop :=
  ∀ m ∈ fullParses g s, ∀ m' ∈ fullParses g s, valFn m.toEnv = valFn m'.toEnv

/-- Capture coherence implies value coherence for every reader (values factor through `toEnv`). -/
theorem ValueCoherent.of_captureCoherent {α : Type} (g : Grammar) (valFn : Env → α) (s : String)
    (h : CaptureCoherent g s) : ValueCoherent g valFn s := by
  intro m hm m' hm'
  rw [h m hm m' hm']

/-- A **decidable** sufficient condition for coherence: at most one full parse. `decide`-able at
    a concrete grammar/string (`fullParses` reduces to a literal list), so the tool can certify a
    given accepted string is unambiguous. -/
def DecodeUnique (g : Grammar) (s : String) : Prop := (fullParses g s).length ≤ 1

instance (g : Grammar) (s : String) : Decidable (DecodeUnique g s) := by
  unfold DecodeUnique; infer_instance

/-- At most one full parse ⟹ capture-coherent (any two members of a ≤1-element list are equal). -/
theorem CaptureCoherent.of_unique (g : Grammar) (s : String) (h : DecodeUnique g s) :
    CaptureCoherent g s := by
  intro m hm m' hm'
  unfold DecodeUnique at h
  -- a list of length ≤ 1 has all its members equal
  match hl : fullParses g s, h with
  | [],      _ => simp [hl] at hm
  | [a],     _ =>
      rw [hl] at hm hm'
      simp only [List.mem_singleton] at hm hm'
      rw [hm, hm']
  | _ :: _ :: _, h => simp at h

/-! ## The payoff -/

/-- **Value coherence.** If every full parse of `s` agrees on the value (`ValueCoherent`), then
    `computeValueF g valFn s` equals `valFn` of the environment of **any** full parse `m` — the
    value is determined by the grammar and string, independent of `decode`'s enumeration order.
    (`decode`'s `head?`-selected parse is *some* full parse, and coherence equates its value to
    `m`'s.) -/
theorem computeValueF_coherent {α : Type} (g : Grammar) (valFn : Env → α) (s : String)
    (hcoh : ValueCoherent g valFn s) {m : CaptureMap} (hm : m ∈ fullParses g s) :
    computeValueF g valFn s = some (valFn m.toEnv) := by
  -- fullParses is nonempty (it contains `m`), so decode = some (head), a full parse.
  have hne : fullParses g s ≠ [] := List.ne_nil_of_mem hm
  have hsome : (decode g s).isSome = true := (decode_isSome_iff g s).mpr hne
  obtain ⟨m₀, hm₀⟩ := Option.isSome_iff_exists.mp hsome
  have hmem₀ : m₀ ∈ fullParses g s := decode_mem_fullParses g s hm₀
  unfold computeValueF
  rw [hm₀]
  simp only [Option.map_some]
  rw [hcoh m₀ hmem₀ m hm]

/-- The `Int`-valued (`ValExpr`) specialization: under coherence the scalar `computeValue` equals
    the value of any full parse. -/
theorem computeValue_coherent (g : Grammar) (ve : ValExpr) (s : String)
    (hcoh : ValueCoherent g (fun env => ve.eval env) s) {m : CaptureMap}
    (hm : m ∈ fullParses g s) :
    computeValue g ve s = some (ve.eval m.toEnv) := by
  have := computeValueF_coherent g (fun env => ve.eval env) s hcoh hm
  simpa [computeValue, computeValueF] using this

/-- Corollary specialized to the decidable check: at a string with a unique full parse, the
    computed value is `valFn` of that parse — the common case for the shipped (unambiguous)
    grammars, dischargeable by `decide` on `DecodeUnique` at any concrete accepted string. -/
theorem computeValueF_of_unique {α : Type} (g : Grammar) (valFn : Env → α) (s : String)
    (h : DecodeUnique g s) {m : CaptureMap} (hm : m ∈ fullParses g s) :
    computeValueF g valFn s = some (valFn m.toEnv) :=
  computeValueF_coherent g valFn s
    (ValueCoherent.of_captureCoherent g valFn s (CaptureCoherent.of_unique g s h)) hm

end Triptych
