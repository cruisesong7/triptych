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
* `CaptureCoherent` / `EnvCoherent` / `ValueCoherent` — successively weaker hypotheses that
  all full parses agree on the full capture map, its scalar environment view, or one computed
  value. `ValueCoherent` ranges over `CaptureMap → α`, so it covers both scalar readers and
  repeated-capture readers.
* `computeValueF_coherent` / `computeValueMap_coherent` — under the corresponding coherence
  hypothesis, the computed value equals that of **any** full parse. So the value is a property
  of the grammar + string, not of `decode`'s enumeration order.
* `DecodeUnique g s := (fullParses g s).length ≤ 1` — a **decidable** sufficient condition.
  `#eval decide` provides a concrete runtime check; a proof of `DecodeUnique` supplies the
  kernel-checked certificate consumed by the coherence theorems.
* `DecodesAs` — the relational view connecting a string to the value of a full parse; under
  coherence it is equivalent to the executable decoder returning that value.

Representative inputs from the shipped examples evaluate to a one-element `fullParses`; this
is evidence, not a grammar-wide proof. `GrammarCaptureFunctional` names the exact all-input
capture property; `GrammarDecodeUnique` is a stronger sufficient condition.
`Triptych.Theorems.Unambiguity` proves the latter from `Grammar.staticUnique`, currently
covering unary reference paths, required sequences with deterministic prefix matches, and
pairwise-distinct literal-leading alternatives, unary token/literal delimiter boundaries, and
a leading optional-literal reference separated by FIRST-character exclusion. Recursive FIRST
sets, shared-prefix alternatives, general nullable sequences, and repetitions remain future
work.
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

/-- The grammar decodes `s` **capture-coherently**: every full parse yields the same complete
    capture map, including repeated captures and their order. This is the strongest coherence
    notion and makes every `CaptureMap → α` reader independent of first-match selection. -/
def CaptureCoherent (g : Grammar) (s : String) : Prop :=
  ∀ m ∈ fullParses g s, ∀ m' ∈ fullParses g s, m = m'

/-- Every full parse has the same scalar environment view. Weaker than `CaptureCoherent`:
    repeated captures after the first may differ while `toEnv` remains equal. This suffices for
    `computeValueF` and the current constraint readers, but not for `computeValueMap`. -/
def EnvCoherent (g : Grammar) (s : String) : Prop :=
  ∀ m ∈ fullParses g s, ∀ m' ∈ fullParses g s, m.toEnv = m'.toEnv

/-- The grammar decodes `s` **value-coherently** under a full-map reader `valFn`: every full
    parse yields the same value. This is the weakest and exact hypothesis needed by
    `computeValueMap_coherent`; an environment reader is represented by `valFn ∘ toEnv`. -/
def ValueCoherent {α : Type} (g : Grammar) (valFn : CaptureMap → α) (s : String) : Prop :=
  ∀ m ∈ fullParses g s, ∀ m' ∈ fullParses g s, valFn m = valFn m'

/-- Every full parse agrees on whether a per-capture acceptance predicate holds. Value
    coherence alone does not imply this: two parses may compute the same value while exposing
    different captures to a constraint. -/
def PredicateCoherent (g : Grammar) (accept : CaptureMap → Prop) (s : String) : Prop :=
  ∀ m ∈ fullParses g s, ∀ m' ∈ fullParses g s, accept m ↔ accept m'

/-- Both acceptance and value are independent of which full parse is selected. -/
def FormatCoherent {α : Type} (g : Grammar) (accept : CaptureMap → Prop)
    (valFn : CaptureMap → α) (s : String) : Prop :=
  PredicateCoherent g accept s ∧ ValueCoherent g valFn s

/-- Full capture coherence implies scalar-environment coherence. -/
theorem EnvCoherent.of_captureCoherent (g : Grammar) (s : String)
    (h : CaptureCoherent g s) : EnvCoherent g s := by
  intro m hm m' hm'
  rw [h m hm m' hm']

/-- Capture coherence implies value coherence for every full-map reader. -/
theorem ValueCoherent.of_captureCoherent {α : Type} (g : Grammar)
    (valFn : CaptureMap → α) (s : String) (h : CaptureCoherent g s) :
    ValueCoherent g valFn s := by
  intro m hm m' hm'
  rw [h m hm m' hm']

/-- Environment coherence implies value coherence for every reader that factors through
    `CaptureMap.toEnv`. -/
theorem ValueCoherent.of_envCoherent {α : Type} (g : Grammar) (valFn : Env → α) (s : String)
    (h : EnvCoherent g s) : ValueCoherent g (fun m => valFn m.toEnv) s := by
  intro m hm m' hm'
  change valFn m.toEnv = valFn m'.toEnv
  rw [h m hm m' hm']

/-- Capture coherence makes every per-capture acceptance predicate coherent. -/
theorem PredicateCoherent.of_captureCoherent (g : Grammar) (accept : CaptureMap → Prop)
    (s : String) (h : CaptureCoherent g s) : PredicateCoherent g accept s := by
  intro m hm m' hm'
  rw [h m hm m' hm']

/-- Capture coherence implies full format coherence for arbitrary acceptance and value
    functions over the capture map. -/
theorem FormatCoherent.of_captureCoherent {α : Type} (g : Grammar)
    (accept : CaptureMap → Prop) (valFn : CaptureMap → α) (s : String)
    (h : CaptureCoherent g s) : FormatCoherent g accept valFn s :=
  ⟨PredicateCoherent.of_captureCoherent g accept s h,
    ValueCoherent.of_captureCoherent g valFn s h⟩

/-- A **decidable** sufficient condition for coherence: at most one full parse. At a concrete
    grammar/string, `#eval decide` is an executable diagnostic. The theorems below consume a
    proof of this proposition; the current parser does not synthesize that proof statically. -/
def DecodeUnique (g : Grammar) (s : String) : Prop := (fullParses g s).length ≤ 1

instance (g : Grammar) (s : String) : Decidable (DecodeUnique g s) := by
  unfold DecodeUnique; infer_instance

/-- At most one full parse implies capture coherence: any two members of a list of length at
    most one are equal. -/
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
      exact hm.trans hm'.symm
  | _ :: _ :: _, h => simp at h

/-- At most one full parse implies value coherence for every full-map reader. -/
theorem ValueCoherent.of_unique {α : Type} (g : Grammar) (valFn : CaptureMap → α) (s : String)
    (h : DecodeUnique g s) : ValueCoherent g valFn s :=
  ValueCoherent.of_captureCoherent g valFn s (CaptureCoherent.of_unique g s h)

/-! ## Grammar-wide certificate surfaces

These are propositions over every string, not per-input decision procedures. The conservative
`Grammar.staticUnique` syntax check proves the stronger `GrammarDecodeUnique`; analyses that
permit duplicate derivations with identical captures can target `GrammarCaptureFunctional`
directly. -/

/-- Every input has at most one full parse. Rejected inputs satisfy this through zero parses. -/
def GrammarDecodeUnique (g : Grammar) : Prop := ∀ s, DecodeUnique g s

/-- The grammar's capture semantics is a partial function: all full parses of an input produce
    the same complete capture map. Unlike `GrammarDecodeUnique`, this permits duplicate or
    otherwise distinct derivations when their observable captures are identical. -/
def GrammarCaptureFunctional (g : Grammar) : Prop := ∀ s, CaptureCoherent g s

/-- Every input is value-coherent for `valFn`. -/
def GrammarValueCoherent {α : Type} (g : Grammar) (valFn : CaptureMap → α) : Prop :=
  ∀ s, ValueCoherent g valFn s

/-- Grammar-wide derivation uniqueness implies capture functionality. -/
theorem GrammarCaptureFunctional.of_unique (g : Grammar) (h : GrammarDecodeUnique g) :
    GrammarCaptureFunctional g := by
  intro s
  exact CaptureCoherent.of_unique g s (h s)

/-- Capture functionality implies grammar-wide coherence for every value reader. -/
theorem GrammarValueCoherent.of_captureFunctional {α : Type} (g : Grammar)
    (valFn : CaptureMap → α) (h : GrammarCaptureFunctional g) :
    GrammarValueCoherent g valFn := by
  intro s
  exact ValueCoherent.of_captureCoherent g valFn s (h s)

/-- A grammar-wide uniqueness certificate implies grammar-wide value coherence. -/
theorem GrammarValueCoherent.of_unique {α : Type} (g : Grammar) (valFn : CaptureMap → α)
    (h : GrammarDecodeUnique g) : GrammarValueCoherent g valFn :=
  GrammarValueCoherent.of_captureFunctional g valFn
    (GrammarCaptureFunctional.of_unique g h)

/-! A grammar may have duplicate derivations while still defining one capture map. This
regression example separates the public functionality contract from the stronger uniqueness
certificate used by the first static checker. -/

private def duplicateEmptyGrammar : Grammar where
  start := "S"
  prods := [{ name := "S", alts := [[], []] }]

private theorem duplicateEmptyGrammar_functional :
    GrammarCaptureFunctional duplicateEmptyGrammar := by
  intro s m hm m' hm'
  simp [fullParses, duplicateEmptyGrammar, Grammar.startProd?, Grammar.prod?, matchProd,
    matchSeq] at hm hm'
  exact hm.1.trans hm'.1.symm

private theorem duplicateEmptyGrammar_not_unique :
    ¬ GrammarDecodeUnique duplicateEmptyGrammar := by
  intro h
  have := h ""
  simp [DecodeUnique, fullParses, duplicateEmptyGrammar, Grammar.startProd?, Grammar.prod?,
    matchProd, matchSeq] at this

/-! ## The payoff -/

/-- **Full-map value coherence.** If every full parse agrees under `valFn`, then
    `computeValueMap` equals `valFn` of **any** full parse. This covers repeated-capture readers
    such as IPv6's `[H16]`, which inspect the complete `CaptureMap`. -/
theorem computeValueMap_coherent {α : Type} (g : Grammar) (valFn : CaptureMap → α) (s : String)
    (hcoh : ValueCoherent g valFn s) {m : CaptureMap} (hm : m ∈ fullParses g s) :
    computeValueMap g valFn s = some (valFn m) := by
  have hne : fullParses g s ≠ [] := List.ne_nil_of_mem hm
  have hsome : (decode g s).isSome = true := (decode_isSome_iff g s).mpr hne
  obtain ⟨m₀, hm₀⟩ := Option.isSome_iff_exists.mp hsome
  have hmem₀ : m₀ ∈ fullParses g s := decode_mem_fullParses g s hm₀
  unfold computeValueMap
  rw [hm₀]
  simp only [Option.map_some]
  rw [hcoh m₀ hmem₀ m hm]

/-- **Environment value coherence.** The `computeValueF` specialization of
    `computeValueMap_coherent`: every full parse agrees after projecting to `Env`. -/
theorem computeValueF_coherent {α : Type} (g : Grammar) (valFn : Env → α) (s : String)
    (hcoh : ValueCoherent g (fun m => valFn m.toEnv) s)
    {m : CaptureMap} (hm : m ∈ fullParses g s) :
    computeValueF g valFn s = some (valFn m.toEnv) := by
  simpa [computeValueF, computeValueMap] using
    computeValueMap_coherent g (fun m => valFn m.toEnv) s hcoh hm

/-- The `Int`-valued (`ValExpr`) specialization: under coherence the scalar `computeValue` equals
    the value of any full parse. -/
theorem computeValue_coherent (g : Grammar) (ve : ValExpr) (s : String)
    (hcoh : ValueCoherent g (fun m => ve.eval m.toEnv) s) {m : CaptureMap}
    (hm : m ∈ fullParses g s) :
    computeValue g ve s = some (ve.eval m.toEnv) := by
  have := computeValueF_coherent g (fun env => ve.eval env) s hcoh hm
  simpa [computeValue, computeValueF] using this

/-- Corollary specialized to uniqueness: at a string with at most one full parse, the computed
    value is `valFn` of that parse. -/
theorem computeValueF_of_unique {α : Type} (g : Grammar) (valFn : Env → α) (s : String)
    (h : DecodeUnique g s) {m : CaptureMap} (hm : m ∈ fullParses g s) :
    computeValueF g valFn s = some (valFn m.toEnv) :=
  computeValueF_coherent g valFn s
    (ValueCoherent.of_unique g (fun m => valFn m.toEnv) s h) hm

/-- The full-map counterpart of `computeValueF_of_unique`, covering repeated captures. -/
theorem computeValueMap_of_unique {α : Type} (g : Grammar) (valFn : CaptureMap → α) (s : String)
    (h : DecodeUnique g s) {m : CaptureMap} (hm : m ∈ fullParses g s) :
    computeValueMap g valFn s = some (valFn m) :=
  computeValueMap_coherent g valFn s (ValueCoherent.of_unique g valFn s h) hm

/-! ## Relational value semantics -/

/-- The grammar and string can be decoded as `v`: some full parse computes `v`. Unlike
    `computeValueMap`, this relation does not select the first parse. Format constraints can be
    conjoined with this relation by the generated `IsValid` predicate. -/
def DecodesAs {α : Type} (g : Grammar) (valFn : CaptureMap → α) (s : String) (v : α) : Prop :=
  ∃ m, m ∈ fullParses g s ∧ valFn m = v

/-- Under value coherence, executable full-map decoding is exactly the relational semantics. -/
theorem computeValueMap_eq_some_iff_decodesAs {α : Type} (g : Grammar)
    (valFn : CaptureMap → α) (s : String) (v : α) (hcoh : ValueCoherent g valFn s) :
    computeValueMap g valFn s = some v ↔ DecodesAs g valFn s v := by
  constructor
  · intro h
    unfold computeValueMap at h
    cases hd : decode g s with
    | none => simp [hd] at h
    | some m =>
      simp only [hd, Option.map_some, Option.some.injEq] at h
      exact ⟨m, decode_mem_fullParses g s hd, h⟩
  · rintro ⟨m, hm, hval⟩
    rw [computeValueMap_coherent g valFn s hcoh hm, hval]

/-- The environment-reader specialization of `DecodesAs`. -/
theorem computeValueF_eq_some_iff_decodesAs {α : Type} (g : Grammar)
    (valFn : Env → α) (s : String) (v : α)
    (hcoh : ValueCoherent g (fun m => valFn m.toEnv) s) :
    computeValueF g valFn s = some v ↔
      DecodesAs g (fun m => valFn m.toEnv) s v := by
  simpa [computeValueF, computeValueMap] using
    computeValueMap_eq_some_iff_decodesAs g (fun m => valFn m.toEnv) s v hcoh

/-! ## Relational format semantics

`DecodesAs` relates grammar recognition to a value. `Denotes` additionally applies an
acceptance predicate to each candidate capture map, so capture-derived constraints are part of
the relation rather than being evaluated only after `decode` has selected its first parse. -/

/-- A valid full parse of `s` denotes `v`. Both `accept` and `valFn` inspect that same parse. -/
def Denotes {α : Type} (g : Grammar) (accept : CaptureMap → Prop)
    (valFn : CaptureMap → α) (s : String) (v : α) : Prop :=
  ∃ m, m ∈ fullParses g s ∧ accept m ∧ valFn m = v

/-- The executable first-match counterpart of `Denotes`. This is deliberately generic over
    the capture-level predicate; generated format constraints can instantiate `accept`. -/
def decodeGatedMap {α : Type} (g : Grammar) (accept : CaptureMap → Prop)
    [DecidablePred accept] (valFn : CaptureMap → α) (s : String) : Option α :=
  match decode g s with
  | none   => none
  | some m => if accept m then some (valFn m) else none

/-- Under full format coherence, the executable first-match decoder and relational `Denotes`
    agree. This is the order-independence theorem for both acceptance and value. -/
theorem decodeGatedMap_eq_some_iff_denotes {α : Type} (g : Grammar)
    (accept : CaptureMap → Prop) [DecidablePred accept] (valFn : CaptureMap → α)
    (s : String) (v : α) (hcoh : FormatCoherent g accept valFn s) :
    decodeGatedMap g accept valFn s = some v ↔ Denotes g accept valFn s v := by
  constructor
  · intro h
    unfold decodeGatedMap at h
    cases hd : decode g s with
    | none => simp [hd] at h
    | some m =>
      simp only [hd] at h
      by_cases ha : accept m
      · rw [if_pos ha] at h
        exact ⟨m, decode_mem_fullParses g s hd, ha, Option.some.inj h⟩
      · rw [if_neg ha] at h
        simp at h
  · rintro ⟨m, hm, ha, hval⟩
    have hne : fullParses g s ≠ [] := List.ne_nil_of_mem hm
    have hsome : (decode g s).isSome = true := (decode_isSome_iff g s).mpr hne
    obtain ⟨m₀, hm₀⟩ := Option.isSome_iff_exists.mp hsome
    have hmem₀ : m₀ ∈ fullParses g s := decode_mem_fullParses g s hm₀
    have ha₀ : accept m₀ := (hcoh.1 m₀ hmem₀ m hm).mpr ha
    have hval₀ : valFn m₀ = valFn m := hcoh.2 m₀ hmem₀ m hm
    unfold decodeGatedMap
    simp only [hm₀, ha₀, ↓reduceIte]
    rw [hval₀, hval]

end Triptych
