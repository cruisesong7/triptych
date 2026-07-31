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

import Triptych.Architecture.Assemble
import Triptych.Theorems.Coherence

/-!
# Relational contracts for generated parsers

The generated parser checks the format constraints against `decode`'s selected capture map.
`Denotes`, by contrast, quantifies over full parses and applies both the constraints and value
reader to the same map. These views coincide when the grammar's capture semantics is
functional: every full parse produces the same complete capture map.

The map-valued theorems cover `value'`; the `F` variants cover readers through `Env`.
Domain-valued variants compose `ofSpec` with the relational value reader.
-/

namespace Triptych

/-- Every format constraint accepts one capture map. Each entry contributes in exactly one
    phase; its contribution in the other phase is `True`. -/
def CaptureAccepts (cs : List ConstraintEntry) (m : CaptureMap) : Prop :=
  ∀ c ∈ cs, c.wfPart m.toEnv ∧ c.valPart m.toEnv

instance (cs : List ConstraintEntry) : DecidablePred (CaptureAccepts cs) := by
  intro m
  unfold CaptureAccepts
  infer_instance

private theorem gatedParseMap_eq_decodeGatedMap {α : Type}
    (g : Grammar) (cs : List ConstraintEntry) (valFn : CaptureMap → α) (s : String) :
    gatedParse (fun s => isWf g cs s ∧ satisfiesConstraints g cs s)
        (computeValueMap g valFn) s =
      decodeGatedMap g (CaptureAccepts cs) valFn s := by
  unfold gatedParse isWf satisfiesConstraints envOf computeValueMap decodeGatedMap
    CaptureAccepts
  cases hd : decode g s with
  | none => simp [hd]
  | some m => simp [hd, forall_and]

/-- For a grammar-wide unique format, the generated full-map parser succeeds exactly when a
    constraint-accepted full parse denotes the returned value. -/
theorem gatedParseMap_eq_some_iff_denotes {α : Type}
    (g : Grammar) (cs : List ConstraintEntry) (valFn : CaptureMap → α)
    (hfunctional : GrammarCaptureFunctional g) (s : String) (v : α) :
    gatedParse (fun s => isWf g cs s ∧ satisfiesConstraints g cs s)
        (computeValueMap g valFn) s = some v ↔
      Denotes g (CaptureAccepts cs) valFn s v := by
  rw [gatedParseMap_eq_decodeGatedMap]
  exact decodeGatedMap_eq_some_iff_denotes g (CaptureAccepts cs) valFn s v
    (FormatCoherent.of_captureCoherent g (CaptureAccepts cs) valFn s (hfunctional s))

/-- Environment-reader specialization of `gatedParseMap_eq_some_iff_denotes`. -/
theorem gatedParseF_eq_some_iff_denotes {α : Type}
    (g : Grammar) (cs : List ConstraintEntry) (valFn : Env → α)
    (hfunctional : GrammarCaptureFunctional g) (s : String) (v : α) :
    gatedParse (fun s => isWf g cs s ∧ satisfiesConstraints g cs s)
        (computeValueF g valFn) s = some v ↔
      Denotes g (CaptureAccepts cs) (fun m => valFn m.toEnv) s v := by
  change
    gatedParse (fun s => isWf g cs s ∧ satisfiesConstraints g cs s)
        (computeValueMap g (fun m => valFn m.toEnv)) s = some v ↔
      Denotes g (CaptureAccepts cs) (fun m => valFn m.toEnv) s v
  exact gatedParseMap_eq_some_iff_denotes g cs (fun m => valFn m.toEnv) hfunctional s v

private theorem gatedParseOfSpecMap_eq_gatedParseComp {α δ : Type}
    (g : Grammar) (cs : List ConstraintEntry) (valFn : CaptureMap → α)
    (ofSpec : α → δ) (s : String) :
    gatedParseOfSpec (fun s => isWf g cs s ∧ satisfiesConstraints g cs s)
        (computeValueMap g valFn) ofSpec s =
      gatedParse (fun s => isWf g cs s ∧ satisfiesConstraints g cs s)
        (computeValueMap g (ofSpec ∘ valFn)) s := by
  unfold gatedParseOfSpec gatedParse
  by_cases h : isWf g cs s ∧ satisfiesConstraints g cs s
  · simp [h, computeValueMap, Function.comp_def, Option.map_map]
  · simp [h]

/-- Domain-valued full-map parsers denote `ofSpec` composed with the value reader. -/
theorem gatedParseOfSpecMap_eq_some_iff_denotes {α δ : Type}
    (g : Grammar) (cs : List ConstraintEntry) (valFn : CaptureMap → α)
    (ofSpec : α → δ)
    (hfunctional : GrammarCaptureFunctional g) (s : String) (d : δ) :
    gatedParseOfSpec (fun s => isWf g cs s ∧ satisfiesConstraints g cs s)
        (computeValueMap g valFn) ofSpec s = some d ↔
      Denotes g (CaptureAccepts cs) (ofSpec ∘ valFn) s d := by
  rw [gatedParseOfSpecMap_eq_gatedParseComp]
  exact gatedParseMap_eq_some_iff_denotes g cs (ofSpec ∘ valFn) hfunctional s d

/-- Domain-valued environment-reader specialization of
    `gatedParseOfSpecMap_eq_some_iff_denotes`. -/
theorem gatedParseOfSpecF_eq_some_iff_denotes {α δ : Type}
    (g : Grammar) (cs : List ConstraintEntry) (valFn : Env → α)
    (ofSpec : α → δ)
    (hfunctional : GrammarCaptureFunctional g) (s : String) (d : δ) :
    gatedParseOfSpec (fun s => isWf g cs s ∧ satisfiesConstraints g cs s)
        (computeValueF g valFn) ofSpec s = some d ↔
      Denotes g (CaptureAccepts cs) (ofSpec ∘ fun m => valFn m.toEnv) s d := by
  change
    gatedParseOfSpec (fun s => isWf g cs s ∧ satisfiesConstraints g cs s)
        (computeValueMap g (fun m => valFn m.toEnv)) ofSpec s = some d ↔
      Denotes g (CaptureAccepts cs) (ofSpec ∘ fun m => valFn m.toEnv) s d
  exact
    gatedParseOfSpecMap_eq_some_iff_denotes
      g cs (fun m => valFn m.toEnv) ofSpec hfunctional s d

end Triptych
