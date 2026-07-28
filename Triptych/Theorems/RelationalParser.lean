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
reader to the same map. These views coincide for a grammar with a `GrammarDecodeUnique`
certificate.

The map-valued theorems cover `value'`; the `F` variants cover readers through `Env`. Lifted
variants compose the user's lift with the relational value reader.
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
    (hunique : GrammarDecodeUnique g) (s : String) (v : α) :
    gatedParse (fun s => isWf g cs s ∧ satisfiesConstraints g cs s)
        (computeValueMap g valFn) s = some v ↔
      Denotes g (CaptureAccepts cs) valFn s v := by
  rw [gatedParseMap_eq_decodeGatedMap]
  exact decodeGatedMap_eq_some_iff_denotes g (CaptureAccepts cs) valFn s v
    (FormatCoherent.of_captureCoherent g (CaptureAccepts cs) valFn s
      (CaptureCoherent.of_unique g s (hunique s)))

/-- Environment-reader specialization of `gatedParseMap_eq_some_iff_denotes`. -/
theorem gatedParseF_eq_some_iff_denotes {α : Type}
    (g : Grammar) (cs : List ConstraintEntry) (valFn : Env → α)
    (hunique : GrammarDecodeUnique g) (s : String) (v : α) :
    gatedParse (fun s => isWf g cs s ∧ satisfiesConstraints g cs s)
        (computeValueF g valFn) s = some v ↔
      Denotes g (CaptureAccepts cs) (fun m => valFn m.toEnv) s v := by
  change
    gatedParse (fun s => isWf g cs s ∧ satisfiesConstraints g cs s)
        (computeValueMap g (fun m => valFn m.toEnv)) s = some v ↔
      Denotes g (CaptureAccepts cs) (fun m => valFn m.toEnv) s v
  exact gatedParseMap_eq_some_iff_denotes g cs (fun m => valFn m.toEnv) hunique s v

private theorem gatedParseLiftMap_eq_gatedParseComp {α δ : Type}
    (g : Grammar) (cs : List ConstraintEntry) (valFn : CaptureMap → α)
    (σ : α → δ) (s : String) :
    gatedParseLift (fun s => isWf g cs s ∧ satisfiesConstraints g cs s)
        (computeValueMap g valFn) σ s =
      gatedParse (fun s => isWf g cs s ∧ satisfiesConstraints g cs s)
        (computeValueMap g (σ ∘ valFn)) s := by
  unfold gatedParseLift gatedParse
  by_cases h : isWf g cs s ∧ satisfiesConstraints g cs s
  · simp [h, computeValueMap, Function.comp_def, Option.map_map]
  · simp [h]

/-- Lifted full-map parsers denote the lift composed with the underlying value reader. -/
theorem gatedParseLiftMap_eq_some_iff_denotes {α δ : Type}
    (g : Grammar) (cs : List ConstraintEntry) (valFn : CaptureMap → α) (σ : α → δ)
    (hunique : GrammarDecodeUnique g) (s : String) (d : δ) :
    gatedParseLift (fun s => isWf g cs s ∧ satisfiesConstraints g cs s)
        (computeValueMap g valFn) σ s = some d ↔
      Denotes g (CaptureAccepts cs) (σ ∘ valFn) s d := by
  rw [gatedParseLiftMap_eq_gatedParseComp]
  exact gatedParseMap_eq_some_iff_denotes g cs (σ ∘ valFn) hunique s d

/-- Lifted environment-reader specialization of
    `gatedParseLiftMap_eq_some_iff_denotes`. -/
theorem gatedParseLiftF_eq_some_iff_denotes {α δ : Type}
    (g : Grammar) (cs : List ConstraintEntry) (valFn : Env → α) (σ : α → δ)
    (hunique : GrammarDecodeUnique g) (s : String) (d : δ) :
    gatedParseLift (fun s => isWf g cs s ∧ satisfiesConstraints g cs s)
        (computeValueF g valFn) σ s = some d ↔
      Denotes g (CaptureAccepts cs) (σ ∘ fun m => valFn m.toEnv) s d := by
  change
    gatedParseLift (fun s => isWf g cs s ∧ satisfiesConstraints g cs s)
        (computeValueMap g (fun m => valFn m.toEnv)) σ s = some d ↔
      Denotes g (CaptureAccepts cs) (σ ∘ fun m => valFn m.toEnv) s d
  exact
    gatedParseLiftMap_eq_some_iff_denotes g cs (fun m => valFn m.toEnv) σ hunique s d

end Triptych
