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

import Triptych.Architecture.SearchPlan
import Triptych.Theorems.Scanner

/-!
# Ordered search-plan correctness

`SearchPlan` resolves production references and optionality at generation time while retaining
the complete scanner's ordered search. The structural certificate lets these theorems erase the
plan layer: executing a mirrored pattern, sequence, or alternative list is exactly the
corresponding scanner operation.
-/

namespace Triptych

namespace SearchPattern

mutual

/-- A certified resolved symbol has exactly the source scanner's continuation behavior. -/
theorem searchK_eq_scanSymK (grammar : Grammar) :
    ∀ {qual : String} {fuel : Nat} {symbol : Sym} {pattern : SearchPattern},
      MirrorsSymbol grammar qual fuel symbol pattern →
      ∀ {α : Type} (input : List Char) (k : CaptureMap → List Char → Option α),
        searchK pattern input k = scanSymK grammar qual fuel symbol input k
  | _, _, _, _, .literal, _, input, k => by
      simp [searchK, scanSymK]
  | _, _, _, _, .stringLiteral, _, input, k => by
      simp [searchK, scanSymK]
  | _, _, _, _, .tokenRun, _, input, k => by
      simp [searchK, scanSymK]
  | _, _, _, _, .capture hproduction hkeys body, _, input, k => by
      simp only [searchK, scanSymK, hproduction]
      rw [hkeys]
      rw [searchAlternativesK_eq_scanAlternatives grammar body]
      unfold expectedCaptureKeys
      split <;> simp [scanProdK]
  | _, _, _, _, .repetition hcount body, _, input, k => by
      simp only [searchK, scanSymK]
      rw [searchK_eq_scanSymK grammar body]
      apply congrArg (fun continuation =>
        scanSymK grammar _ _ _ input continuation)
      funext firstCaptures remaining
      rw [hcount]
      apply congrArg (fun scanItem =>
        scanStarK scanItem _ _ _ input.length remaining firstCaptures 1 _)
      funext itemInput itemK
      exact searchK_eq_scanSymK grammar body itemInput itemK

/-- A certified resolved sequence has exactly the source scanner's continuation behavior. -/
theorem searchSequenceK_eq_scanSeqK (grammar : Grammar) :
    ∀ {qual : String} {fuel : Nat} {sequence : Triptych.Seq}
      {patterns : List SearchPattern},
      MirrorsSequence grammar qual fuel sequence patterns →
      ∀ {α : Type} (input : List Char) (k : CaptureMap → List Char → Option α),
        searchSequenceK patterns input k = scanSeqK grammar qual fuel sequence input k
  | _, _, _, _, .empty, _, input, k => by
      simp [searchSequenceK, scanSeqK]
  | _, _, _, _, .required head tail, _, input, k => by
      simp only [searchSequenceK, scanSeqK, Bool.false_eq_true, ite_false]
      rw [searchK_eq_scanSymK grammar head]
      apply congrArg (fun continuation =>
        scanSymK grammar _ _ _ input continuation)
      funext firstCaptures remaining
      rw [searchSequenceK_eq_scanSeqK grammar tail]
  | _, _, _, _, .optional head tail, _, input, k => by
      simp only [searchSequenceK, searchK, scanSeqK, ite_true]
      rw [searchK_eq_scanSymK grammar head]
      simp only [searchSequenceK_eq_scanSeqK grammar tail, List.nil_append]

/-- A certified resolved alternative list performs the source scanner's ordered search. -/
theorem searchAlternativesK_eq_scanAlternatives (grammar : Grammar) :
    ∀ {qual : String} {fuel : Nat} {alternatives : List Triptych.Seq}
      {patterns : List (List SearchPattern)},
      MirrorsAlternatives grammar qual fuel alternatives patterns →
      ∀ {α : Type} (input : List Char) (k : CaptureMap → List Char → Option α),
        searchAlternativesK patterns input k =
          alternatives.findSome? fun alternative =>
            scanSeqK grammar qual fuel alternative input k
  | _, _, _, _, .empty, _, input, k => by
      simp [searchAlternativesK]
  | _, _, _, _, .cons head tail, _, input, k => by
      simp only [searchAlternativesK, List.findSome?_cons]
      rw [searchSequenceK_eq_scanSeqK grammar head]
      rw [searchAlternativesK_eq_scanAlternatives grammar tail]
      unfold scanOrElse
      cases hresult : scanSeqK grammar _ _ _ input k <;> rfl

end

end SearchPattern

namespace SearchPlan

/-- A certified ordered plan is exactly the complete continuation scanner. -/
theorem decode_eq_scanSearch {plan : SearchPlan} {grammar : Grammar}
    (hmirror : MirrorsGrammar plan grammar) (source : String) :
    plan.decode source = scanSearch grammar source := by
  cases hmirror with
  | intro hstart production hproduction body =>
      unfold decode scanSearch
      simp only [hproduction]
      rw [SearchPattern.searchAlternativesK_eq_scanAlternatives grammar body]
      simp [scanProdK]

/-- Every successfully compiled ordered plan agrees with the complete scanner. -/
theorem compileSearchPlan_decode_eq_scanSearch {grammar : Grammar} {plan : SearchPlan}
    (hcompile : compileSearchPlan grammar = .ok plan) (source : String) :
    plan.decode source = scanSearch grammar source :=
  decode_eq_scanSearch (compileSearchPlan_mirrorsGrammar hcompile) source

/-- Every successfully compiled ordered plan agrees with the archived parser semantics. -/
theorem compileSearchPlan_decode_eq_decode {grammar : Grammar} {plan : SearchPlan}
    (hcompile : compileSearchPlan grammar = .ok plan) (source : String) :
    plan.decode source = Triptych.decode grammar source := by
  rw [compileSearchPlan_decode_eq_scanSearch hcompile]
  exact scanSearch_eq_decode grammar source

end SearchPlan

end Triptych
