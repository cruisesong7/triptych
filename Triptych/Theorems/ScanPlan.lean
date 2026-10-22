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

import Triptych.Architecture.CursorProgram
import Triptych.Reference.DecodeLemmas
import Triptych.Theorems.Scanner
import Triptych.Theorems.Unambiguity

/-!
# Scan-plan correctness

The architecture layer proves that structured scan patterns flatten to cursor programs without
changing execution. This module connects the structured pattern back to the reference
grammar semantics. Every successful direct match is a reference match, and every reference match
induces the same boundary-certified direct consumer path. Together these directions yield direct
soundness, completeness, and exact rejection for every successfully compiled plan.
-/

namespace Triptych

namespace ScanPattern

/-- Proof-facing deterministic matcher for a structured scan pattern. -/
def matchCaptures : ScanPattern → List Char → Option (CaptureMap × List Char)
  | .empty, input => some ([], input)
  | .literal _ _, [] => none
  | .literal character rest, actual :: input =>
      if actual = character then rest.matchCaptures input else none
  | .optionalLiteral _ rest, [] => rest.matchCaptures []
  | .optionalLiteral character rest, input@(actual :: tail) =>
      if actual = character then rest.matchCaptures tail else rest.matchCaptures input
  | .tokenRun token length rest, input =>
      let width := ScanPlan.tokenWidth token length input
      if termPrefixOk token length input width then
        rest.matchCaptures (input.drop width)
      else
        none
  | .capture _ keys body rest, input => do
      let bodyResult ← body.matchCaptures input
      let consumed := String.ofList (input.take (input.length - bodyResult.2.length))
      let tailResult ← rest.matchCaptures bodyResult.2
      let ownCaptures := keys.map fun key => (key, consumed)
      some (ownCaptures ++ bodyResult.1 ++ tailResult.1, tailResult.2)

/-- Successful structured execution is reflected by the proof-facing matcher. The theorem is
    generalized over an existing cursor state so the capture case can apply it recursively. -/
theorem executePattern_sound {input : List Char} {pattern : ScanPattern}
    {state finalState : ScanPlan.ExecutionState}
    (hexecute : ScanPlan.executePattern input pattern state = some finalState) :
    ∃ captures,
      pattern.matchCaptures (input.drop state.position) =
        some (captures, input.drop finalState.position) ∧
      finalState.starts = state.starts ∧
      finalState.captureMap = state.captureMap ++ captures := by
  induction pattern generalizing state finalState with
  | empty =>
      simp only [ScanPlan.executePattern] at hexecute
      injection hexecute with hstate
      subst finalState
      exact ⟨[], rfl, rfl, by simp⟩
  | literal character rest ih =>
      simp only [ScanPlan.executePattern] at hexecute
      obtain ⟨next, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hexecute
      unfold ScanPlan.executeOperation at hstep
      cases hsuffix : input.drop state.position with
      | nil => simp [hsuffix] at hstep
      | cons actual tail =>
          by_cases heq : actual = character
          · simp [hsuffix, heq] at hstep
            subst next
            obtain ⟨captures, hmatch, hstarts, hcaptures⟩ := ih hrest
            refine ⟨captures, ?_, hstarts, hcaptures⟩
            have hdrop : input.drop (state.position + 1) = tail := by
              have := congrArg (List.drop 1) hsuffix
              simpa [List.drop_drop] using this
            simp [matchCaptures, heq, hdrop] at hmatch ⊢
            exact hmatch
          · simp [hsuffix, heq] at hstep
  | optionalLiteral character rest ih =>
      cases hsuffix : input.drop state.position with
      | nil =>
          have hrest : ScanPlan.executePattern input rest state = some finalState := by
            simpa [ScanPlan.executePattern, ScanPlan.executeOperation, hsuffix] using hexecute
          obtain ⟨captures, hmatch, hstarts, hcaptures⟩ := ih hrest
          exact ⟨captures, by simpa [matchCaptures, hsuffix] using hmatch,
            hstarts, hcaptures⟩
      | cons actual tail =>
          by_cases heq : actual = character
          · let next : ScanPlan.ExecutionState :=
              { state with position := state.position + 1 }
            have hrest : ScanPlan.executePattern input rest next = some finalState := by
              simpa [ScanPlan.executePattern, ScanPlan.executeOperation, hsuffix, heq, next]
                using hexecute
            obtain ⟨captures, hmatch, hstarts, hcaptures⟩ := ih hrest
            refine ⟨captures, ?_, hstarts, hcaptures⟩
            have hdrop : input.drop (state.position + 1) = tail := by
              have := congrArg (List.drop 1) hsuffix
              simpa [List.drop_drop] using this
            simpa [matchCaptures, hsuffix, heq, hdrop, next] using hmatch
          · have hrest : ScanPlan.executePattern input rest state = some finalState := by
              simpa [ScanPlan.executePattern, ScanPlan.executeOperation, hsuffix, heq]
                using hexecute
            obtain ⟨captures, hmatch, hstarts, hcaptures⟩ := ih hrest
            exact ⟨captures, by simpa [matchCaptures, hsuffix, heq] using hmatch,
              hstarts, hcaptures⟩
  | tokenRun token length rest ih =>
      simp only [ScanPlan.executePattern] at hexecute
      obtain ⟨next, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hexecute
      let width := ScanPlan.tokenWidth token length (input.drop state.position)
      by_cases hprefix :
          termPrefixOk token length (input.drop state.position) width = true
      · simp [ScanPlan.executeOperation, width, hprefix] at hstep
        subst next
        obtain ⟨captures, hmatch, hstarts, hcaptures⟩ := ih hrest
        refine ⟨captures, ?_, hstarts, hcaptures⟩
        simpa [matchCaptures, width, hprefix, List.drop_drop] using hmatch
      · simp [ScanPlan.executeOperation, width, hprefix] at hstep
  | capture name keys body rest bodyIH restIH =>
      let frame : ScanPlan.OpenCapture :=
        { name := name
          keys := keys
          start := state.position
          captureMark := state.captureMap.length }
      let opened : ScanPlan.ExecutionState :=
        { state with starts := frame :: state.starts }
      have hwhole :
          (do
            let afterBody ← ScanPlan.executePattern input body opened
            let closed ← ScanPlan.executeOperation input (.endCapture name) afterBody
            ScanPlan.executePattern input rest closed) = some finalState := by
        simpa [ScanPlan.executePattern, ScanPlan.executeOperation, opened, frame] using hexecute
      obtain ⟨afterBody, hbody, hafterBody⟩ := Option.bind_eq_some_iff.mp hwhole
      obtain ⟨closed, hclose, hrest⟩ := Option.bind_eq_some_iff.mp hafterBody
      obtain ⟨bodyCaptures, hbodyMatch, hbodyStarts, hbodyCaptures⟩ := bodyIH hbody
      have hbodyStarts' : afterBody.starts = frame :: state.starts := by
        simpa [opened] using hbodyStarts
      have hbodyCaptures' :
          afterBody.captureMap = state.captureMap ++ bodyCaptures := by
        simpa [opened] using hbodyCaptures
      simp [ScanPlan.executeOperation, hbodyStarts', ScanPlan.takeStart?, frame,
        hbodyCaptures', List.take_append, List.drop_append] at hclose
      subst closed
      obtain ⟨tailCaptures, htailMatch, htailStarts, htailCaptures⟩ := restIH hrest
      let ownCaptures :=
        keys.map fun key =>
          (key, ScanPlan.capturedText input state.position afterBody.position)
      refine ⟨ownCaptures ++ bodyCaptures ++ tailCaptures, ?_, ?_, ?_⟩
      · have hbodyMatch' :
            body.matchCaptures (input.drop state.position) =
              some (bodyCaptures, input.drop afterBody.position) := by
          simpa [opened] using hbodyMatch
        simp [matchCaptures, hbodyMatch', htailMatch, ownCaptures,
          ScanPlan.capturedText, List.append_assoc]
      · exact htailStarts
      · simpa [ownCaptures, List.append_assoc] using htailCaptures

/-- A successful complete structured run produces exactly the matcher captures and consumes the
    entire source. -/
theorem runPattern_matchCaptures {plan : ScanPlan} {source : String} {result : ScanResult}
    (hrun : plan.runPattern source = some result) :
    plan.pattern.matchCaptures source.toList = some (result.captureMap, []) := by
  unfold ScanPlan.runPattern at hrun
  obtain ⟨state, hexecute, hresult⟩ := Option.bind_eq_some_iff.mp hrun
  by_cases hcomplete :
      (state.position == source.toList.length && state.starts.isEmpty) = true
  · rw [ite_eq_left hcomplete] at hresult
    injection hresult with hresult
    subst result
    obtain ⟨captures, hmatch, _, hcaptures⟩ := executePattern_sound hexecute
    have hposition : state.position = source.toList.length := by
      simpa using (Bool.and_eq_true_iff.mp hcomplete).1
    simp at hcaptures
    subst captures
    simpa [hposition] using hmatch
  · rw [ite_eq_right hcomplete] at hresult
    contradiction

/-- Successful structured decoding is exactly a complete proof-facing pattern match. -/
theorem decodePattern_matchCaptures {plan : ScanPlan} {source : String}
    {captures : CaptureMap}
    (hdecode : plan.decodePattern source = some captures) :
    plan.pattern.matchCaptures source.toList = some (captures, []) := by
  unfold ScanPlan.decodePattern ScanPlan.toCaptureMap at hdecode
  rw [Option.map_eq_some_iff] at hdecode
  obtain ⟨result, hrun, hcaptures⟩ := hdecode
  rw [← hcaptures]
  exact runPattern_matchCaptures hrun

/-- Every successful structured-pattern match is admitted by the reference grammar semantics. -/
theorem matchCaptures_mem_matchSeq {grammar : Grammar} {qual : String} {fuel : Nat}
    {sequence : Triptych.Seq} {pattern : ScanPattern} {input remaining : List Char}
    {captures : CaptureMap}
    (hmirror : MirrorsSequence grammar qual fuel sequence pattern)
    (hmatch : pattern.matchCaptures input = some (captures, remaining)) :
    (captures, remaining) ∈ matchSeq grammar qual fuel sequence input := by
  induction hmirror generalizing input captures remaining with
  | empty =>
      rename_i matchedQual matchedFuel
      simp only [matchCaptures, Option.some.injEq, Prod.mk.injEq] at hmatch
      rcases hmatch with ⟨rfl, rfl⟩
      exact
        (mem_matchSeq_nil_iff grammar matchedQual matchedFuel input input []).mpr
          ⟨rfl, rfl⟩
  | optionalLiteral htext tail tailIH =>
      rename_i character matchedQual matchedFuel rest tailPattern text
      rw [mem_matchSeq_cons_mk_optional_iff]
      cases input with
      | nil =>
          exact Or.inr (tailIH hmatch)
      | cons actual input =>
          by_cases heq : actual = character
          · simp only [matchCaptures, heq, ite_true] at hmatch
            refine Or.inl ⟨[], input, captures, ?_, tailIH hmatch, by simp⟩
            simp [matchSym, htext, heq]
          · simp only [matchCaptures, heq, ite_false] at hmatch
            exact Or.inr (tailIH hmatch)
  | literal htext tail tailIH =>
      rename_i character matchedQual matchedFuel rest tailPattern text
      rw [mem_matchSeq_cons_mk_required_iff]
      cases input with
      | nil => simp [matchCaptures] at hmatch
      | cons actual input =>
          by_cases heq : actual = character
          · simp only [matchCaptures, heq, ite_true] at hmatch
            refine ⟨[], input, captures, ?_, tailIH hmatch, by simp⟩
            simp [matchSym, htext, heq]
          · simp [matchCaptures, heq] at hmatch
  | tokenRun htoken hlength tail tailIH =>
      rename_i token foundToken length foundLength matchedQual matchedFuel rest tailPattern
      subst foundToken
      subst foundLength
      rw [mem_matchSeq_cons_mk_required_iff]
      by_cases hprefix :
          termPrefixOk token length input (ScanPlan.tokenWidth token length input) = true
      · simp [matchCaptures, hprefix] at hmatch
        let width := ScanPlan.tokenWidth token length input
        refine ⟨[], input.drop width, captures, ?_, tailIH hmatch, by simp⟩
        rw [mem_matchSym_term_iff]
        refine ⟨rfl, input.take width, List.take_append_drop width input |>.symm, ?_⟩
        unfold termPrefixOk at hprefix
        rw [Bool.and_eq_true] at hprefix
        exact of_decide_eq_true hprefix.2
      · simp [matchCaptures, hprefix] at hmatch
  | capture hname hkeys hproduction halternative body tail bodyIH tailIH =>
      rename_i name foundName keys matchedQual production alternative matchedFuel
        bodyPattern rest tailPattern
      subst foundName
      subst keys
      rw [mem_matchSeq_cons_mk_required_iff]
      unfold matchCaptures at hmatch
      obtain ⟨bodyResult, hbodyMatch, hmatch⟩ :=
        Option.bind_eq_some_iff.mp hmatch
      obtain ⟨bodyCaptures, middle⟩ := bodyResult
      obtain ⟨tailResult, htailMatch, hmatch⟩ :=
        Option.bind_eq_some_iff.mp hmatch
      obtain ⟨tailCaptures, suffix⟩ := tailResult
      simp only [Option.some.injEq, Prod.mk.injEq] at hmatch
      rcases hmatch with ⟨hcaptures, hremaining⟩
      subst captures
      subst remaining
      let consumed :=
        String.ofList (input.take (input.length - middle.length))
      let ownCaptures :=
        (expectedCaptureKeys matchedQual name).map fun key => (key, consumed)
      refine
        ⟨ownCaptures ++ bodyCaptures, middle, tailCaptures, ?_, ?_, ?_⟩
      · rw [mem_matchSym_ref_iff grammar matchedQual matchedFuel name production
          hproduction]
        refine ⟨bodyCaptures, ?_, ?_⟩
        · unfold matchProd
          simp [halternative, bodyIH hbodyMatch]
        · by_cases hempty : matchedQual = ""
          · simp [ownCaptures, consumed, expectedCaptureKeys, hempty]
          · simp [ownCaptures, consumed, expectedCaptureKeys, hempty]
      · exact tailIH (by simpa using htailMatch)
      · rfl

end ScanPattern

/-- Capture-erased evidence that a straight-line operation sequence consumes one prefix and
    leaves a specified suffix. This relation records the grammar's chosen token spans without
    committing to the cursor implementation's greedy width calculation. -/
inductive ConsumingMatch : List ScanOp → List Char → List Char → Prop where
  | empty (input : List Char) : ConsumingMatch [] input input
  | literal {character input remaining rest}
      (tail : ConsumingMatch rest input remaining) :
      ConsumingMatch (.literal character :: rest) (character :: input) remaining
  | optionalPresent {character input remaining rest}
      (tail : ConsumingMatch rest input remaining) :
      ConsumingMatch (.optionalLiteral character :: rest) (character :: input) remaining
  | optionalAbsent {character input remaining rest}
      (tail : ConsumingMatch rest input remaining) :
      ConsumingMatch (.optionalLiteral character :: rest) input remaining
  | tokenRun {token lengthSpec pre input remaining rest}
      (valid : matchesTerm token lengthSpec (String.ofList pre))
      (tail : ConsumingMatch rest input remaining) :
      ConsumingMatch (.tokenRun token lengthSpec :: rest) (pre ++ input) remaining

namespace ConsumingMatch

/-- Sequential capture-erased matches compose. -/
theorem append {first second : List ScanOp} {input middle remaining : List Char}
    (head : ConsumingMatch first input middle)
    (tail : ConsumingMatch second middle remaining) :
    ConsumingMatch (first ++ second) input remaining := by
  induction head with
  | empty => exact tail
  | literal next ih => exact .literal (ih tail)
  | optionalPresent next ih => exact .optionalPresent (ih tail)
  | optionalAbsent next ih => exact .optionalAbsent (ih tail)
  | tokenRun valid next ih => exact .tokenRun valid (ih tail)

end ConsumingMatch

@[simp] theorem consumingOps_append (first second : List ScanOp) :
    consumingOps (first ++ second) = consumingOps first ++ consumingOps second := by
  induction first with
  | nil => rfl
  | cons operation rest ih =>
      cases operation <;> simp [consumingOps, ih]

/-- Execute only source-consuming operations, ignoring balanced capture markers. This
    proof-facing machine isolates the deterministic cursor choices from capture bookkeeping. -/
def executeConsumers : List ScanOp → List Char → Option (List Char)
  | [], input => some input
  | .literal character :: rest, input =>
      match input with
      | actual :: tail =>
          if actual = character then executeConsumers rest tail else none
      | [] => none
  | .optionalLiteral character :: rest, input =>
      match input with
      | actual :: tail =>
          if actual = character then executeConsumers rest tail
          else executeConsumers rest input
      | [] => executeConsumers rest []
  | .tokenRun token lengthSpec :: rest, input =>
      let width := ScanPlan.tokenWidth token lengthSpec input
      if termPrefixOk token lengthSpec input width then
        executeConsumers rest (input.drop width)
      else
        none
  | .beginCapture _ _ :: rest, input
  | .endCapture _ :: rest, input =>
      executeConsumers rest input

/-- A valid token prefix has the width chosen by the greedy cursor whenever the next
    operation supplies a certified boundary. -/
theorem tokenWidth_eq_of_append_boundary
    {token : TokClass} {lengthSpec : LenSpec} {pre suffix : List Char}
    (hmatches : matchesTerm token lengthSpec (String.ofList pre))
    (hboundary :
      match lengthSpec with
      | .exactly _ => True
      | _ =>
          suffix = [] ∨
            ∃ character rest, suffix = character :: rest ∧ ¬token.mem character) :
    ScanPlan.tokenWidth token lengthSpec (pre ++ suffix) = pre.length := by
  cases lengthSpec with
  | «exactly» width =>
      simpa [ScanPlan.tokenWidth] using hmatches.2.symm
  | «between» lower upper =>
      unfold ScanPlan.tokenWidth
      rw [List.takeWhile_append_of_pos]
      · rcases hboundary with rfl | ⟨character, rest, rfl, hcharacter⟩
        · simp
        · simp [hcharacter]
      · intro character hmem
        exact decide_eq_true (hmatches.1 character (by simpa using hmem))
  | «atLeastOne» =>
      unfold ScanPlan.tokenWidth
      rw [List.takeWhile_append_of_pos]
      · rcases hboundary with rfl | ⟨character, rest, rfl, hcharacter⟩
        · simp
        · simp [hcharacter]
      · intro character hmem
        exact decide_eq_true (hmatches.1 character (by simpa using hmem))

/-- A grammar-selected token prefix passes the cursor's executable token check. -/
theorem termPrefixOk_append_length {token : TokClass} {lengthSpec : LenSpec}
    {pre suffix : List Char}
    (hmatches : matchesTerm token lengthSpec (String.ofList pre)) :
    termPrefixOk token lengthSpec (pre ++ suffix) pre.length = true := by
  unfold termPrefixOk
  rw [Bool.and_eq_true]
  constructor
  · simp
  · simpa using decide_eq_true hmatches

namespace ConsumingMatch

/-- A variable-width token followed by a certified consumer path ends at a non-token
    character or at the end of the complete input. -/
theorem tokenBoundary {token : TokClass} {lengthSpec : LenSpec}
    {rest : List ScanOp} {input : List Char}
    (hmatch : ConsumingMatch rest input [])
    (hsafe : greedyBoundarySafe token lengthSpec rest = true) :
    match lengthSpec with
    | .exactly _ => True
    | _ => input = [] ∨
        ∃ character tail, input = character :: tail ∧ ¬token.mem character := by
  cases lengthSpec with
  | «exactly» => trivial
  | «between» lower upper =>
      cases rest with
      | nil =>
          cases hmatch
          exact Or.inl rfl
      | cons operation rest =>
          cases operation with
          | beginCapture =>
              cases hmatch
          | endCapture =>
              cases hmatch
          | literal character =>
              cases hmatch with
              | literal tail =>
                  refine Or.inr ⟨character, _, rfl, ?_⟩
                  intro hmem
                  simp [greedyBoundarySafe, consumingOps, tokenAccepts, hmem] at hsafe
          | optionalLiteral =>
              simp [greedyBoundarySafe, consumingOps] at hsafe
          | tokenRun =>
              simp [greedyBoundarySafe, consumingOps] at hsafe
  | «atLeastOne» =>
      cases rest with
      | nil =>
          cases hmatch
          exact Or.inl rfl
      | cons operation rest =>
          cases operation with
          | beginCapture =>
              cases hmatch
          | endCapture =>
              cases hmatch
          | literal character =>
              cases hmatch with
              | literal tail =>
                  refine Or.inr ⟨character, _, rfl, ?_⟩
                  intro hmem
                  simp [greedyBoundarySafe, consumingOps, tokenAccepts, hmem] at hsafe
          | optionalLiteral =>
              simp [greedyBoundarySafe, consumingOps] at hsafe
          | tokenRun =>
              simp [greedyBoundarySafe, consumingOps] at hsafe

/-- If a grammar match omits an optional literal, the next matched character differs from
    that literal. Positive token lengths make the first following token character observable. -/
theorem optionalAbsentBoundary {optionalCharacter : Char}
    {restOps : List ScanOp} {source finalSuffix : List Char}
    (hmatch : ConsumingMatch restOps source finalSuffix)
    (hempty : finalSuffix = [])
    (hsafe : optionalBoundarySafe optionalCharacter restOps = true)
    (hpositive : positiveTokenLengthsOps restOps = true) :
    source = [] ∨
      ∃ actual tail, source = actual :: tail ∧ actual ≠ optionalCharacter := by
  induction hmatch with
  | empty =>
      rename_i matchedInput
      exact Or.inl hempty
  | literal tail ih =>
      rename_i next suffix remaining rest
      refine Or.inr ⟨next, _, rfl, ?_⟩
      intro heq
      simp [optionalBoundarySafe, consumingOps, heq] at hsafe
  | optionalPresent tail ih =>
      simp [optionalBoundarySafe, consumingOps] at hsafe
  | optionalAbsent tail ih =>
      simp [optionalBoundarySafe, consumingOps] at hsafe
  | tokenRun valid tail ih =>
      rename_i token lengthSpec tokenPrefix suffix remaining rest
      have hprefix : tokenPrefix ≠ [] := by
        intro hprefix
        subst tokenPrefix
        cases lengthSpec with
        | «exactly» width =>
            simp [positiveTokenLengthsOps] at hpositive
            have hwidth := valid.2
            simp [LenSpec.sat] at hwidth
            omega
        | «between» lower upper =>
            simp [positiveTokenLengthsOps] at hpositive
            have hlower := valid.2.1
            simp at hlower
            omega
        | «atLeastOne» =>
            simpa [matchesTerm, LenSpec.sat] using valid.2
      obtain ⟨actual, preTail, hprefixEq⟩ :=
        List.exists_cons_of_ne_nil hprefix
      rw [hprefixEq]
      refine Or.inr ⟨actual, preTail ++ suffix, by simp, ?_⟩
      intro heq
      subst actual
      have htoken : token.mem optionalCharacter :=
        valid.1 optionalCharacter (by rw [hprefixEq]; simp)
      simp [optionalBoundarySafe, consumingOps, tokenAccepts, htoken] at hsafe

end ConsumingMatch

/-- On a boundary-certified, positive-width operation sequence, the greedy consumer machine
    accepts every complete grammar-selected consumer path. -/
theorem executeConsumers_complete_aux
    {allOperations : List ScanOp} {source finalSuffix : List Char}
    (hmatch : ConsumingMatch allOperations source finalSuffix)
    (hempty : finalSuffix = [])
    (hsafe : boundariesSafe allOperations = true)
    (hpositive : positiveTokenLengthsOps allOperations = true) :
    executeConsumers allOperations source = some finalSuffix := by
  induction hmatch with
  | empty =>
      rfl
  | literal tail ih =>
      simp only [boundariesSafe] at hsafe
      simp only [positiveTokenLengthsOps, List.all_cons, Bool.true_and] at hpositive
      simpa [executeConsumers] using ih hempty hsafe hpositive
  | optionalPresent tail ih =>
      have hsafeTail := (Bool.and_eq_true_iff.mp hsafe).2
      simp only [positiveTokenLengthsOps, List.all_cons, Bool.true_and] at hpositive
      simpa [executeConsumers] using ih hempty hsafeTail hpositive
  | optionalAbsent tail ih =>
      have hsafeParts := Bool.and_eq_true_iff.mp hsafe
      simp only [positiveTokenLengthsOps, List.all_cons, Bool.true_and] at hpositive
      have hboundary := tail.optionalAbsentBoundary hempty hsafeParts.1 hpositive
      rcases hboundary with rfl | ⟨actual, rest, rfl, hne⟩
      · simpa [executeConsumers] using ih hempty hsafeParts.2 hpositive
      · simpa [executeConsumers, hne] using ih hempty hsafeParts.2 hpositive
  | tokenRun valid tail ih =>
      rename_i token lengthSpec tokenPrefix suffix remaining rest
      have hsafeParts := Bool.and_eq_true_iff.mp hsafe
      have hpositiveTail : positiveTokenLengthsOps rest = true := by
        unfold positiveTokenLengthsOps at hpositive ⊢
        rw [List.all_cons] at hpositive
        exact (Bool.and_eq_true_iff.mp hpositive).2
      have htail : ConsumingMatch rest suffix [] := by
        simpa [hempty] using tail
      have hboundary := htail.tokenBoundary hsafeParts.1
      have hwidth :
          ScanPlan.tokenWidth token lengthSpec (tokenPrefix ++ suffix) =
            tokenPrefix.length := by
        cases lengthSpec with
        | «exactly» =>
            exact tokenWidth_eq_of_append_boundary
              (pre := tokenPrefix) (suffix := suffix) valid trivial
        | «between» =>
            exact tokenWidth_eq_of_append_boundary
              (pre := tokenPrefix) (suffix := suffix) valid (by simpa using hboundary)
        | «atLeastOne» =>
            exact tokenWidth_eq_of_append_boundary
              (pre := tokenPrefix) (suffix := suffix) valid (by simpa using hboundary)
      have hprefixOk := termPrefixOk_append_length (suffix := suffix) valid
      simp only [executeConsumers, hwidth, hprefixOk, ite_true, List.drop_left]
      exact ih hempty hsafeParts.2 hpositiveTail

/-- The consumer machine has no false rejection on a complete certified match. -/
theorem executeConsumers_complete {operations : List ScanOp} {input : List Char}
    (hmatch : ConsumingMatch operations input [])
    (hsafe : boundariesSafe operations = true)
    (hpositive : positiveTokenLengthsOps operations = true) :
    executeConsumers operations input = some [] :=
  executeConsumers_complete_aux hmatch rfl hsafe hpositive

/-- Consumer execution composes over operation-list append. -/
theorem executeConsumers_append (first second : List ScanOp) (input : List Char) :
    executeConsumers (first ++ second) input =
      (executeConsumers first input).bind (executeConsumers second) := by
  induction first generalizing input with
  | nil =>
      rfl
  | cons operation rest ih =>
      cases operation with
      | beginCapture name keys | endCapture name =>
          simpa [executeConsumers] using ih input
      | literal character =>
          cases input with
          | nil =>
              rfl
          | cons actual tail =>
              by_cases heq : actual = character <;>
                simp [executeConsumers, heq, ih]
      | optionalLiteral character =>
          cases input with
          | nil =>
              simpa [executeConsumers] using ih []
          | cons actual tail =>
              by_cases heq : actual = character <;>
                simp [executeConsumers, heq, ih]
      | tokenRun token lengthSpec =>
          by_cases hprefix :
              termPrefixOk token lengthSpec input
                (ScanPlan.tokenWidth token lengthSpec input) = true <;>
            simp [executeConsumers, hprefix, ih]

/-- A successful capture-erased consumer run lifts to the structured cursor executor.
    Balanced capture markers preserve the final suffix, the surrounding capture stack, and
    the invariant that the cursor remains inside the input. -/
theorem executePattern_complete_of_consumers
    {input : List Char} {pattern : ScanPattern}
    {state : ScanPlan.ExecutionState} {remaining : List Char}
    (hconsumes :
      executeConsumers (consumingOps pattern.operations) (input.drop state.position) =
        some remaining)
    (hposition : state.position ≤ input.length) :
    ∃ finalState,
      ScanPlan.executePattern input pattern state = some finalState ∧
      input.drop finalState.position = remaining ∧
      finalState.starts = state.starts ∧
      finalState.position ≤ input.length := by
  induction pattern generalizing state remaining with
  | empty =>
      refine ⟨state, rfl, ?_, rfl, hposition⟩
      simpa [ScanPattern.operations, consumingOps, executeConsumers] using hconsumes
  | literal character rest ih =>
      cases hsuffix : input.drop state.position with
      | nil =>
          simp [ScanPattern.operations, consumingOps, executeConsumers, hsuffix] at hconsumes
      | cons actual tail =>
          by_cases heq : actual = character
          · subst actual
            have htail :
                executeConsumers (consumingOps rest.operations) tail = some remaining := by
              simpa [ScanPattern.operations, consumingOps, executeConsumers, hsuffix] using
                hconsumes
            let next : ScanPlan.ExecutionState :=
              { state with position := state.position + 1 }
            have hdrop : input.drop next.position = tail := by
              have htailDrop := congrArg (List.drop 1) hsuffix
              simpa [next, List.drop_drop] using htailDrop
            have hnextPosition : next.position ≤ input.length := by
              have hsuffixLength := congrArg List.length hsuffix
              simp [List.length_drop, next] at hsuffixLength ⊢
              omega
            obtain ⟨finalState, hrun, hremaining, hstarts, hfinalPosition⟩ :=
              ih (state := next) (remaining := remaining) (by simpa [hdrop] using htail)
                hnextPosition
            refine ⟨finalState, ?_, hremaining, ?_, hfinalPosition⟩
            · simpa [ScanPlan.executePattern, ScanPlan.executeOperation, hsuffix, next] using hrun
            · simpa [next] using hstarts
          · simp [ScanPattern.operations, consumingOps, executeConsumers, hsuffix, heq]
              at hconsumes
  | optionalLiteral character rest ih =>
      cases hsuffix : input.drop state.position with
      | nil =>
          have htail :
              executeConsumers (consumingOps rest.operations) [] = some remaining := by
            simpa [ScanPattern.operations, consumingOps, executeConsumers, hsuffix] using
              hconsumes
          obtain ⟨finalState, hrun, hremaining, hstarts, hfinalPosition⟩ :=
            ih (state := state) (remaining := remaining) (by simpa [hsuffix] using htail)
              hposition
          exact
            ⟨finalState,
              by simpa [ScanPlan.executePattern, ScanPlan.executeOperation, hsuffix] using hrun,
              hremaining, hstarts, hfinalPosition⟩
      | cons actual tail =>
          by_cases heq : actual = character
          · subst actual
            have htail :
                executeConsumers (consumingOps rest.operations) tail = some remaining := by
              simpa [ScanPattern.operations, consumingOps, executeConsumers, hsuffix] using
                hconsumes
            let next : ScanPlan.ExecutionState :=
              { state with position := state.position + 1 }
            have hdrop : input.drop next.position = tail := by
              have htailDrop := congrArg (List.drop 1) hsuffix
              simpa [next, List.drop_drop] using htailDrop
            have hnextPosition : next.position ≤ input.length := by
              have hsuffixLength := congrArg List.length hsuffix
              simp [List.length_drop, next] at hsuffixLength ⊢
              omega
            obtain ⟨finalState, hrun, hremaining, hstarts, hfinalPosition⟩ :=
              ih (state := next) (remaining := remaining) (by simpa [hdrop] using htail)
                hnextPosition
            refine ⟨finalState, ?_, hremaining, ?_, hfinalPosition⟩
            · simpa [ScanPlan.executePattern, ScanPlan.executeOperation, hsuffix, next] using hrun
            · simpa [next] using hstarts
          · have htail :
                executeConsumers (consumingOps rest.operations) (actual :: tail) =
                  some remaining := by
              simpa [ScanPattern.operations, consumingOps, executeConsumers, hsuffix, heq] using
                hconsumes
            obtain ⟨finalState, hrun, hremaining, hstarts, hfinalPosition⟩ :=
              ih (state := state) (remaining := remaining) (by simpa [hsuffix] using htail)
                hposition
            exact
              ⟨finalState,
                by
                  simpa [ScanPlan.executePattern, ScanPlan.executeOperation, hsuffix, heq]
                    using hrun,
                hremaining, hstarts, hfinalPosition⟩
  | tokenRun token lengthSpec rest ih =>
      let suffix := input.drop state.position
      let width := ScanPlan.tokenWidth token lengthSpec suffix
      by_cases hprefix : termPrefixOk token lengthSpec suffix width = true
      · have htail :
            executeConsumers (consumingOps rest.operations) (suffix.drop width) =
              some remaining := by
          simpa [ScanPattern.operations, consumingOps, executeConsumers, suffix, width, hprefix]
            using hconsumes
        let next : ScanPlan.ExecutionState :=
          { state with position := state.position + width }
        have hdrop : input.drop next.position = suffix.drop width := by
          simp [next, suffix, List.drop_drop]
        have hnextPosition : next.position ≤ input.length := by
          unfold termPrefixOk at hprefix
          have hwidthLe := (Bool.and_eq_true_iff.mp hprefix).1
          simp [next, suffix, List.length_drop] at hwidthLe ⊢
          omega
        obtain ⟨finalState, hrun, hremaining, hstarts, hfinalPosition⟩ :=
          ih (state := next) (remaining := remaining) (by simpa [hdrop] using htail)
            hnextPosition
        refine ⟨finalState, ?_, hremaining, ?_, hfinalPosition⟩
        · simpa [ScanPlan.executePattern, ScanPlan.executeOperation, suffix, width, hprefix, next]
            using hrun
        · simpa [next] using hstarts
      · simp [ScanPattern.operations, consumingOps, executeConsumers, suffix, width, hprefix]
          at hconsumes
  | capture name keys body rest bodyIH restIH =>
      rw [ScanPattern.operations, consumingOps, consumingOps_append,
        executeConsumers_append] at hconsumes
      obtain ⟨middle, hbodyConsumes, hrestConsumes⟩ :=
        Option.bind_eq_some_iff.mp hconsumes
      let frame : ScanPlan.OpenCapture :=
        { name := name
          keys := keys
          start := state.position
          captureMark := state.captureMap.length }
      let opened : ScanPlan.ExecutionState :=
        { state with starts := frame :: state.starts }
      obtain ⟨afterBody, hbodyRun, hmiddle, hbodyStarts, hbodyPosition⟩ :=
        bodyIH (state := opened) (remaining := middle) hbodyConsumes (by simpa [opened])
      have hbodyStarts' : afterBody.starts = frame :: state.starts := by
        simpa [opened] using hbodyStarts
      let text := ScanPlan.capturedText input frame.start afterBody.position
      let ownCaptures := frame.keys.map fun key => (key, text)
      let captureMap :=
        afterBody.captureMap.take frame.captureMark ++ ownCaptures ++
          afterBody.captureMap.drop frame.captureMark
      let closed : ScanPlan.ExecutionState :=
        { afterBody with
          starts := state.starts
          captures :=
            afterBody.captures ++
              [{ name, start := frame.start, stop := afterBody.position }]
          captureMap }
      have hclose :
          ScanPlan.executeOperation input (.endCapture name) afterBody = some closed := by
        simp [ScanPlan.executeOperation, hbodyStarts', ScanPlan.takeStart?, frame, closed,
          text, ownCaptures, captureMap]
      obtain ⟨finalState, hrestRun, hremaining, hrestStarts, hfinalPosition⟩ :=
        restIH (state := closed) (remaining := remaining)
          (by simpa [consumingOps, closed, hmiddle] using hrestConsumes)
          (by simpa [closed] using hbodyPosition)
      refine ⟨finalState, ?_, hremaining, ?_, hfinalPosition⟩
      · simp only [ScanPlan.executePattern]
        rw [show ScanPlan.executeOperation input (.beginCapture name keys) state = some opened by
          simp [ScanPlan.executeOperation, opened, frame]]
        simp [hbodyRun, hclose, hrestRun]
      · simpa [closed] using hrestStarts

/-- Removing capture markers twice has the same effect as removing them once. -/
@[simp] theorem consumingOps_idem (operations : List ScanOp) :
    consumingOps (consumingOps operations) = consumingOps operations := by
  induction operations with
  | nil =>
      rfl
  | cons operation rest ih =>
      cases operation <;> simp [consumingOps, ih]

/-- Boundary certification depends only on source-consuming operations. -/
@[simp] theorem boundariesSafe_consumingOps (operations : List ScanOp) :
    boundariesSafe (consumingOps operations) = boundariesSafe operations := by
  induction operations with
  | nil =>
      rfl
  | cons operation rest ih =>
      cases operation <;>
        simp [consumingOps, boundariesSafe, greedyBoundarySafe, optionalBoundarySafe, ih]

/-- Positive terminal widths are unchanged when capture markers are removed. -/
@[simp] theorem positiveTokenLengthsOps_consumingOps (operations : List ScanOp) :
    positiveTokenLengthsOps (consumingOps operations) =
      positiveTokenLengthsOps operations := by
  induction operations with
  | nil =>
      rfl
  | cons operation rest ih =>
      unfold positiveTokenLengthsOps at ih ⊢
      cases operation <;> simp [consumingOps, ih]

/-- A certified plan has positive-width direct terminal runs. -/
theorem ScanPlan.certified_positiveTokenLengths {plan : ScanPlan}
    (hcertified : plan.certified = true) :
    plan.positiveTokenLengths = true :=
  (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp hcertified).1).2

/-- A certified plan has deterministic direct-operation boundaries. -/
theorem ScanPlan.certified_deterministicBoundaries {plan : ScanPlan}
    (hcertified : plan.certified = true) :
    plan.deterministicBoundaries = true :=
  (Bool.and_eq_true_iff.mp hcertified).2

/-- A reference match for a mirrored grammar sequence exposes the same capture-erased consumer
    path used by the direct cursor program. -/
theorem ScanPattern.MirrorsSequence.consumingMatch_of_mem_matchSeq
    {g : Grammar} {qual : String} {fuel : Nat} {sequence : Triptych.Seq}
    {pattern : ScanPattern} {input remaining : List Char} {captures : CaptureMap}
    (hmirror : ScanPattern.MirrorsSequence g qual fuel sequence pattern)
    (hmem : (captures, remaining) ∈ matchSeq g qual fuel sequence input) :
    ConsumingMatch (consumingOps pattern.operations) input remaining := by
  induction hmirror generalizing input captures remaining with
  | empty =>
      have hshape := (mem_matchSeq_nil_iff g _ _ input remaining captures).mp hmem
      rcases hshape with ⟨rfl, rfl⟩
      exact .empty _
  | optionalLiteral htext tail tailIH =>
      rw [mem_matchSeq_cons_mk_optional_iff] at hmem
      rcases hmem with ⟨headCaptures, middle, tailCaptures, hhead, htail, rfl⟩ | htail
      · have hhead' :=
          (mem_matchSym_lit_iff g _ _ _ input middle headCaptures).mp hhead
        rcases hhead' with ⟨rfl, hinput⟩
        have htail' := tailIH htail
        simp only [htext, List.singleton_append] at hinput
        subst input
        exact .optionalPresent htail'
      · exact .optionalAbsent (tailIH htail)
  | literal htext tail tailIH =>
      rw [mem_matchSeq_cons_mk_required_iff] at hmem
      obtain ⟨headCaptures, middle, tailCaptures, hhead, htail, rfl⟩ := hmem
      have hhead' :=
        (mem_matchSym_lit_iff g _ _ _ input middle headCaptures).mp hhead
      rcases hhead' with ⟨rfl, hinput⟩
      have htail' := tailIH htail
      simp only [htext, List.singleton_append] at hinput
      subst input
      exact .literal htail'
  | tokenRun htoken hlength tail tailIH =>
      subst htoken
      subst hlength
      rw [mem_matchSeq_cons_mk_required_iff] at hmem
      obtain ⟨headCaptures, middle, tailCaptures, hhead, htail, rfl⟩ := hmem
      have hhead' :=
        (mem_matchSym_term_iff g _ _ _ _ input middle headCaptures).mp hhead
      rcases hhead' with ⟨rfl, pre, rfl, hmatches⟩
      exact .tokenRun hmatches (tailIH htail)
  | capture hname hkeys hproduction halternative body tail bodyIH tailIH =>
      subst hname
      subst hkeys
      rw [mem_matchSeq_cons_mk_required_iff] at hmem
      obtain ⟨headCaptures, middle, tailCaptures, hhead, htail, rfl⟩ := hmem
      have hhead' :=
        (mem_matchSym_ref_iff g _ _ _ _ hproduction input middle headCaptures).mp hhead
      obtain ⟨innerCaptures, hinner, _⟩ := hhead'
      unfold matchProd at hinner
      rw [halternative] at hinner
      simp only [List.flatMap_singleton] at hinner
      have hbody := bodyIH hinner
      have hrest := tailIH htail
      simpa [ScanPattern.operations, consumingOps, consumingOps_append] using
        hbody.append hrest

/-- If the reference decoder succeeds, a structurally mirrored certified direct plan cannot
    reject. This is the generic no-false-rejection theorem for every compiled `ScanPlan`. -/
theorem ScanPlan.decode_isSome_of_decode_eq_some
    {g : Grammar} {plan : ScanPlan} {source : String} {captures : CaptureMap}
    (hmirror : ScanPlan.MirrorsGrammar plan g)
    (hcertified : plan.certified = true)
    (hdecode : Triptych.decode g source = some captures) :
    (plan.decode source).isSome = true := by
  obtain ⟨foundProduction, hstart, hmatch⟩ :=
    mem_matchProd_of_decode_eq_some hdecode
  cases hmirror with
  | intro hstartEq production alternative hproduction halternative hsequence =>
      have hproductionEq : foundProduction = production := by
        rw [hproduction] at hstart
        injection hstart with heq
        exact heq.symm
      subst foundProduction
      unfold matchProd at hmatch
      rw [halternative] at hmatch
      simp only [List.flatMap_singleton] at hmatch
      have hconsumerMatch := hsequence.consumingMatch_of_mem_matchSeq hmatch
      have hconsumerRun :
          executeConsumers (consumingOps plan.pattern.operations) source.toList = some [] := by
        apply executeConsumers_complete hconsumerMatch
        · simpa [ScanPlan.deterministicBoundaries, ScanPlan.operations] using
            ScanPlan.certified_deterministicBoundaries hcertified
        · simpa [ScanPlan.positiveTokenLengths, ScanPlan.operations] using
            ScanPlan.certified_positiveTokenLengths hcertified
      obtain ⟨finalState, hrun, hremaining, hstarts, hposition⟩ :=
        executePattern_complete_of_consumers
          (state := ({} : ScanPlan.ExecutionState)) hconsumerRun (by simp)
      change source.toList.drop finalState.position = [] at hremaining
      change finalState.position ≤ source.toList.length at hposition
      change
        ScanPlan.executePattern source.toList plan.pattern {} = some finalState
        at hrun
      have hpositionEq : finalState.position = source.toList.length := by
        have hlength :
            source.toList.length - finalState.position = 0 := by
          simpa only [List.length_drop, List.length_nil] using
            congrArg List.length hremaining
        exact Nat.le_antisymm hposition (by omega)
      have hrunSome : (plan.runPattern source).isSome = true := by
        unfold ScanPlan.runPattern
        dsimp only
        rw [hrun]
        simp [hpositionEq, hstarts]
      rw [ScanPlan.decode_eq_decodePattern]
      unfold ScanPlan.decodePattern
      simpa [Option.isSome_map] using hrunSome

/-- A full structured-pattern match is one of the reference grammar's complete parses. -/
theorem ScanPlan.matchCaptures_mem_fullParses {grammar : Grammar} {plan : ScanPlan}
    {source : String} {captures : CaptureMap}
    (hmirror : ScanPlan.MirrorsGrammar plan grammar)
    (hmatch : plan.pattern.matchCaptures source.toList = some (captures, [])) :
    captures ∈ fullParses grammar source := by
  cases hmirror with
  | intro hstart production alternative hproduction halternative hsequence =>
      unfold fullParses
      rw [hproduction]
      rw [List.mem_map]
      refine ⟨(captures, []), ?_, rfl⟩
      rw [List.mem_filter]
      refine ⟨?_, by simp⟩
      unfold matchProd
      rw [halternative]
      simp only [List.flatMap_singleton]
      exact ScanPattern.matchCaptures_mem_matchSeq hsequence hmatch

/-- On a capture-functional grammar, a successful structured-pattern match is exactly the
    reference decoder result. -/
theorem decode_eq_of_scanPlan_matchCaptures_of_functional
    {grammar : Grammar} {plan : ScanPlan}
    {source : String} {captures : CaptureMap}
    (hmirror : ScanPlan.MirrorsGrammar plan grammar)
    (hfunctional : GrammarCaptureFunctional grammar)
    (hmatch : plan.pattern.matchCaptures source.toList = some (captures, [])) :
    decode grammar source = some captures := by
  apply decode_eq_of_mem_fullParses hfunctional
  exact plan.matchCaptures_mem_fullParses hmirror hmatch

/-- On a statically unique grammar, a successful structured-pattern match is exactly the
    reference decoder result. -/
theorem decode_eq_of_scanPlan_matchCaptures {grammar : Grammar} {plan : ScanPlan}
    {source : String} {captures : CaptureMap}
    (hmirror : ScanPlan.MirrorsGrammar plan grammar)
    (hunique : grammar.staticUnique = true)
    (hmatch : plan.pattern.matchCaptures source.toList = some (captures, [])) :
    decode grammar source = some captures :=
  decode_eq_of_scanPlan_matchCaptures_of_functional hmirror
    (GrammarCaptureFunctional.of_unique grammar
      (GrammarDecodeUnique.of_staticUnique grammar hunique))
    hmatch

/-- A complete ScanPlan certificate exposes both its structural grammar witness and the
    all-input uniqueness fact used by semantic soundness. -/
theorem ScanPlan.certifiedFor_mirrorsGrammar {grammar : Grammar} {plan : ScanPlan}
    (hcertified : plan.certifiedFor grammar = true) :
    ScanPlan.MirrorsGrammar plan grammar := by
  apply ScanPlan.mirrorsGrammar_of_matchesGrammar
  have hrest : (plan.matchesGrammar grammar && grammar.staticUnique) = true :=
    (Bool.and_eq_true_iff.mp hcertified).2
  exact (Bool.and_eq_true_iff.mp hrest).1

/-- A complete ScanPlan certificate includes grammar-level uniqueness. -/
theorem ScanPlan.certifiedFor_staticUnique {grammar : Grammar} {plan : ScanPlan}
    (hcertified : plan.certifiedFor grammar = true) :
    grammar.staticUnique = true := by
  have hrest : (plan.matchesGrammar grammar && grammar.staticUnique) = true :=
    (Bool.and_eq_true_iff.mp hcertified).2
  exact (Bool.and_eq_true_iff.mp hrest).2

/-- Every successful match produced by a certified structured pattern agrees with the reference
    decoder. This theorem depends only on the independently checkable certificate, not on how the
    plan was constructed. -/
theorem ScanPlan.matchCaptures_sound {grammar : Grammar} {plan : ScanPlan}
    {source : String} {captures : CaptureMap}
    (hcertified : plan.certifiedFor grammar = true)
    (hmatch : plan.pattern.matchCaptures source.toList = some (captures, [])) :
    Triptych.decode grammar source = some captures :=
  decode_eq_of_scanPlan_matchCaptures
    (plan.certifiedFor_mirrorsGrammar hcertified)
    (plan.certifiedFor_staticUnique hcertified)
    hmatch

/-- Every successful structured decode from a certified plan agrees with the reference decoder. -/
theorem ScanPlan.decodePattern_sound {grammar : Grammar} {plan : ScanPlan}
    {source : String} {captures : CaptureMap}
    (hcertified : plan.certifiedFor grammar = true)
    (hdecode : plan.decodePattern source = some captures) :
    Triptych.decode grammar source = some captures :=
  plan.matchCaptures_sound hcertified
    (ScanPattern.decodePattern_matchCaptures hdecode)

/-- Every successful flattened decode from a certified plan agrees with the reference decoder. -/
theorem ScanPlan.decode_sound {grammar : Grammar} {plan : ScanPlan}
    {source : String} {captures : CaptureMap}
    (hcertified : plan.certifiedFor grammar = true)
    (hdecode : plan.decode source = some captures) :
    Triptych.decode grammar source = some captures := by
  apply plan.decodePattern_sound hcertified
  simpa using hdecode

/-- A structural plan witness and a capture-functionality certificate are sufficient to justify
    every successful flattened decode. This is the proof surface used by generated staged
    parsers, which emit the structural witness directly instead of trusting a Boolean validator. -/
theorem ScanPlan.decode_sound_of_mirrors {grammar : Grammar} {plan : ScanPlan}
    {source : String} {captures : CaptureMap}
    (hmirror : ScanPlan.MirrorsGrammar plan grammar)
    (hfunctional : GrammarCaptureFunctional grammar)
    (hdecode : plan.decode source = some captures) :
    Triptych.decode grammar source = some captures := by
  apply decode_eq_of_scanPlan_matchCaptures_of_functional hmirror hfunctional
  apply ScanPattern.decodePattern_matchCaptures
  simpa using hdecode

/-- A structurally mirrored certified direct plan is extensionally equal to the reference
    decoder. Soundness identifies every direct result; generic completeness rules out false
    rejection, so no fallback search is required. -/
@[simp] theorem ScanPlan.decode_eq_decode_of_mirrors
    {grammar : Grammar} {plan : ScanPlan}
    (hmirror : ScanPlan.MirrorsGrammar plan grammar)
    (hfunctional : GrammarCaptureFunctional grammar)
    (hcertified : plan.certified = true)
    (source : String) :
    plan.decode source = Triptych.decode grammar source := by
  cases href : Triptych.decode grammar source with
  | none =>
      cases hdirect : plan.decode source with
      | none =>
          rfl
      | some captures =>
          have hsound :=
            plan.decode_sound_of_mirrors hmirror hfunctional hdirect
          rw [href] at hsound
          contradiction
  | some captures =>
      have hsome := plan.decode_isSome_of_decode_eq_some hmirror hcertified href
      cases hdirect : plan.decode source with
      | none =>
          change (plan.decode source).isSome = true at hsome
          rw [hdirect] at hsome
          contradiction
      | some directCaptures =>
          have hsound :=
            plan.decode_sound_of_mirrors hmirror hfunctional hdirect
          rw [href] at hsound
          injection hsound with heq
          subst directCaptures
          rfl

/-- Every successful match produced by a compiled structured pattern agrees with the reference
    decoder. No format-specific proof is required. -/
theorem compileScanPlan_matchCaptures_sound {grammar : Grammar} {plan : ScanPlan}
    {source : String} {captures : CaptureMap}
    (hcompile : compileScanPlan grammar = .ok plan)
    (hmatch : plan.pattern.matchCaptures source.toList = some (captures, [])) :
    decode grammar source = some captures :=
  plan.matchCaptures_sound (compileScanPlan_certifiedFor hcompile) hmatch

/-- Every successful structured decode from a compiled plan agrees with the reference decoder. -/
theorem compileScanPlan_decodePattern_sound {grammar : Grammar} {plan : ScanPlan}
    {source : String} {captures : CaptureMap}
    (hcompile : compileScanPlan grammar = .ok plan)
    (hdecode : plan.decodePattern source = some captures) :
    decode grammar source = some captures :=
  plan.decodePattern_sound (compileScanPlan_certifiedFor hcompile) hdecode

/-- Every successful flattened scan-plan decode agrees with the reference decoder. -/
theorem compileScanPlan_decode_sound {grammar : Grammar} {plan : ScanPlan}
    {source : String} {captures : CaptureMap}
    (hcompile : compileScanPlan grammar = .ok plan)
    (hdecode : plan.decode source = some captures) :
    decode grammar source = some captures :=
  plan.decode_sound (compileScanPlan_certifiedFor hcompile) hdecode

/-- Every successful decode from the lowered cursor program agrees with the reference decoder.
    This is the public soundness certificate consumed by direct backends. -/
theorem compileCursorProgram_decode_sound {grammar : Grammar} {plan : ScanPlan}
    {source : String} {captures : CaptureMap}
    (hcompile : compileScanPlan grammar = .ok plan)
    (hdecode : (lowerScanPlan plan).decode source = some captures) :
    decode grammar source = some captures := by
  apply compileScanPlan_decode_sound hcompile
  simpa using hdecode

/-- A fully certified ScanPlan is complete without a rejection fallback. -/
@[simp] theorem ScanPlan.decode_eq_decode {grammar : Grammar} {plan : ScanPlan}
    (hcertified : plan.certifiedFor grammar = true) (source : String) :
    plan.decode source = Triptych.decode grammar source := by
  have hplanCertified : plan.certified = true :=
    (Bool.and_eq_true_iff.mp hcertified).1
  have hfunctional : GrammarCaptureFunctional grammar :=
    GrammarCaptureFunctional.of_unique grammar
      (GrammarDecodeUnique.of_staticUnique grammar
        (plan.certifiedFor_staticUnique hcertified))
  exact plan.decode_eq_decode_of_mirrors
    (plan.certifiedFor_mirrorsGrammar hcertified)
    hfunctional hplanCertified source

/-- A directly compiled ScanPlan agrees with the reference decoder on every input. -/
@[simp] theorem compileScanPlan_decode_eq_decode {grammar : Grammar} {plan : ScanPlan}
    (hcompile : compileScanPlan grammar = .ok plan) (source : String) :
    plan.decode source = Triptych.decode grammar source :=
  plan.decode_eq_decode (compileScanPlan_certifiedFor hcompile) source

/-- The lowered cursor program inherits direct completeness from its ScanPlan certificate. -/
@[simp] theorem CursorProgram.decode_eq_decode
    {grammar : Grammar} {plan : ScanPlan}
    (hcertified : plan.certifiedFor grammar = true) (source : String) :
    (lowerScanPlan plan).decode source = Triptych.decode grammar source := by
  rw [CursorProgram.lowerScanPlan_decode]
  exact plan.decode_eq_decode hcertified source

/-- A mirrored lowered cursor program is directly complete without `scanSearch`. -/
@[simp] theorem CursorProgram.decode_eq_decode_of_mirrors
    {grammar : Grammar} {plan : ScanPlan}
    (hmirror : ScanPlan.MirrorsGrammar plan grammar)
    (hfunctional : GrammarCaptureFunctional grammar)
    (hcertified : plan.certified = true)
    (source : String) :
    (lowerScanPlan plan).decode source = Triptych.decode grammar source := by
  rw [CursorProgram.lowerScanPlan_decode]
  exact plan.decode_eq_decode_of_mirrors hmirror hfunctional hcertified source

/-- A directly certified ScanPlan rejects exactly the strings rejected by the grammar. -/
theorem ScanPlan.decode_eq_none_iff {grammar : Grammar} {plan : ScanPlan}
    (hcertified : plan.certifiedFor grammar = true) (source : String) :
    plan.decode source = none ↔ Triptych.decode grammar source = none := by
  rw [plan.decode_eq_decode hcertified]

/-- A directly certified ScanPlan returns exactly the reference decoder's capture map. -/
theorem ScanPlan.decode_eq_some_iff {grammar : Grammar} {plan : ScanPlan}
    (hcertified : plan.certifiedFor grammar = true)
    (source : String) (captures : CaptureMap) :
    plan.decode source = some captures ↔
      Triptych.decode grammar source = some captures := by
  rw [plan.decode_eq_decode hcertified]

/-- A directly certified lowered cursor program has exact rejection. -/
theorem CursorProgram.decode_eq_none_iff
    {grammar : Grammar} {plan : ScanPlan}
    (hcertified : plan.certifiedFor grammar = true) (source : String) :
    (lowerScanPlan plan).decode source = none ↔
      Triptych.decode grammar source = none := by
  rw [CursorProgram.decode_eq_decode hcertified]

/-- A directly certified lowered cursor program returns exactly the selected captures. -/
theorem CursorProgram.decode_eq_some_iff
    {grammar : Grammar} {plan : ScanPlan}
    (hcertified : plan.certifiedFor grammar = true)
    (source : String) (captures : CaptureMap) :
    (lowerScanPlan plan).decode source = some captures ↔
      Triptych.decode grammar source = some captures := by
  rw [CursorProgram.decode_eq_decode hcertified]

/-- A compiled lowered cursor program is directly complete on every input. -/
@[simp] theorem compileCursorProgram_decode_eq_decode
    {grammar : Grammar} {plan : ScanPlan}
    (hcompile : compileScanPlan grammar = .ok plan) (source : String) :
    (lowerScanPlan plan).decode source = Triptych.decode grammar source :=
  CursorProgram.decode_eq_decode (compileScanPlan_certifiedFor hcompile) source

/-- The certified ScanPlan parser is extensionally equal to the reference decoder. The direct
    plan handles its successful fast path; `scanSearch` supplies completeness and exact rejection
    only when that plan returns `none`. -/
@[simp] theorem ScanPlan.decodeCertified_eq_decode {grammar : Grammar} {plan : ScanPlan}
    (hcertified : plan.certifiedFor grammar = true) (source : String) :
    plan.decodeCertified grammar source = Triptych.decode grammar source := by
  unfold ScanPlan.decodeCertified
  cases hdirect : plan.decode source with
  | none => simp [scanSearch_eq_decode]
  | some captures =>
      have hsound : Triptych.decode grammar source = some captures :=
        plan.decode_sound hcertified hdirect
      simp [hsound]

/-- A structurally mirrored plan with functional captures is complete once direct rejection falls
    back to `scanSearch`. This form lets generated parsers carry a constructor proof rather than
    a native Boolean certificate. -/
@[simp] theorem ScanPlan.decodeCertified_eq_decode_of_mirrors
    {grammar : Grammar} {plan : ScanPlan}
    (hmirror : ScanPlan.MirrorsGrammar plan grammar)
    (hfunctional : GrammarCaptureFunctional grammar)
    (source : String) :
    plan.decodeCertified grammar source = Triptych.decode grammar source := by
  unfold ScanPlan.decodeCertified
  cases hdirect : plan.decode source with
  | none => simp [scanSearch_eq_decode]
  | some captures =>
      have hsound : Triptych.decode grammar source = some captures :=
        plan.decode_sound_of_mirrors hmirror hfunctional hdirect
      simp [hsound]

/-- A certified ScanPlan rejects exactly the strings rejected by the grammar decoder. -/
theorem ScanPlan.decodeCertified_eq_none_iff {grammar : Grammar} {plan : ScanPlan}
    (hcertified : plan.certifiedFor grammar = true) (source : String) :
    plan.decodeCertified grammar source = none ↔
      Triptych.decode grammar source = none := by
  rw [plan.decodeCertified_eq_decode hcertified]

/-- A certified ScanPlan returns a capture map exactly when the grammar decoder returns it. -/
theorem ScanPlan.decodeCertified_eq_some_iff {grammar : Grammar} {plan : ScanPlan}
    (hcertified : plan.certifiedFor grammar = true)
    (source : String) (captures : CaptureMap) :
    plan.decodeCertified grammar source = some captures ↔
      Triptych.decode grammar source = some captures := by
  rw [plan.decodeCertified_eq_decode hcertified]

/-- The certified ScanPlan parser is extensionally equal to the reference decoder. The direct
    plan handles its successful fast path; `scanSearch` supplies completeness and exact rejection
    only when that plan returns `none`. -/
@[simp] theorem compileScanPlan_decodeCertified_eq_decode {grammar : Grammar} {plan : ScanPlan}
    (hcompile : compileScanPlan grammar = .ok plan) (source : String) :
    plan.decodeCertified grammar source = decode grammar source :=
  plan.decodeCertified_eq_decode (compileScanPlan_certifiedFor hcompile) source

/-- A lowered cursor program inherits generic completeness from its source ScanPlan certificate. -/
@[simp] theorem CursorProgram.decodeCertified_eq_decode
    {grammar : Grammar} {plan : ScanPlan}
    (hcertified : plan.certifiedFor grammar = true) (source : String) :
    (lowerScanPlan plan).decodeCertified grammar source =
      Triptych.decode grammar source := by
  rw [CursorProgram.lowerScanPlan_decodeCertified]
  exact plan.decodeCertified_eq_decode hcertified source

/-- Lowering preserves the structurally certified complete parser. -/
@[simp] theorem CursorProgram.decodeCertified_eq_decode_of_mirrors
    {grammar : Grammar} {plan : ScanPlan}
    (hmirror : ScanPlan.MirrorsGrammar plan grammar)
    (hfunctional : GrammarCaptureFunctional grammar)
    (source : String) :
    (lowerScanPlan plan).decodeCertified grammar source =
      Triptych.decode grammar source := by
  rw [CursorProgram.lowerScanPlan_decodeCertified]
  exact plan.decodeCertified_eq_decode_of_mirrors hmirror hfunctional source

/-- A certified lowered cursor program has exact rejection. -/
theorem CursorProgram.decodeCertified_eq_none_iff
    {grammar : Grammar} {plan : ScanPlan}
    (hcertified : plan.certifiedFor grammar = true) (source : String) :
    (lowerScanPlan plan).decodeCertified grammar source = none ↔
      Triptych.decode grammar source = none := by
  rw [CursorProgram.decodeCertified_eq_decode hcertified]

/-- A certified lowered cursor program is complete and preserves the selected capture map. -/
theorem CursorProgram.decodeCertified_eq_some_iff
    {grammar : Grammar} {plan : ScanPlan}
    (hcertified : plan.certifiedFor grammar = true)
    (source : String) (captures : CaptureMap) :
    (lowerScanPlan plan).decodeCertified grammar source = some captures ↔
      Triptych.decode grammar source = some captures := by
  rw [CursorProgram.decodeCertified_eq_decode hcertified]

/-- The verified-lowered cursor program has no false rejections and returns exactly the same
    captures as the reference decoder for every input. -/
@[simp] theorem compileCursorProgram_decodeCertified_eq_decode
    {grammar : Grammar} {plan : ScanPlan}
    (hcompile : compileScanPlan grammar = .ok plan) (source : String) :
    (lowerScanPlan plan).decodeCertified grammar source = decode grammar source :=
  CursorProgram.decodeCertified_eq_decode (compileScanPlan_certifiedFor hcompile) source

/-- A certified cursor program rejects exactly the strings rejected by the grammar decoder. -/
theorem compileCursorProgram_decodeCertified_eq_none_iff
    {grammar : Grammar} {plan : ScanPlan}
    (hcompile : compileScanPlan grammar = .ok plan) (source : String) :
    (lowerScanPlan plan).decodeCertified grammar source = none ↔
      decode grammar source = none := by
  exact CursorProgram.decodeCertified_eq_none_iff
    (compileScanPlan_certifiedFor hcompile) source

/-- A certified cursor program returns a capture map exactly when the grammar decoder returns
    that same map. -/
theorem compileCursorProgram_decodeCertified_eq_some_iff
    {grammar : Grammar} {plan : ScanPlan}
    (hcompile : compileScanPlan grammar = .ok plan)
    (source : String) (captures : CaptureMap) :
    (lowerScanPlan plan).decodeCertified grammar source = some captures ↔
      decode grammar source = some captures := by
  exact CursorProgram.decodeCertified_eq_some_iff
    (compileScanPlan_certifiedFor hcompile) source captures

end Triptych
