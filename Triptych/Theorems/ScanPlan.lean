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
import Triptych.Archive.DecodeLemmas
import Triptych.Theorems.Scanner
import Triptych.Theorems.Unambiguity

/-!
# Scan-plan correctness

The architecture layer proves that structured scan patterns flatten to cursor programs without
changing execution. This module connects the structured pattern back to the archived reference
grammar semantics. Every successful direct match is a reference match. The certified parser then
uses the complete continuation scanner only after direct rejection, yielding full equivalence,
including completeness and exact rejection, for every successfully compiled plan.
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
  · rw [if_pos hcomplete] at hresult
    injection hresult with hresult
    subst result
    obtain ⟨captures, hmatch, _, hcaptures⟩ := executePattern_sound hexecute
    have hposition : state.position = source.toList.length := by
      simpa using (Bool.and_eq_true_iff.mp hcomplete).1
    simp at hcaptures
    subst captures
    simpa [hposition] using hmatch
  · rw [if_neg hcomplete] at hresult
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
          · simp only [matchCaptures, heq, if_true] at hmatch
            refine Or.inl ⟨[], input, captures, ?_, tailIH hmatch, by simp⟩
            simp [matchSym, htext, heq]
          · simp only [matchCaptures, heq, if_false] at hmatch
            exact Or.inr (tailIH hmatch)
  | literal htext tail tailIH =>
      rename_i character matchedQual matchedFuel rest tailPattern text
      rw [mem_matchSeq_cons_mk_required_iff]
      cases input with
      | nil => simp [matchCaptures] at hmatch
      | cons actual input =>
          by_cases heq : actual = character
          · simp only [matchCaptures, heq, if_true] at hmatch
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
