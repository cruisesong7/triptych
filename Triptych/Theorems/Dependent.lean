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

import Triptych.Architecture.Dependent
import Triptych.Archive.ScannerProfile
import Triptych.Theorems.Scanner

/-!
# Correctness of dependent scanning

The reference semantics enumerates header-prefix candidates in source order and runs the
archived complete decoder on the tail grammar selected by each candidate. The executable
dependent scanner fuses the header enumeration with its continuation and uses the verified
runtime scanner for each selected tail.
-/

namespace Triptych

/-- Ordered reference semantics for a header-dependent tail grammar. -/
def decodeDependent (header : Grammar) (body : CaptureMap → Grammar)
    (input : String) : Option CaptureMap :=
  match header.startProd? with
  | none => none
  | some headerProduction =>
      (matchProd header "" header.prods.length headerProduction input.toList).findSome?
        fun found =>
          (decode (body found.1) (String.ofList found.2)).map
            fun bodyCaptures => found.1 ++ bodyCaptures

/-- Order-independent recognition semantics for a dependent format: some header-prefix parse
    selects a tail grammar that has a complete parse of the remaining input. -/
def DependentAccepts (header : Grammar) (body : CaptureMap → Grammar)
    (input : String) : Prop :=
  match header.startProd? with
  | none => False
  | some production =>
      ∃ found ∈ matchProd header "" header.prods.length production input.toList,
        fullParses (body found.1) (String.ofList found.2) ≠ []

/-- Dependent scanning is exactly the ordered reference semantics. -/
@[simp] theorem scanDependent_eq_decodeDependent
    (header : Grammar) (body : CaptureMap → Grammar) (input : String) :
    scanDependent header body input = decodeDependent header body input := by
  unfold scanDependent decodeDependent
  cases hheader : header.startProd? with
  | none => rfl
  | some headerProduction =>
      simp only
      rw [scanProdK_eq_matchProd]
      congr 1
      funext found
      rw [scan_eq_decode]

/-- The dependent scanner succeeds exactly when the declarative dependent format recognizes the
    input. Candidate ordering affects which captures are returned, not recognition. -/
theorem scanDependent_isSome_iff (header : Grammar) (body : CaptureMap → Grammar)
    (input : String) :
    (scanDependent header body input).isSome = true ↔
      DependentAccepts header body input := by
  rw [scanDependent_eq_decodeDependent]
  unfold decodeDependent DependentAccepts
  cases hheader : header.startProd? with
  | none => simp
  | some production =>
      simp only
      rw [List.findSome?_isSome_iff]
      simp only [Option.isSome_map]
      constructor
      · rintro ⟨found, hmem, hsome⟩
        exact ⟨found, hmem, (decode_isSome_iff _ _).mp hsome⟩
      · rintro ⟨found, hmem, hfull⟩
        exact ⟨found, hmem, (decode_isSome_iff _ _).mpr hfull⟩

/-- Dependent semantic computation uses the same capture assignment as the reference decoder. -/
@[simp] theorem dependentComputeValueMap_eq
    {α : Type} (header : Grammar) (body : CaptureMap → Grammar)
    (valueFn : CaptureMap → α) (input : String) :
    dependentComputeValueMap header body valueFn input =
      (decodeDependent header body input).map valueFn := by
  simp [dependentComputeValueMap]

private theorem profileDependentCandidates_result (body : CaptureMap → Grammar)
    (candidates : List (CaptureMap × List Char)) :
    (profileDependentCandidates body candidates).result =
      candidates.findSome? fun found =>
        (scan (body found.1) (String.ofList found.2)).map fun bodyCaptures =>
          found.1 ++ bodyCaptures := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih =>
      obtain ⟨headerCaptures, remaining⟩ := candidate
      simp only [profileDependentCandidates, List.findSome?_cons]
      rw [← scanProfile_result]
      cases htail : (scanProfile (body headerCaptures) (String.ofList remaining)).result with
      | none => simp [ih]
      | some bodyCaptures => simp

/-- Profiling preserves the executable dependent scanner's result. -/
@[simp] theorem dependentScanProfile_result (header : Grammar)
    (body : CaptureMap → Grammar) (input : String) :
    (dependentScanProfile header body input).result = scanDependent header body input := by
  unfold dependentScanProfile scanDependent
  cases hheader : header.startProd? with
  | none => rfl
  | some production =>
      simp only
      rw [profileDependentCandidates_result]
      rw [scanProdK_eq_matchProd]

private theorem profileDependentCandidates_checks_le (body : CaptureMap → Grammar)
    (candidates : List (CaptureMap × List Char)) :
    (profileDependentCandidates body candidates).headerCandidateChecks +
        (profileDependentCandidates body candidates).tailCandidateChecks ≤
      dependentCandidateBudgetFor body candidates := by
  induction candidates with
  | nil => simp [profileDependentCandidates, dependentCandidateBudgetFor]
  | cons candidate rest ih =>
      obtain ⟨headerCaptures, remaining⟩ := candidate
      simp only [profileDependentCandidates, dependentCandidateBudgetFor]
      have hchecks :=
        scannerCandidateChecks_le (body headerCaptures) (String.ofList remaining)
      unfold scannerCandidateChecks at hchecks
      cases htail : (scanProfile (body headerCaptures) (String.ofList remaining)).result with
      | some bodyCaptures =>
          simp only
          omega
      | none =>
          simp only
          omega

/-- Every dependent scan performs no more completed header/tail candidate checks than its
    finite archived candidate budget. -/
theorem dependentCandidateChecks_le (header : Grammar) (body : CaptureMap → Grammar)
    (input : String) :
    (dependentScanProfile header body input).headerCandidateChecks +
        (dependentScanProfile header body input).tailCandidateChecks ≤
      dependentCandidateBudget header body input := by
  unfold dependentScanProfile dependentCandidateBudget
  cases hheader : header.startProd? with
  | none => simp
  | some production => exact profileDependentCandidates_checks_le body _

/-! ## Executable regression evidence -/

private def lengthHeaderGrammar : Grammar where
  start := "Start"
  prods := [
    { name := "Start", alts := [[{ sym := .ref "Width" }]] },
    { name := "Width", alts := [[{ sym := .term .digit (.exactly 1) }]] }
  ]

private def lowerAsciiPayloadGrammar (captures : CaptureMap) : Grammar :=
  let width := (captures.toEnv "Width").map readNat |>.getD 0
  {
    start := "Start"
    prods := [
      { name := "Start", alts := [[{ sym := .ref "Payload" }]] },
      {
        name := "Payload"
        alts := [[{ sym := .term (.asciiRange 97 122) (.exactly width) }]]
      }
    ]
  }

#guard scanDependent lengthHeaderGrammar lowerAsciiPayloadGrammar "3abc" =
  some [("Width", "3"), ("Payload", "abc")]
#guard scanDependent lengthHeaderGrammar lowerAsciiPayloadGrammar "2abc" = none
#guard scanDependent lengthHeaderGrammar lowerAsciiPayloadGrammar "3ab1" = none
#guard (dependentScanProfile lengthHeaderGrammar lowerAsciiPayloadGrammar "3abc").result =
  scanDependent lengthHeaderGrammar lowerAsciiPayloadGrammar "3abc"
#guard
  (dependentScanProfile lengthHeaderGrammar lowerAsciiPayloadGrammar "3abc").tailCandidateChecks =
    0

end Triptych
