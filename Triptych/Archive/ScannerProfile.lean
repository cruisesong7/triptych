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
import Triptych.Architecture.Dependent
import Triptych.Archive.ReferenceDecoder

/-!
# Proof-only scanner profiles

This module connects runtime scanning to the archived candidate tree for proofs, diagnostics,
and benchmarks. Importing `Triptych.Architecture.Scanner` alone does not import the decoder.
-/

namespace Triptych

/-- Result and completed-candidate count for the scanner's root continuation. -/
structure ScanSearchProfile where
  result : Option CaptureMap
  candidateChecks : Nat
  deriving Repr, Inhabited, DecidableEq

/-- Inspect ordered root candidates until the first full-consumption candidate is found. -/
def profileCompleteCandidates : List (CaptureMap × List Char) → ScanSearchProfile
  | [] => ⟨none, 0⟩
  | (captures, remaining) :: rest =>
      if remaining.isEmpty then
        ⟨some captures, 1⟩
      else
        let tail := profileCompleteCandidates rest
        ⟨tail.result, tail.candidateChecks + 1⟩

/-- Proof-only profile corresponding to `scanSearch`. -/
def scanSearchProfile (g : Grammar) (input : String) : ScanSearchProfile :=
  match g.startProd? with
  | none => ⟨none, 0⟩
  | some production =>
      profileCompleteCandidates
        (matchProd g "" g.prods.length production input.toList)

/-- Number of complete root candidates available to the ordered scanner search. -/
def scannerCandidateBudget (g : Grammar) (input : String) : Nat :=
  match g.startProd? with
  | none => 0
  | some production =>
      (matchProd g "" g.prods.length production input.toList).length

/-- Proof-only profile of the public scanner, including its certified fast path. -/
def scanProfile (g : Grammar) (input : String) : ScanSearchProfile :=
  if g.staticUnique then
    match fastScan g input with
    | some captures => ⟨some captures, 0⟩
    | none => scanSearchProfile g input
  else
    scanSearchProfile g input

/-- Completed root-candidate checks performed by the public scanner's search phase. -/
def scannerCandidateChecks (g : Grammar) (input : String) : Nat :=
  (scanProfile g input).candidateChecks

/-! ## Dependent scanner profiles -/

/-- Result and candidate counts for a header-dependent scan. Header candidates and completed
    tail candidates are counted separately so generated diagnostics can distinguish an
    ambiguous header from search inside the selected payload grammar. -/
structure DependentScanProfile where
  result : Option CaptureMap
  headerCandidateChecks : Nat
  tailCandidateChecks : Nat
  deriving Repr, Inhabited, DecidableEq

/-- Inspect ordered header candidates until one of their generated tail grammars accepts. -/
def profileDependentCandidates (body : CaptureMap → Grammar) :
    List (CaptureMap × List Char) → DependentScanProfile
  | [] => ⟨none, 0, 0⟩
  | (headerCaptures, remaining) :: rest =>
      let tail := scanProfile (body headerCaptures) (String.ofList remaining)
      match tail.result with
      | some bodyCaptures =>
          ⟨some (headerCaptures ++ bodyCaptures), 1, tail.candidateChecks⟩
      | none =>
          let fallback := profileDependentCandidates body rest
          ⟨fallback.result, fallback.headerCandidateChecks + 1,
            fallback.tailCandidateChecks + tail.candidateChecks⟩

/-- Proof-only profile of `scanDependent`. -/
def dependentScanProfile (header : Grammar) (body : CaptureMap → Grammar)
    (input : String) : DependentScanProfile :=
  match header.startProd? with
  | none => ⟨none, 0, 0⟩
  | some production =>
      profileDependentCandidates body
        (matchProd header "" header.prods.length production input.toList)

/-- Finite candidate budget for one ordered dependent scan. -/
def dependentCandidateBudgetFor (body : CaptureMap → Grammar) :
    List (CaptureMap × List Char) → Nat
  | [] => 0
  | candidate :: rest =>
      1 + scannerCandidateBudget (body candidate.1) (String.ofList candidate.2) +
        dependentCandidateBudgetFor body rest

/-- Candidate budget selected by a header grammar and dependent tail factory. -/
def dependentCandidateBudget (header : Grammar) (body : CaptureMap → Grammar)
    (input : String) : Nat :=
  match header.startProd? with
  | none => 0
  | some production =>
      dependentCandidateBudgetFor body
        (matchProd header "" header.prods.length production input.toList)

/-- Result and completed-root-candidate count for a generated parser execution. -/
structure ScannerParserProfile (δ : Type) where
  result : Option δ
  candidateChecks : Nat

/-- Proof-only profile of the generated single-scan parser. The runtime parser does not
    construct this record; it exists to expose the result and scanner search cost together. -/
def scannerParseMapProfile {β δ : Type} (g : Grammar)
    (constraints : List ConstraintEntry) (valueFn : CaptureMap → β)
    (ofSpec : β → δ) (input : String) : ScannerParserProfile δ :=
  let scanResult := scanProfile g input
  let result :=
    match scanResult.result with
    | none => none
    | some captures =>
        if CaptureAccepts constraints captures then
          some (ofSpec (valueFn captures))
        else
          none
  ⟨result, scanResult.candidateChecks⟩

/-- Environment-reader specialization of `scannerParseMapProfile`. -/
def scannerParseFProfile {β δ : Type} (g : Grammar)
    (constraints : List ConstraintEntry) (valueFn : Env → β)
    (ofSpec : β → δ) (input : String) : ScannerParserProfile δ :=
  scannerParseMapProfile g constraints (fun captures => valueFn captures.toEnv) ofSpec input

/-- Analyzable `ValExpr` specialization of `scannerParseMapProfile`. -/
def scannerParseProfile (g : Grammar) (constraints : List ConstraintEntry)
    (valueExpr : ValExpr) (ofSpec : Int → δ) (input : String) : ScannerParserProfile δ :=
  scannerParseFProfile g constraints valueExpr.eval ofSpec input

end Triptych
