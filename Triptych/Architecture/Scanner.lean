/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Triptych.Archive.ReferenceDecoder
import Triptych.Architecture.Unambiguity

/-!
# Executable scanner

`decode` is the archived reference semantics: it materializes every possible prefix match and
then selects the first complete parse. This module implements the same ordered search directly.
Continuations fuse symbol, sequence, and production matching, so failed candidates are discarded
immediately and the first complete parse stops the search.

The complete scanner handles every current grammar form:

* literals and quoted string literals;
* fixed- and variable-width token runs;
* source-ordered alternatives and present-before-absent optional symbols;
* separated repetitions with the same stop-before-continue policy as the reference decoder;
* named captures, including qualified and repetition-count captures.

For statically unique grammars, a boundary-driven specialization first tries the deterministic
path without enumerating candidate prefix lengths. If that path cannot handle the grammar, the
complete continuation scanner continues the same request. No generated parser calls the
reference decoder at runtime.
-/

namespace Triptych

/-! ## Boundary-driven specialization -/

/-- What must follow a specialized scan. -/
inductive ScanBoundary where
  /-- The production must consume the rest of the input. -/
  | endOfInput
  /-- The unconsumed suffix must begin with this literal. -/
  | literal (text : String)
  /-- The caller has no directly inspectable boundary. -/
  | unknown
  deriving Repr, DecidableEq

/-- Fixed width when the length specification determines exactly one width. -/
def LenSpec.fixedWidth? : LenSpec → Option Nat
  | .exactly n => some n
  | .between lo hi => if lo == hi then some lo else none
  | .atLeastOne => none

/-- The direct literal boundary at the head of a remaining sequence. -/
def scanBoundary? : Seq → Option ScanBoundary
  | { sym := .lit literal, optional := false } :: _ =>
      if literal.isEmpty then none else some (.literal literal)
  | _ => none

/-- Choose the one prefix length inspected by the specialized terminal scanner. -/
def fastScanTokenLength (tok : TokClass) (lengthSpec : LenSpec) (input : List Char) : Nat :=
  match lengthSpec.fixedWidth? with
  | some width => width
  | none => (input.takeWhile fun c => decide (tok.mem c)).length

/-- Whether a specialized production ends where its caller requires. -/
def ScanBoundary.accepts : ScanBoundary → List Char → Bool
  | .endOfInput, remaining => remaining.isEmpty
  | .literal text, remaining => text.toList.isPrefixOf remaining
  | .unknown, _ => true

/-- Compose one specialized item with the scanner for the rest of its sequence. -/
def fastScanPresent (head : Option (CaptureMap × List Char))
    (scanTail : List Char → Option (CaptureMap × List Char)) :
    Option (CaptureMap × List Char) :=
  head.bind fun found =>
    (scanTail found.2).map fun tail =>
      (found.1 ++ tail.1, tail.2)

/-- Select the first alternative that reaches the caller's boundary. -/
def fastScanAlternatives (boundary : ScanBoundary)
    (scanAlternative : Seq → Option (CaptureMap × List Char)) :
    List Seq → Option (CaptureMap × List Char)
  | [] => none
  | alternative :: rest =>
      match scanAlternative alternative with
      | some result =>
          if boundary.accepts result.2 then some result
          else fastScanAlternatives boundary scanAlternative rest
      | none => fastScanAlternatives boundary scanAlternative rest

mutual

/-- Specialized scanner for one symbol. Quoted strings and repetitions defer to the complete
    scanner by returning `none`. -/
def fastScanSym (g : Grammar) (qual : String) :
    Nat → ScanBoundary → Sym → List Char → Option (CaptureMap × List Char)
  | _, _, .lit literal, input =>
      let chars := literal.toList
      if chars.isPrefixOf input then some ([], input.drop chars.length) else none
  | _, _, .str, _ => none
  | _, _, .term tok lengthSpec, input =>
      let width := fastScanTokenLength tok lengthSpec input
      if termPrefixOk tok lengthSpec input width then some ([], input.drop width) else none
  | _, _, .rep _ _ _ _, _ => none
  | 0, _, .ref _, _ => none
  | fuel + 1, boundary, .ref name, input =>
      match g.prod? name with
      | none => none
      | some production =>
          (fastScanProd g name fuel boundary production input).map fun (captures, remaining) =>
            let consumed := String.ofList (input.take (input.length - remaining.length))
            let keys :=
              if qual.isEmpty then [(name, consumed)]
              else [(name, consumed), (qual ++ "." ++ name, consumed)]
            (keys ++ captures, remaining)

/-- Specialized scanner for a sequence. -/
def fastScanSeq (g : Grammar) (qual : String) (fuel : Nat) :
    ScanBoundary → Seq → List Char → Option (CaptureMap × List Char)
  | _, [], input => some ([], input)
  | outerBoundary, item :: rest, input =>
      let itemBoundary :=
        match scanBoundary? rest with
        | some boundary => boundary
        | none => if rest.isEmpty then outerBoundary else .unknown
      let present :=
        fastScanPresent (fastScanSym g qual fuel itemBoundary item.sym input)
          (fastScanSeq g qual fuel outerBoundary rest)
      if item.optional then
        present.orElse fun _ => fastScanSeq g qual fuel outerBoundary rest input
      else
        present

/-- Specialized scanner for a production. -/
def fastScanProd (g : Grammar) (qual : String) (fuel : Nat) (boundary : ScanBoundary) :
    Production → List Char → Option (CaptureMap × List Char)
  | production, input =>
      fastScanAlternatives boundary (fun alternative =>
        fastScanSeq g qual fuel boundary alternative input) production.alts

end

/-- Run the boundary-driven specialization on a complete input. -/
def fastScan (g : Grammar) (input : String) : Option CaptureMap :=
  match g.startProd? with
  | none => none
  | some production =>
      match fastScanProd g "" g.prods.length .endOfInput production input.toList with
      | some (captures, []) => some captures
      | _ => none

/-! ## Complete continuation scanner -/

/-- Continue with `fallback` only if `attempt` failed. -/
def scanOrElse (attempt : Option α) (fallback : Unit → Option α) : Option α :=
  attempt.orElse fallback

/-- Does a separated-repetition count satisfy its declared bounds? -/
def repetitionCountOk (lo : Nat) (hi : Option Nat) (itemCount : Nat) : Bool :=
  lo ≤ itemCount && match hi with
    | none => true
    | some upper => itemCount ≤ upper

/-- Lazily scan the `(separator item)*` tail. The current count is offered to the caller before
    another item is attempted, matching the reference decoder's stop-before-continue order. -/
def scanStarK {α : Type} (scanItem :
      List Char → (CaptureMap → List Char → Option α) → Option α)
    (separator : List Char) (lo : Nat) (hi : Option Nat) :
    Nat → List Char → CaptureMap → Nat →
      (CaptureMap → List Char → Nat → Option α) → Option α
  | 0, input, captures, itemCount, finish =>
      if repetitionCountOk lo hi itemCount then finish captures input itemCount else none
  | fuel + 1, input, captures, itemCount, finish =>
      let stop :=
        if repetitionCountOk lo hi itemCount then finish captures input itemCount else none
      scanOrElse stop fun _ =>
        if separator.isPrefixOf input then
          scanItem (input.drop separator.length) fun nextCaptures remaining =>
            scanStarK scanItem separator lo hi fuel remaining
              (captures ++ nextCaptures) (itemCount + 1) finish
        else
          none

mutual

/-- Lazily scan one symbol and pass each candidate, in reference order, to `continue`. -/
def scanSymK {α : Type} (g : Grammar) (qual : String) :
    Nat → Sym → List Char → (CaptureMap → List Char → Option α) → Option α
  | _, .lit literal, input, k =>
      let chars := literal.toList
      if chars.isPrefixOf input then k [] (input.drop chars.length) else none
  | _, .str, input, k =>
      (List.range (input.length + 1)).findSome? fun width =>
        if stringPrefixOk input width then k [] (input.drop width) else none
  | _, .term tok lengthSpec, input, k =>
      (List.range (input.length + 1)).findSome? fun width =>
        if termPrefixOk tok lengthSpec input width then
          k [] (input.drop width)
        else
          none
  | fuel, .rep separator item lo hi, input, k =>
      scanSymK g qual fuel item input fun firstCaptures remaining =>
        let base := item.refName?.getD qual
        scanStarK (scanSymK g qual fuel item) separator.toList lo hi input.length
          remaining firstCaptures 1 fun captures suffix itemCount =>
            k ((base ++ "#count", toString itemCount) :: captures) suffix
  | 0, .ref _, _, _ => none
  | fuel + 1, .ref name, input, k =>
      match g.prod? name with
      | none => none
      | some production =>
          scanProdK g name fuel production input fun captures remaining =>
            let consumed := String.ofList (input.take (input.length - remaining.length))
            let keys :=
              if qual.isEmpty then [(name, consumed)]
              else [(name, consumed), (qual ++ "." ++ name, consumed)]
            k (keys ++ captures) remaining

/-- Lazily scan a sequence, composing captures left-to-right. Optional symbols try their
    present path before their absent path, exactly as the reference decoder does. -/
def scanSeqK {α : Type} (g : Grammar) (qual : String) (fuel : Nat) :
    Seq → List Char → (CaptureMap → List Char → Option α) → Option α
  | [], input, k => k [] input
  | item :: rest, input, k =>
      let present :=
        scanSymK g qual fuel item.sym input fun headCaptures remaining =>
          scanSeqK g qual fuel rest remaining fun tailCaptures suffix =>
            k (headCaptures ++ tailCaptures) suffix
      if item.optional then
        scanOrElse present fun _ => scanSeqK g qual fuel rest input k
      else
        present

/-- Lazily scan alternatives in source order. -/
def scanProdK {α : Type} (g : Grammar) (qual : String) (fuel : Nat) :
    Production → List Char → (CaptureMap → List Char → Option α) → Option α
  | production, input, k =>
      production.alts.findSome? fun alternative =>
        scanSeqK g qual fuel alternative input k

end

/-- Complete ordered scanner. It stops as soon as the first full parse is found. -/
def scanSearch (g : Grammar) (input : String) : Option CaptureMap :=
  match g.startProd? with
  | none => none
  | some production =>
      scanProdK g "" g.prods.length production input.toList fun captures remaining =>
        if remaining.isEmpty then some captures else none

/-- Runtime scanner used by generated parsers. A certified deterministic grammar first uses the
    boundary-driven specialization; every other request uses the complete continuation scanner.
    Both paths are proved equal to the archived reference decoder. -/
def scan (g : Grammar) (input : String) : Option CaptureMap :=
  if g.staticUnique then
    (fastScan g input).orElse fun _ => scanSearch g input
  else
    scanSearch g input

/-- Compatibility name for code generated before the scanner became the sole runtime engine. -/
abbrev executeDecode := scan

/-! ## Proof-only performance model -/

/-- Result and completed-candidate count for the scanner's root continuation.

This profile is proof and diagnostic data, not the runtime implementation. One candidate check
means that a complete root-production candidate reached the final continuation and was tested
for an empty suffix. Internal branches that fail before reaching the root continuation are
accounted for by the candidate tree from which the budget is computed. -/
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

/-- Proof-only profile corresponding to `scanSearch`. It deliberately uses the archived
    candidate semantics so its bound is transparent and independently inspectable. -/
def scanSearchProfile (g : Grammar) (input : String) : ScanSearchProfile :=
  match g.startProd? with
  | none => ⟨none, 0⟩
  | some production =>
      profileCompleteCandidates
        (matchProd g "" g.prods.length production input.toList)

/-- Number of complete root candidates available to the ordered scanner search. This may be
    exponential for an ambiguous grammar; exposing that fact is part of the guarantee. -/
def scannerCandidateBudget (g : Grammar) (input : String) : Nat :=
  match g.startProd? with
  | none => 0
  | some production =>
      (matchProd g "" g.prods.length production input.toList).length

/-- Completed-candidate checks performed by the public scanner's search phase. A successful
    certified fast path performs no complete-candidate backtracking. -/
def scannerCandidateChecks (g : Grammar) (input : String) : Nat :=
  if g.staticUnique then
    match fastScan g input with
    | some _ => 0
    | none => (scanSearchProfile g input).candidateChecks
  else
    (scanSearchProfile g input).candidateChecks

/-- Scanner-backed counterpart of `computeValue`. -/
def scannerComputeValue (g : Grammar) (valueExpr : ValExpr) (input : String) : Option Int :=
  (scan g input).map fun captures => valueExpr.eval captures.toEnv

/-- Scanner-backed counterpart of `computeValueF`. -/
def scannerComputeValueF {α : Type} (g : Grammar) (valueFn : Env → α)
    (input : String) : Option α :=
  (scan g input).map fun captures => valueFn captures.toEnv

/-- Scanner-backed counterpart of `computeValueMap`. -/
def scannerComputeValueMap {α : Type} (g : Grammar) (valueFn : CaptureMap → α)
    (input : String) : Option α :=
  (scan g input).map valueFn

end Triptych
