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

import Triptych.Architecture.Scanner
import Triptych.Theorems.Unambiguity

/-!
# Correctness of the executable scanner

The complete scanner is a continuation-fused implementation of the archived list decoder.
The fusion theorems below prove that scanning a symbol, sequence, or production is exactly
`List.findSome?` over the corresponding reference candidates. At the root, the continuation
accepts only an empty suffix, so `scanSearch` returns exactly `decode`'s first complete parse.

The boundary-driven specialization is separately proved sound. `Grammar.staticUnique` makes
every successful specialized result equal to the reference result. Consequently the public
`scan` function can use that fast path and otherwise continue with `scanSearch`, without ever
calling `decode` at runtime.
-/

namespace Triptych

/-! ## Generic list-search fusion -/

private theorem findSome?_flatMap {α β γ : Type} (xs : List α) (f : α → List β)
    (k : β → Option γ) :
    (xs.flatMap f).findSome? k = xs.findSome? (fun x => (f x).findSome? k) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.flatMap_cons, List.findSome?_append, ih, List.findSome?_cons]
      cases (f x).findSome? k <;> rfl

private theorem findSome?_filterMap {α β γ : Type} (xs : List α) (f : α → Option β)
    (k : β → Option γ) :
    (xs.filterMap f).findSome? k = xs.findSome? (fun x => (f x).bind k) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.findSome?_cons]
      cases h : f x with
      | none => simp [h, ih]
      | some y =>
          simp only [List.filterMap_cons, h]
          rw [List.findSome?_cons]
          cases hk : k y <;> simp [hk, ih]

/-- `scanStarK` fuses `matchStar` with its consumer while preserving stop-before-continue
    ordering and capture concatenation. -/
theorem scanStarK_eq_matchStar {α : Type}
    (scanItem : List Char → (CaptureMap → List Char → Option α) → Option α)
    (matchItem : List Char → List (CaptureMap × List Char))
    (hitem : ∀ input k, scanItem input k =
      (matchItem input).findSome? (fun result => k result.1 result.2))
    (separator : List Char) (lo : Nat) (hi : Option Nat) (fuel : Nat)
    (input : List Char) (prefixCaptures : CaptureMap) (startCount : Nat)
    (finish : CaptureMap → List Char → Nat → Option α) :
    scanStarK scanItem separator lo hi fuel input prefixCaptures startCount finish =
      (matchStar matchItem separator fuel input).findSome? fun result =>
        let total := startCount + result.2.2
        if repetitionCountOk lo hi total then
          finish (prefixCaptures ++ result.1) result.2.1 total
        else none := by
  induction fuel generalizing input prefixCaptures startCount with
  | zero => simp [scanStarK, matchStar]
  | succ fuel ih =>
      simp only [scanStarK, matchStar, List.findSome?_cons, Nat.add_zero, List.append_nil]
      cases hstop : (if repetitionCountOk lo hi startCount then
          finish prefixCaptures input startCount else none) with
      | some resultValue => simp [scanOrElse]
      | none =>
          simp only [scanOrElse, Option.orElse_none]
          split <;> rename_i hprefix
          · rw [hitem]
            rw [findSome?_flatMap]
            congr 1
            funext result
            obtain ⟨itemCaptures, remaining⟩ := result
            simp only
            rw [ih]
            rw [List.findSome?_map]
            congr 1
            funext tail
            obtain ⟨tailCaptures, suffix, additional⟩ := tail
            simp [Function.comp_apply, Nat.add_comm, Nat.add_left_comm, List.append_assoc]
          · simp

/-! ## Exact fusion with the reference matchers -/

mutual

/-- Scanning one symbol is ordered search over exactly the candidates from `matchSym`. -/
theorem scanSymK_eq_matchSym (g : Grammar) (qual : String) :
    ∀ {α : Type} fuel sym input (k : CaptureMap → List Char → Option α),
      scanSymK g qual fuel sym input k =
        (matchSym g qual fuel sym input).findSome? fun result => k result.1 result.2
  | _, _, .lit literal, input, k => by
      by_cases hprefix : literal.toList.isPrefixOf input = true <;>
        simp [scanSymK, matchSym, hprefix]
  | _, _, .str, input, k => by
      rw [scanSymK, matchSym, findSome?_filterMap]
      congr 1
      funext width
      by_cases h : stringPrefixOk input width = true <;> simp [h]
  | _, _, .term tok lengthSpec, input, k => by
      rw [scanSymK, matchSym, findSome?_filterMap]
      congr 1
      funext width
      by_cases h : termPrefixOk tok lengthSpec input width = true <;> simp [h]
  | _, fuel, .rep separator item lo hi, input, k => by
      simp only [scanSymK, matchSym, matchRep]
      rw [scanSymK_eq_matchSym]
      rw [findSome?_filterMap]
      rw [findSome?_flatMap]
      congr 1
      funext first
      obtain ⟨firstCaptures, remaining⟩ := first
      simp only
      rw [scanStarK_eq_matchStar
        (matchItem := fun itemInput => matchSym g qual fuel item itemInput)
        (hitem := fun itemInput itemK =>
          scanSymK_eq_matchSym g qual fuel item itemInput itemK)]
      rw [List.findSome?_map]
      congr 1
      funext tail
      obtain ⟨tailCaptures, suffix, additional⟩ := tail
      simp only [Function.comp_apply, Nat.add_comm]
      unfold repetitionCountOk
      cases hi with
      | none =>
          by_cases hbounds : lo ≤ additional + 1 <;> simp [hbounds]
      | some upper =>
          by_cases hbounds : lo ≤ additional + 1 ∧ additional + 1 ≤ upper <;>
            simp [hbounds]
  | _, 0, .ref _, _, _ => by simp [scanSymK, matchSym]
  | _, fuel + 1, .ref name, input, k => by
      simp only [scanSymK, matchSym]
      cases hproduction : g.prod? name with
      | none => simp
      | some production =>
          simp only
          rw [scanProdK_eq_matchProd]
          rw [List.findSome?_map]
          congr 1

/-- Scanning a sequence is ordered search over exactly the candidates from `matchSeq`. -/
theorem scanSeqK_eq_matchSeq (g : Grammar) (qual : String) (fuel : Nat) :
    ∀ {α : Type} seq input (k : CaptureMap → List Char → Option α),
      scanSeqK g qual fuel seq input k =
        (matchSeq g qual fuel seq input).findSome? fun result => k result.1 result.2
  | _, [], input, k => by simp [scanSeqK, matchSeq]
  | _, item :: rest, input, k => by
      simp only [scanSeqK, matchSeq]
      rw [scanSymK_eq_matchSym]
      have hpresent :
          (matchSym g qual fuel item.sym input).findSome? (fun head =>
            scanSeqK g qual fuel rest head.2 fun tailCaptures suffix =>
              k (head.1 ++ tailCaptures) suffix) =
            ((matchSym g qual fuel item.sym input).flatMap fun head =>
              (matchSeq g qual fuel rest head.2).map fun tail =>
                (head.1 ++ tail.1, tail.2)).findSome? fun result =>
                  k result.1 result.2 := by
        rw [findSome?_flatMap]
        congr 1
        funext head
        obtain ⟨headCaptures, remaining⟩ := head
        simp only
        rw [scanSeqK_eq_matchSeq]
        rw [List.findSome?_map]
        congr 1
      by_cases hoptional : item.optional = true
      · simp only [hoptional, if_true]
        rw [hpresent, scanSeqK_eq_matchSeq, List.findSome?_append]
        cases ((matchSym g qual fuel item.sym input).flatMap fun head =>
            (matchSeq g qual fuel rest head.2).map fun tail =>
              (head.1 ++ tail.1, tail.2)).findSome? fun result =>
                k result.1 result.2 <;> rfl
      · simp only [hoptional, Bool.false_eq_true, if_false]
        exact hpresent

/-- Scanning a production is ordered search over exactly the candidates from `matchProd`. -/
theorem scanProdK_eq_matchProd (g : Grammar) (qual : String) (fuel : Nat) :
    ∀ {α : Type} production input (k : CaptureMap → List Char → Option α),
      scanProdK g qual fuel production input k =
        (matchProd g qual fuel production input).findSome? fun result =>
          k result.1 result.2
  | _, production, input, k => by
      simp only [scanProdK, matchProd]
      rw [findSome?_flatMap]
      congr 1
      funext alternative
      exact scanSeqK_eq_matchSeq g qual fuel alternative input k

end

private theorem findSome?_complete_eq_head
    (candidates : List (CaptureMap × List Char)) :
    candidates.findSome? (fun result =>
        if result.2.isEmpty then some result.1 else none) =
      (candidates.filter fun result => result.2.isEmpty).head?.map (·.1) := by
  have hfilter :
      candidates.filterMap (fun result =>
          if result.2.isEmpty then some result.1 else none) =
        (candidates.filter fun result => result.2.isEmpty).map (·.1) := by
    induction candidates with
    | nil => rfl
    | cons result rest ih =>
        obtain ⟨captures, remaining⟩ := result
        cases remaining <;> simp_all
  rw [← List.head?_filterMap, hfilter, List.head?_map]

/-- The complete continuation scanner is exactly the archived reference decoder. -/
theorem scanSearch_eq_decode (g : Grammar) (input : String) :
    scanSearch g input = decode g input := by
  unfold scanSearch decode
  cases hstart : g.startProd? with
  | none => simp
  | some production =>
      simp only
      rw [scanProdK_eq_matchProd]
      exact findSome?_complete_eq_head
        (matchProd g "" g.prods.length production input.toList)

/-! ## Boundary-driven specialization -/

private theorem fastScanTokenLength_le (tok : TokClass) (lengthSpec : LenSpec)
    (input : List Char)
    (h : termPrefixOk tok lengthSpec input
      (fastScanTokenLength tok lengthSpec input) = true) :
    fastScanTokenLength tok lengthSpec input ≤ input.length := by
  unfold termPrefixOk at h
  rw [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

mutual

theorem fastScanSym_mem_matchSym (g : Grammar) (qual : String) :
    ∀ fuel boundary sym input captures remaining,
      fastScanSym g qual fuel boundary sym input = some (captures, remaining) →
        (captures, remaining) ∈ matchSym g qual fuel sym input
  | _, _, .lit literal, input, captures, remaining, h => by
      simp only [fastScanSym] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp_all [matchSym]
      · simp at h
  | _, _, .str, _, _, _, h => by simp [fastScanSym] at h
  | fuel, boundary, .term tok lengthSpec, input, captures, remaining, h => by
      simp only [fastScanSym] at h
      by_cases hprefix :
          termPrefixOk tok lengthSpec input
            (fastScanTokenLength tok lengthSpec input) = true
      · simp only [hprefix, if_true, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp only [matchSym, List.mem_filterMap]
        refine ⟨fastScanTokenLength tok lengthSpec input, ?_, ?_⟩
        · rw [List.mem_range]
          have := fastScanTokenLength_le tok lengthSpec input hprefix
          omega
        · simp [hprefix]
      · simp only [Bool.not_eq_true] at hprefix
        simp [hprefix] at h
  | _, _, .rep _ _ _ _, _, _, _, h => by simp [fastScanSym] at h
  | 0, _, .ref _, _, _, _, h => by simp [fastScanSym] at h
  | fuel + 1, boundary, .ref name, input, captures, remaining, h => by
      simp only [fastScanSym] at h
      split at h
      · simp at h
      · rename_i production hproduction
        rw [Option.map_eq_some_iff] at h
        obtain ⟨⟨innerCaptures, suffix⟩, hscan, heq⟩ := h
        dsimp only at heq
        simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        have hmem :=
          fastScanProd_mem_matchProd g name fuel boundary production input
            innerCaptures suffix hscan
        simp only [matchSym, hproduction, List.mem_map]
        exact ⟨(innerCaptures, suffix), hmem, rfl⟩

theorem fastScanSeq_mem_matchSeq (g : Grammar) (qual : String) (fuel : Nat) :
    ∀ boundary seq input captures remaining,
      fastScanSeq g qual fuel boundary seq input = some (captures, remaining) →
        (captures, remaining) ∈ matchSeq g qual fuel seq input
  | _, [], input, captures, remaining, h => by
      simp only [fastScanSeq, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp [matchSeq]
  | outerBoundary, { sym, optional } :: rest, input, captures, remaining, h => by
      let itemBoundary : ScanBoundary :=
        match scanBoundary? rest with
        | some boundary => boundary
        | none => if rest.isEmpty then outerBoundary else .unknown
      have present_mem :
          ∀ result,
            fastScanPresent (fastScanSym g qual fuel itemBoundary sym input)
                (fastScanSeq g qual fuel outerBoundary rest) = some result →
              result ∈
                (matchSym g qual fuel sym input).flatMap fun head =>
                  (matchSeq g qual fuel rest head.2).map fun tail =>
                    (head.1 ++ tail.1, tail.2) := by
        intro result hpresent
        simp only [fastScanPresent, Option.bind_eq_some_iff,
          Option.map_eq_some_iff] at hpresent
        obtain ⟨head, hhead, tail, htail, heq⟩ := hpresent
        rcases heq with rfl
        rw [List.mem_flatMap]
        refine ⟨head, fastScanSym_mem_matchSym g qual fuel itemBoundary sym input
          head.1 head.2 hhead, ?_⟩
        rw [List.mem_map]
        exact ⟨tail, fastScanSeq_mem_matchSeq g qual fuel outerBoundary rest head.2
          tail.1 tail.2 htail, rfl⟩
      by_cases hoptional : optional = true
      · simp only [matchSeq, hoptional, if_true]
        simp only [fastScanSeq, hoptional, if_true] at h
        change
          (fastScanPresent (fastScanSym g qual fuel itemBoundary sym input)
              (fastScanSeq g qual fuel outerBoundary rest)).orElse
              (fun _ => fastScanSeq g qual fuel outerBoundary rest input) =
            some (captures, remaining) at h
        cases hpresent :
            fastScanPresent (fastScanSym g qual fuel itemBoundary sym input)
              (fastScanSeq g qual fuel outerBoundary rest) with
        | none =>
            simp only [hpresent, Option.orElse_none] at h
            exact List.mem_append_right _
              (fastScanSeq_mem_matchSeq g qual fuel outerBoundary rest input
                captures remaining h)
        | some result =>
            simp only [hpresent, Option.orElse_some, Option.some.injEq] at h
            rcases h with rfl
            exact List.mem_append_left _ (present_mem _ hpresent)
      · rw [Bool.not_eq_true] at hoptional
        simp only [matchSeq, hoptional, Bool.false_eq_true, if_false] at ⊢
        apply present_mem
        unfold itemBoundary
        have h' := h
        simp only [fastScanSeq, hoptional, Bool.false_eq_true, if_false] at h'
        exact h'

theorem fastScanProd_mem_matchProd (g : Grammar) (qual : String) (fuel : Nat) :
    ∀ boundary production input captures remaining,
      fastScanProd g qual fuel boundary production input = some (captures, remaining) →
        (captures, remaining) ∈ matchProd g qual fuel production input
  | boundary, { name, alts }, input, captures, remaining, h => by
      unfold fastScanProd at h
      unfold matchProd
      induction alts with
      | nil => simp [fastScanAlternatives] at h
      | cons alternative rest ih =>
          simp only [fastScanAlternatives] at h
          cases hscan : fastScanSeq g qual fuel boundary alternative input with
          | none =>
              simp only [hscan] at h
              rw [List.flatMap_cons]
              exact List.mem_append_right _ (ih h)
          | some result =>
              obtain ⟨foundCaptures, foundRemaining⟩ := result
              simp only [hscan] at h
              by_cases haccepts : boundary.accepts foundRemaining = true
              · simp only [haccepts, if_true, Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl⟩
                rw [List.flatMap_cons]
                exact List.mem_append_left _
                  (fastScanSeq_mem_matchSeq g qual fuel boundary alternative input
                    foundCaptures foundRemaining hscan)
              · simp only [Bool.not_eq_true] at haccepts
                simp only [haccepts] at h
                rw [List.flatMap_cons]
                exact List.mem_append_right _ (ih h)

end

/-- Every successful specialized complete scan is one of the reference full parses. -/
theorem fastScan_mem_fullParses (g : Grammar) (input : String) {captures : CaptureMap}
    (hscan : fastScan g input = some captures) :
    captures ∈ fullParses g input := by
  unfold fastScan at hscan
  cases hstart : g.startProd? with
  | none => simp [hstart] at hscan
  | some production =>
      simp only [hstart] at hscan
      cases hprod :
          fastScanProd g "" g.prods.length .endOfInput production input.toList with
      | none => simp [hprod] at hscan
      | some result =>
          obtain ⟨foundCaptures, remaining⟩ := result
          cases remaining with
          | cons c cs => simp [hprod] at hscan
          | nil =>
              simp only [hprod, Option.some.injEq] at hscan
              subst foundCaptures
              unfold fullParses
              rw [hstart]
              rw [List.mem_map]
              refine ⟨(captures, []), ?_, rfl⟩
              rw [List.mem_filter]
              exact ⟨fastScanProd_mem_matchProd g "" g.prods.length .endOfInput production
                input.toList captures [] hprod, by simp⟩

/-- On a statically unique grammar, a successful specialized scan is the reference result. -/
theorem decode_eq_fastScan_of_staticUnique (g : Grammar) (input : String)
    (hunique : g.staticUnique = true) {captures : CaptureMap}
    (hscan : fastScan g input = some captures) :
    decode g input = some captures := by
  apply decode_eq_of_mem_fullParses
  · exact GrammarCaptureFunctional.of_unique g
      (GrammarDecodeUnique.of_staticUnique g hunique)
  · exact fastScan_mem_fullParses g input hscan

/-! ## Public scanner equivalence -/

/-- The generated runtime scanner is extensionally identical to the archived decoder. -/
@[simp] theorem scan_eq_decode (g : Grammar) (input : String) :
    scan g input = decode g input := by
  unfold scan
  by_cases hunique : g.staticUnique = true
  · simp only [hunique, if_true]
    cases hscan : fastScan g input with
    | none => simp [scanSearch_eq_decode]
    | some captures =>
        have hdecode := decode_eq_fastScan_of_staticUnique g input hunique hscan
        simp [hdecode]
  · rw [Bool.not_eq_true] at hunique
    simp [hunique, scanSearch_eq_decode]

/-- Compatibility theorem for generated files that still use the old executor name. -/
@[simp] theorem executeDecode_eq_decode (g : Grammar) (input : String) :
    executeDecode g input = decode g input :=
  scan_eq_decode g input

/-! ## Formal search-cost guarantees -/

private theorem profileCompleteCandidates_result_eq
    (candidates : List (CaptureMap × List Char)) :
    (profileCompleteCandidates candidates).result =
      candidates.findSome? (fun result =>
        if result.2.isEmpty then some result.1 else none) := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih =>
      obtain ⟨captures, remaining⟩ := candidate
      simp only [profileCompleteCandidates, List.findSome?_cons]
      split <;> simp_all

private theorem profileCompleteCandidates_checks_le_length
    (candidates : List (CaptureMap × List Char)) :
    (profileCompleteCandidates candidates).candidateChecks ≤ candidates.length := by
  induction candidates with
  | nil => simp [profileCompleteCandidates]
  | cons candidate rest ih =>
      obtain ⟨captures, remaining⟩ := candidate
      simp only [profileCompleteCandidates, List.length_cons]
      split <;> simp_all

/-- The proof-only search profile returns exactly the complete scanner's result. -/
@[simp] theorem scanSearchProfile_result (g : Grammar) (input : String) :
    (scanSearchProfile g input).result = scanSearch g input := by
  unfold scanSearchProfile scanSearch
  cases hstart : g.startProd? with
  | none => rfl
  | some production =>
      simp only
      rw [scanProdK_eq_matchProd]
      exact profileCompleteCandidates_result_eq
        (matchProd g "" g.prods.length production input.toList)

/-- For every grammar and input, the continuation scanner tests no more complete root
    candidates than exist in the archived candidate tree. This is a finite, executable upper
    bound; ambiguous choices may make the bound exponential in the input length. -/
theorem scanSearch_candidateChecks_le (g : Grammar) (input : String) :
    (scanSearchProfile g input).candidateChecks ≤ scannerCandidateBudget g input := by
  unfold scanSearchProfile scannerCandidateBudget
  cases hstart : g.startProd? with
  | none => simp
  | some production =>
      exact profileCompleteCandidates_checks_le_length
        (matchProd g "" g.prods.length production input.toList)

/-- The public scanner's completed-candidate search is bounded for every grammar and input. -/
theorem scannerCandidateChecks_le (g : Grammar) (input : String) :
    scannerCandidateChecks g input ≤ scannerCandidateBudget g input := by
  unfold scannerCandidateChecks
  split
  · split
    · simp
    · exact scanSearch_candidateChecks_le g input
  · exact scanSearch_candidateChecks_le g input

/-- A successful certified fast path performs no complete-candidate backtracking. -/
theorem scannerCandidateChecks_eq_zero_of_fastScan
    (g : Grammar) (input : String) (hunique : g.staticUnique = true)
    {captures : CaptureMap} (hscan : fastScan g input = some captures) :
    scannerCandidateChecks g input = 0 := by
  simp [scannerCandidateChecks, hunique, hscan]

@[simp] theorem scannerComputeValue_eq_computeValue
    (g : Grammar) (valueExpr : ValExpr) (input : String) :
    scannerComputeValue g valueExpr input = computeValue g valueExpr input := by
  simp [scannerComputeValue, computeValue]

@[simp] theorem scannerComputeValueF_eq_computeValueF {α : Type}
    (g : Grammar) (valueFn : Env → α) (input : String) :
    scannerComputeValueF g valueFn input = computeValueF g valueFn input := by
  simp [scannerComputeValueF, computeValueF]

@[simp] theorem scannerComputeValueMap_eq_computeValueMap {α : Type}
    (g : Grammar) (valueFn : CaptureMap → α) (input : String) :
    scannerComputeValueMap g valueFn input = computeValueMap g valueFn input := by
  simp [scannerComputeValueMap, computeValueMap]

/-- Scanner-backed decision procedure for the denotational grammar predicate. -/
@[reducible] def decIsWfScanner (g : Grammar) (hg : g.repOk = true) :
    DecidablePred (IsWf g) := fun input =>
  decidable_of_iff ((scan g input).isSome = true) (by
    rw [scan_eq_decode]
    exact decodeSome_iff_IsWf g hg input)

/-! ## Executable regression evidence -/

private def decimalScannerGrammar : Grammar where
  start := "Decimal"
  prods := [
    {
      name := "Decimal"
      alts := [[
        { sym := .ref "Sign" },
        { sym := .ref "Natural" },
        { sym := .lit "." },
        { sym := .ref "Fraction" }
      ]]
    },
    {
      name := "Sign"
      alts := [[{ sym := .lit "-", optional := true }]]
    },
    {
      name := "Natural"
      alts := [[{ sym := .term .digit .atLeastOne }]]
    },
    {
      name := "Fraction"
      alts := [[{ sym := .term .digit (.between 1 4) }]]
    }
  ]

private def scannerAlternativesGrammar : Grammar where
  start := "Root"
  prods := [{
    name := "Root"
    alts := [
      [{ sym := .lit "d" }, { sym := .term .digit .atLeastOne }],
      [{ sym := .lit "x" }, { sym := .term .hexDigit .atLeastOne }]
    ]
  }]

private def scannerRepetitionGrammar : Grammar where
  start := "Root"
  prods := [{
    name := "Root"
    alts := [[{ sym := .rep "," (.term .digit (.exactly 1)) 1 (some 3) }]]
  }]

private def scannerStringGrammar : Grammar where
  start := "Root"
  prods := [{
    name := "Root"
    alts := [[{ sym := .str }]]
  }]

private def scannerSharedPrefixGrammar : Grammar where
  start := "Root"
  prods := [
    {
      name := "Root"
      alts := [
        [{ sym := .ref "Date" }],
        [{ sym := .ref "Date" }, { sym := .lit "T" }, { sym := .ref "Time" }]
      ]
    },
    {
      name := "Date"
      alts := [[{ sym := .term .digit (.exactly 2) }]]
    },
    {
      name := "Time"
      alts := [[{ sym := .term .digit (.exactly 2) }]]
    }
  ]

private def scannerOptionalComponentsGrammar : Grammar where
  start := "Root"
  prods := [
    {
      name := "Root"
      alts := [[
        { sym := .ref "Days", optional := true },
        { sym := .ref "Hours", optional := true }
      ]]
    },
    {
      name := "Days"
      alts := [[{ sym := .term .digit .atLeastOne }, { sym := .lit "d" }]]
    },
    {
      name := "Hours"
      alts := [[{ sym := .term .digit .atLeastOne }, { sym := .lit "h" }]]
    }
  ]

#guard decimalScannerGrammar.staticUnique
#guard fastScan decimalScannerGrammar "-12.34" =
  some [("Sign", "-"), ("Natural", "12"), ("Fraction", "34")]
#guard scan decimalScannerGrammar "-12.34" = decode decimalScannerGrammar "-12.34"
#guard scan decimalScannerGrammar "12.x" = none
#guard scannerCandidateChecks decimalScannerGrammar "-12.34" = 0
#guard (scanSearchProfile decimalScannerGrammar "-12.34").result =
  scanSearch decimalScannerGrammar "-12.34"
#guard (scanSearchProfile decimalScannerGrammar "12.x").candidateChecks ≤
  scannerCandidateBudget decimalScannerGrammar "12.x"

#guard scannerAlternativesGrammar.staticUnique
#guard scan scannerAlternativesGrammar "d12" = some []
#guard scan scannerAlternativesGrammar "x2a" = some []

#guard scan scannerSharedPrefixGrammar "12" = some [("Date", "12")]
#guard scan scannerSharedPrefixGrammar "12T34" =
  some [("Date", "12"), ("Time", "34")]

#guard scan scannerOptionalComponentsGrammar "1d2h" =
  some [("Days", "1d"), ("Hours", "2h")]
#guard scan scannerOptionalComponentsGrammar "2h" = some [("Hours", "2h")]

#guard fastScan scannerRepetitionGrammar "1,2" = none
#guard scan scannerRepetitionGrammar "1,2" = some [("#count", "2")]
#guard scan scannerRepetitionGrammar "1,2,3,4" = none
#guard scannerCandidateChecks scannerRepetitionGrammar "1,2" ≤
  scannerCandidateBudget scannerRepetitionGrammar "1,2"

#guard fastScan scannerStringGrammar "\"text\"" = none
#guard scan scannerStringGrammar "\"text\"" = some []

end Triptych
