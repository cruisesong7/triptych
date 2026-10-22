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

import Triptych.Architecture.SearchMachine
import Triptych.Theorems.ScanPlan
import Triptych.Theorems.SearchPlan
import Triptych.Theorems.SearchProgram

/-!
# Search-machine lowering correctness

Successful lowering to callback-free states preserves the exact selected capture map and
remainder. This is the proof boundary needed by direct Lean and Verus state-function emitters.
-/

namespace Triptych

namespace SearchMachineCode

private theorem findSome?_eq_selected {α β : Type} (xs : List α) (f : α → Option β)
    (selected : α) (hmem : selected ∈ xs)
    (hunique : ∀ x ∈ xs, (f x).isSome = true → x = selected) :
    xs.findSome? f = f selected := by
  cases hselected : f selected with
  | none =>
      apply List.findSome?_eq_none_iff.mpr
      intro x hx
      cases hxvalue : f x with
      | none => rfl
      | some result =>
          have heq := hunique x hx (by simp [hxvalue])
          subst x
          simp [hselected] at hxvalue
  | some selectedValue =>
      induction xs with
      | nil => simp at hmem
      | cons head tail ih =>
          rw [List.findSome?_cons]
          cases hhead : f head with
          | none =>
              simp only
              apply ih
              · simp only [List.mem_cons] at hmem
                rcases hmem with heq | htail
                · subst head
                  simp [hselected] at hhead
                · exact htail
              · intro x hx hsome
                exact hunique x (by simp [hx]) hsome
          | some headValue =>
              simp only
              have heq := hunique head (by simp) (by simp [hhead])
              subst head
              rw [hselected] at hhead
              injection hhead with heq
              subst headValue
              rfl

private theorem tokenWidth_le_variable (token : TokClass) (input : List Char) :
    (input.takeWhile fun character => decide (token.mem character)).length ≤ input.length := by
  induction input with
  | nil => simp
  | cons character tail ih =>
      by_cases hmem : token.mem character
      · simp [hmem, ih]
      · simp [hmem]

/-- The boundary analysis reports only characters that every successful execution must consume
    next. -/
theorem requiredHead?_sound {code : SearchMachineCode} {character : Char}
    (hrequired : code.requiredHead? = some character)
    (state : SearchMachine.State) (finish : SearchMachine.State → Option α)
    {result : α} (hrun : SearchMachine.runK code state finish = some result) :
    state.input.head? = some character := by
  induction code generalizing state result with
  | accept => simp [requiredHead?] at hrequired
  | fail => simp [requiredHead?] at hrequired
  | literal text next ih =>
      cases hcharacters : text.toList with
      | nil =>
          simp only [requiredHead?, hcharacters] at hrequired
          simp only [SearchMachine.runK, hcharacters, List.length_nil, List.drop_zero] at hrun
          exact ih hrequired state hrun
      | cons first rest =>
          simp only [requiredHead?, hcharacters, Option.some.injEq] at hrequired
          subst first
          simp only [SearchMachine.runK] at hrun
          split at hrun
          next hpref =>
            obtain ⟨suffix, hsuffix⟩ := List.isPrefixOf_iff_prefix.mp hpref
            calc
              state.input.head? = (text.toList ++ suffix).head? := by rw [hsuffix]
              _ = some character := by simp [hcharacters]
          next hnot =>
            simp at hrun
  | stringLiteral next ih =>
      simp [requiredHead?] at hrequired
  | tokenRun token length next ih =>
      simp [requiredHead?] at hrequired
  | greedyTokenRun token length next ih =>
      simp [requiredHead?] at hrequired
  | save next ih =>
      simp only [requiredHead?] at hrequired
      have hhead := ih hrequired
        { state with
          markers := { start := state.input, captureCount := state.captures.length } ::
            state.markers }
        (by simpa only [SearchMachine.runK] using hrun)
      exact hhead
  | capture keys next ih =>
      simp only [requiredHead?] at hrequired
      simp only [SearchMachine.runK] at hrun
      obtain ⟨closed, hclosed, hnext⟩ := Option.bind_eq_some_iff.mp hrun
      have hhead := ih hrequired closed hnext
      unfold SearchMachine.closeCapture at hclosed
      split at hclosed
      · simp at hclosed
      · injection hclosed with heq
        subst closed
        exact hhead
  | choice first second firstIH secondIH =>
      cases hfirst : first.requiredHead? with
      | none => simp [requiredHead?, hfirst] at hrequired
      | some firstCharacter =>
          cases hsecond : second.requiredHead? with
          | none => simp [requiredHead?, hfirst, hsecond] at hrequired
          | some secondCharacter =>
              by_cases hsame : firstCharacter = secondCharacter
              · subst secondCharacter
                simp [requiredHead?, hfirst, hsecond] at hrequired
                subst character
                simp only [SearchMachine.runK, scanOrElse] at hrun
                cases hfirstRun : SearchMachine.runK first state finish with
                | none =>
                    simp [hfirstRun] at hrun
                    exact secondIH hsecond state hrun
                | some firstResult =>
                    simp [hfirstRun] at hrun
                    subst result
                    exact firstIH hfirst state hfirstRun
              · simp [requiredHead?, hfirst, hsecond, hsame] at hrequired
  | repetition separator item lower upper countKey next itemIH nextIH =>
      simp [requiredHead?] at hrequired

private theorem tokenWidth_eq_of_requiredHead_success
    {token : TokClass} {length : LenSpec} {input : List Char} {width : Nat}
    {next : SearchMachineCode} {character : Char}
    (hrequired : next.requiredHead? = some character)
    (hnot : ¬token.mem character)
    (hprefix : termPrefixOk token length input width = true)
    (state : SearchMachine.State) (finish : SearchMachine.State → Option α)
    {result : α}
    (hrun :
      SearchMachine.runK next { state with input := input.drop width } finish =
        some result) :
    ScanPlan.tokenWidth token length input = width := by
  have hhead :
      (input.drop width).head? = some character := by
    simpa using requiredHead?_sound hrequired
      { state with input := input.drop width } finish hrun
  have hparts := Bool.and_eq_true_iff.mp hprefix
  have hbound : width ≤ input.length := of_decide_eq_true hparts.1
  have hmatches :
      matchesTerm token length (String.ofList (input.take width)) :=
    of_decide_eq_true hparts.2
  have hboundary :
      input.drop width = [] ∨
        ∃ boundary rest,
          input.drop width = boundary :: rest ∧ ¬token.mem boundary := by
    cases hsuffix : input.drop width with
    | nil => exact Or.inl rfl
    | cons boundary rest =>
        simp [hsuffix] at hhead
        subst boundary
        exact Or.inr ⟨character, rest, rfl, hnot⟩
  cases length with
  | «exactly» expected =>
      have hwidth :=
        tokenWidth_eq_of_append_boundary
          (pre := input.take width) (suffix := input.drop width)
          hmatches trivial
      rw [List.take_append_drop] at hwidth
      simpa [List.length_take, Nat.min_eq_left hbound] using hwidth
  | «between» lower upper =>
      have hwidth :=
        tokenWidth_eq_of_append_boundary
          (pre := input.take width) (suffix := input.drop width)
          hmatches hboundary
      rw [List.take_append_drop] at hwidth
      simpa [List.length_take, Nat.min_eq_left hbound] using hwidth
  | «atLeastOne» =>
      have hwidth :=
        tokenWidth_eq_of_append_boundary
          (pre := input.take width) (suffix := input.drop width)
          hmatches hboundary
      rw [List.take_append_drop] at hwidth
      simpa [List.length_take, Nat.min_eq_left hbound] using hwidth

private theorem scanStarStateK_congr
    (hscan : ∀ (state : SearchMachine.State)
        (finish : SearchMachine.State → Option α),
      firstScan state finish = secondScan state finish)
    (hfinish : ∀ state itemCount,
      firstFinish state itemCount = secondFinish state itemCount)
    (separator lower upper fuel state itemCount) :
    SearchMachine.scanStarStateK firstScan separator lower upper fuel state itemCount
        firstFinish =
      SearchMachine.scanStarStateK secondScan separator lower upper fuel state itemCount
        secondFinish := by
  induction fuel generalizing state itemCount with
  | zero =>
      simp [SearchMachine.scanStarStateK, hfinish]
  | succ fuel ih =>
      simp only [SearchMachine.scanStarStateK]
      rw [hfinish]
      apply congrArg (fun fallback =>
        scanOrElse
          (if repetitionCountOk lower upper itemCount then
            secondFinish state itemCount
          else
            none)
          fallback)
      funext _
      split
      · rw [hscan]
        apply congrArg
        funext nextState
        exact ih (itemCount := itemCount + 1) (state := nextState)
      · rfl

private theorem runK_fuse (code : SearchMachineCode) (state : SearchMachine.State)
    (finish : SearchMachine.State → Option α) :
    SearchMachine.runK code.fuse state finish =
      SearchMachine.runK code state finish := by
  induction code generalizing state finish with
  | accept => simp [SearchMachineCode.fuse, SearchMachine.runK]
  | fail => simp [SearchMachineCode.fuse, SearchMachine.runK]
  | literal text next ih =>
      simp only [SearchMachineCode.fuse, SearchMachine.runK]
      split <;> simp [ih]
  | stringLiteral next ih =>
      simp only [SearchMachineCode.fuse, SearchMachine.runK]
      apply congrArg (fun candidate =>
        (List.range (state.input.length + 1)).findSome? candidate)
      funext width
      split <;> simp [ih]
  | tokenRun token length next ih =>
      cases length with
      | «exactly» width =>
          simp only [SearchMachineCode.fuse, SearchMachine.runK]
          apply congrArg (fun candidate =>
            (List.range (state.input.length + 1)).findSome? candidate)
          funext candidateWidth
          split <;> simp [ih]
      | «between» lower upper =>
          let fusedNext := next.fuse
          have hnext :
              ∀ nextState,
                SearchMachine.runK fusedNext nextState finish =
                  SearchMachine.runK next nextState finish := by
            intro nextState
            exact ih nextState finish
          cases hrequired : fusedNext.requiredHead? with
          | none =>
              have hfuse :
                  (SearchMachineCode.tokenRun token (.between lower upper) next).fuse =
                    .tokenRun token (.between lower upper) fusedNext := by
                simp [SearchMachineCode.fuse, fusedNext, hrequired]
              rw [hfuse]
              simp only [SearchMachine.runK]
              apply congrArg (fun candidate =>
                (List.range (state.input.length + 1)).findSome? candidate)
              funext candidateWidth
              split <;> simp [hnext]
          | some character =>
              by_cases hmem : token.mem character
              · have hfuse :
                    (SearchMachineCode.tokenRun token (.between lower upper) next).fuse =
                      .tokenRun token (.between lower upper) fusedNext := by
                  simp [SearchMachineCode.fuse, fusedNext, hrequired, hmem]
                rw [hfuse]
                simp only [SearchMachine.runK]
                apply congrArg (fun candidate =>
                  (List.range (state.input.length + 1)).findSome? candidate)
                funext candidateWidth
                split <;> simp [hnext]
              · have hfuse :
                    (SearchMachineCode.tokenRun token (.between lower upper) next).fuse =
                      .greedyTokenRun token (.between lower upper) fusedNext := by
                  simp [SearchMachineCode.fuse, fusedNext, hrequired, hmem]
                rw [hfuse]
                simp only [SearchMachine.runK]
                let selected :=
                  ScanPlan.tokenWidth token (.between lower upper) state.input
                let candidate := fun candidateWidth =>
                  if termPrefixOk token (.between lower upper) state.input candidateWidth then
                    SearchMachine.runK fusedNext
                      { state with input := state.input.drop candidateWidth } finish
                  else
                    none
                have hselected :
                    selected ∈ List.range (state.input.length + 1) := by
                  rw [List.mem_range]
                  apply Nat.lt_succ_of_le
                  exact tokenWidth_le_variable token state.input
                have hunique :
                    ∀ candidateWidth ∈ List.range (state.input.length + 1),
                      (candidate candidateWidth).isSome = true →
                        candidateWidth = selected := by
                  intro candidateWidth _ hsome
                  simp only [candidate] at hsome
                  split at hsome
                  next hprefix =>
                    cases hrun :
                        SearchMachine.runK fusedNext
                          { state with input := state.input.drop candidateWidth } finish with
                    | none => simp [hrun] at hsome
                    | some result =>
                        have hwidth :=
                          tokenWidth_eq_of_requiredHead_success hrequired hmem hprefix
                            state finish hrun
                        exact hwidth.symm
                  next hprefix =>
                    simp at hsome
                have hfind :=
                  findSome?_eq_selected
                    (List.range (state.input.length + 1)) candidate selected
                    hselected hunique
                calc
                  (if
                      termPrefixOk token (.between lower upper) state.input selected
                    then
                      SearchMachine.runK fusedNext
                        { state with input := state.input.drop selected } finish
                    else
                      none) =
                      (List.range (state.input.length + 1)).findSome? candidate :=
                    hfind.symm
                  _ =
                      (List.range (state.input.length + 1)).findSome? fun candidateWidth =>
                        if
                            termPrefixOk token (.between lower upper) state.input
                              candidateWidth
                        then
                          SearchMachine.runK next
                            { state with input := state.input.drop candidateWidth } finish
                        else
                          none := by
                    apply congrArg (fun found =>
                      (List.range (state.input.length + 1)).findSome? found)
                    funext candidateWidth
                    simp only [candidate]
                    split <;> simp [hnext]
      | «atLeastOne» =>
          let fusedNext := next.fuse
          have hnext :
              ∀ nextState,
                SearchMachine.runK fusedNext nextState finish =
                  SearchMachine.runK next nextState finish := by
            intro nextState
            exact ih nextState finish
          cases hrequired : fusedNext.requiredHead? with
          | none =>
              have hfuse :
                  (SearchMachineCode.tokenRun token .atLeastOne next).fuse =
                    .tokenRun token .atLeastOne fusedNext := by
                simp [SearchMachineCode.fuse, fusedNext, hrequired]
              rw [hfuse]
              simp only [SearchMachine.runK]
              apply congrArg (fun candidate =>
                (List.range (state.input.length + 1)).findSome? candidate)
              funext candidateWidth
              split <;> simp [hnext]
          | some character =>
              by_cases hmem : token.mem character
              · have hfuse :
                    (SearchMachineCode.tokenRun token .atLeastOne next).fuse =
                      .tokenRun token .atLeastOne fusedNext := by
                  simp [SearchMachineCode.fuse, fusedNext, hrequired, hmem]
                rw [hfuse]
                simp only [SearchMachine.runK]
                apply congrArg (fun candidate =>
                  (List.range (state.input.length + 1)).findSome? candidate)
                funext candidateWidth
                split <;> simp [hnext]
              · have hfuse :
                    (SearchMachineCode.tokenRun token .atLeastOne next).fuse =
                      .greedyTokenRun token .atLeastOne fusedNext := by
                  simp [SearchMachineCode.fuse, fusedNext, hrequired, hmem]
                rw [hfuse]
                simp only [SearchMachine.runK]
                let selected :=
                  ScanPlan.tokenWidth token .atLeastOne state.input
                let candidate := fun candidateWidth =>
                  if termPrefixOk token .atLeastOne state.input candidateWidth then
                    SearchMachine.runK fusedNext
                      { state with input := state.input.drop candidateWidth } finish
                  else
                    none
                have hselected :
                    selected ∈ List.range (state.input.length + 1) := by
                  rw [List.mem_range]
                  apply Nat.lt_succ_of_le
                  exact tokenWidth_le_variable token state.input
                have hunique :
                    ∀ candidateWidth ∈ List.range (state.input.length + 1),
                      (candidate candidateWidth).isSome = true →
                        candidateWidth = selected := by
                  intro candidateWidth _ hsome
                  simp only [candidate] at hsome
                  split at hsome
                  next hprefix =>
                    cases hrun :
                        SearchMachine.runK fusedNext
                          { state with input := state.input.drop candidateWidth } finish with
                    | none => simp [hrun] at hsome
                    | some result =>
                        have hwidth :=
                          tokenWidth_eq_of_requiredHead_success hrequired hmem hprefix
                            state finish hrun
                        exact hwidth.symm
                  next hprefix =>
                    simp at hsome
                have hfind :=
                  findSome?_eq_selected
                    (List.range (state.input.length + 1)) candidate selected
                    hselected hunique
                calc
                  (if termPrefixOk token .atLeastOne state.input selected then
                      SearchMachine.runK fusedNext
                        { state with input := state.input.drop selected } finish
                    else
                      none) =
                      (List.range (state.input.length + 1)).findSome? candidate :=
                    hfind.symm
                  _ =
                      (List.range (state.input.length + 1)).findSome? fun candidateWidth =>
                        if termPrefixOk token .atLeastOne state.input candidateWidth then
                          SearchMachine.runK next
                            { state with input := state.input.drop candidateWidth } finish
                        else
                          none := by
                    apply congrArg (fun found =>
                      (List.range (state.input.length + 1)).findSome? found)
                    funext candidateWidth
                    simp only [candidate]
                    split <;> simp [hnext]
  | greedyTokenRun token length next ih =>
      simp only [SearchMachineCode.fuse, SearchMachine.runK]
      split <;> simp [ih (finish := finish)]
  | save next ih =>
      simp only [SearchMachineCode.fuse, SearchMachine.runK]
      exact ih _ finish
  | capture keys next ih =>
      simp only [SearchMachineCode.fuse, SearchMachine.runK]
      cases SearchMachine.closeCapture keys state <;> simp [ih (finish := finish)]
  | choice first second firstIH secondIH =>
      simp only [SearchMachineCode.fuse, SearchMachine.runK]
      rw [firstIH (finish := finish), secondIH (finish := finish)]
  | repetition separator item lower upper countKey next itemIH nextIH =>
      simp only [SearchMachineCode.fuse, SearchMachine.runK]
      rw [itemIH state]
      apply congrArg (fun continuation =>
        SearchMachine.runK item state continuation)
      funext firstState
      exact scanStarStateK_congr itemIH
        (fun repeatedState itemCount => nextIH
          (SearchMachine.insertCaptureAt state.captures.length
            (countKey ++ "#count", toString itemCount) repeatedState)
          finish)
        separator.toList lower upper state.input.length firstState 1

private theorem scanOrElse_none_right (result : Option α) :
    scanOrElse result (fun _ => none) = result := by
  cases result <;> rfl

private theorem scanOrElse_none_left (fallback : Unit → Option α) :
    scanOrElse none fallback = fallback () := rfl

private theorem runK_merge (first second : SearchMachineCode)
    (state : SearchMachine.State) (finish : SearchMachine.State → Option α) :
    SearchMachine.runK (first.merge second) state finish =
      scanOrElse
        (SearchMachine.runK first state finish)
        fun _ => SearchMachine.runK second state finish := by
  induction first generalizing second state with
  | accept =>
      cases second <;>
        simp [SearchMachineCode.merge, SearchMachine.runK, scanOrElse_none_right,
          ]
  | fail =>
      cases second <;>
        simp [SearchMachineCode.merge, SearchMachine.runK, scanOrElse_none_left]
  | literal firstText firstNext firstIH =>
      cases second with
      | fail =>
          simp [SearchMachineCode.merge, SearchMachine.runK, scanOrElse_none_right]
      | accept =>
          simp [SearchMachineCode.merge, SearchMachine.runK]
      | literal secondText secondNext =>
          by_cases htext : firstText = secondText
          · subst secondText
            by_cases hprefix : firstText.toList.isPrefixOf state.input = true
            · simp [SearchMachineCode.merge, SearchMachine.runK, hprefix,
                firstIH secondNext]
            · simp [SearchMachineCode.merge, SearchMachine.runK, hprefix,
                scanOrElse_none_left]
          · simp [SearchMachineCode.merge, htext, SearchMachine.runK]
      | stringLiteral
      | tokenRun
      | greedyTokenRun
      | save
      | capture
      | choice
      | repetition =>
          simp [SearchMachineCode.merge, SearchMachine.runK]
  | stringLiteral firstNext firstIH =>
      cases second with
      | fail =>
          simp [SearchMachineCode.merge, SearchMachine.runK, scanOrElse_none_right]
      | accept
      | literal
      | stringLiteral
      | tokenRun
      | greedyTokenRun
      | save
      | capture
      | choice
      | repetition =>
          simp [SearchMachineCode.merge, SearchMachine.runK]
  | tokenRun firstToken firstLength firstNext firstIH =>
      cases second with
      | fail =>
          simp [SearchMachineCode.merge, SearchMachine.runK, scanOrElse_none_right]
      | accept
      | literal
      | stringLiteral
      | tokenRun
      | greedyTokenRun
      | save
      | capture
      | choice
      | repetition =>
          simp [SearchMachineCode.merge, SearchMachine.runK]
  | greedyTokenRun firstToken firstLength firstNext firstIH =>
      cases second with
      | fail =>
          simp [SearchMachineCode.merge, SearchMachine.runK, scanOrElse_none_right]
      | greedyTokenRun secondToken secondLength secondNext =>
          by_cases htoken : firstToken = secondToken
          · subst secondToken
            by_cases hlength : firstLength = secondLength
            · subst secondLength
              by_cases hprefix :
                  termPrefixOk firstToken firstLength state.input
                      (ScanPlan.tokenWidth firstToken firstLength state.input) = true
              · simp [SearchMachineCode.merge, SearchMachine.runK, hprefix,
                  firstIH secondNext]
              · simp [SearchMachineCode.merge, SearchMachine.runK, hprefix,
                  scanOrElse_none_left]
            · simp [SearchMachineCode.merge, hlength, SearchMachine.runK]
          · simp [SearchMachineCode.merge, htoken, SearchMachine.runK]
      | accept
      | literal
      | stringLiteral
      | tokenRun
      | save
      | capture
      | choice
      | repetition =>
          simp [SearchMachineCode.merge, SearchMachine.runK]
  | save firstNext firstIH =>
      cases second with
      | fail =>
          simp [SearchMachineCode.merge, SearchMachine.runK, scanOrElse_none_right]
      | save secondNext =>
          simp only [SearchMachineCode.merge, SearchMachine.runK]
          exact firstIH secondNext _
      | accept
      | literal
      | stringLiteral
      | tokenRun
      | greedyTokenRun
      | capture
      | choice
      | repetition =>
          simp [SearchMachineCode.merge, SearchMachine.runK]
  | capture firstKeys firstNext firstIH =>
      cases second with
      | fail =>
          simp [SearchMachineCode.merge, SearchMachine.runK, scanOrElse_none_right]
      | capture secondKeys secondNext =>
          by_cases hkeys : firstKeys = secondKeys
          · subst secondKeys
            cases hclosed : SearchMachine.closeCapture firstKeys state with
            | none =>
                simp [SearchMachineCode.merge, SearchMachine.runK, hclosed,
                  scanOrElse_none_left]
            | some closed =>
                simpa [SearchMachineCode.merge, SearchMachine.runK, hclosed] using
                  firstIH secondNext closed
          · simp [SearchMachineCode.merge, hkeys, SearchMachine.runK]
      | accept
      | literal
      | stringLiteral
      | tokenRun
      | greedyTokenRun
      | save
      | choice
      | repetition =>
          simp [SearchMachineCode.merge, SearchMachine.runK]
  | choice firstLeft firstRight leftIH rightIH =>
      cases second with
      | fail =>
          simp [SearchMachineCode.merge, SearchMachine.runK, scanOrElse_none_right]
      | accept
      | literal
      | stringLiteral
      | tokenRun
      | greedyTokenRun
      | save
      | capture
      | choice
      | repetition =>
          simp [SearchMachineCode.merge, SearchMachine.runK]
  | repetition separator item lower upper countKey next itemIH nextIH =>
      cases second with
      | fail =>
          simp [SearchMachineCode.merge, SearchMachine.runK, scanOrElse_none_right]
      | accept
      | literal
      | stringLiteral
      | tokenRun
      | greedyTokenRun
      | save
      | capture
      | choice
      | repetition =>
          simp [SearchMachineCode.merge, SearchMachine.runK]

private theorem runK_reduce (code : SearchMachineCode) (state : SearchMachine.State)
    (finish : SearchMachine.State → Option α) :
    SearchMachine.runK code.reduce state finish =
      SearchMachine.runK code state finish := by
  induction code generalizing state finish with
  | accept => simp [SearchMachineCode.reduce]
  | fail => simp [SearchMachineCode.reduce]
  | literal text next ih =>
      simp only [SearchMachineCode.reduce, SearchMachine.runK]
      split <;> simp [ih]
  | stringLiteral next ih =>
      simp only [SearchMachineCode.reduce, SearchMachine.runK]
      apply congrArg (fun candidate =>
        (List.range (state.input.length + 1)).findSome? candidate)
      funext width
      split <;> simp [ih]
  | tokenRun token length next ih =>
      simp only [SearchMachineCode.reduce, SearchMachine.runK]
      apply congrArg (fun candidate =>
        (List.range (state.input.length + 1)).findSome? candidate)
      funext width
      split <;> simp [ih]
  | greedyTokenRun token length next ih =>
      simp only [SearchMachineCode.reduce, SearchMachine.runK]
      split <;> simp [ih]
  | save next ih =>
      simp only [SearchMachineCode.reduce, SearchMachine.runK]
      exact ih _ finish
  | capture keys next ih =>
      simp only [SearchMachineCode.reduce, SearchMachine.runK]
      cases SearchMachine.closeCapture keys state <;> simp [ih]
  | choice first second firstIH secondIH =>
      simp only [SearchMachineCode.reduce, SearchMachine.runK]
      rw [runK_merge, firstIH, secondIH]
  | repetition separator item lower upper countKey next itemIH nextIH =>
      simp only [SearchMachineCode.reduce, SearchMachine.runK]
      rw [itemIH state]
      apply congrArg (fun continuation =>
        SearchMachine.runK item state continuation)
      funext firstState
      exact scanStarStateK_congr itemIH
        (fun repeatedState itemCount => nextIH
          (SearchMachine.insertCaptureAt state.captures.length
            (countKey ++ "#count", toString itemCount) repeatedState)
          finish)
        separator.toList lower upper state.input.length firstState 1

private theorem scanStarStateK_eq_scanStarK
    (hitem : ∀ (state : SearchMachine.State)
        (finish : SearchMachine.State → Option α),
      SearchMachine.runK machineItem state finish =
        SearchCode.runK sourceItem state.input fun captures remaining =>
          finish
            { state with
              input := remaining
              captures := state.captures ++ captures })
    (separator : List Char) (lower upper itemCount fuel)
    (state : SearchMachine.State) (outerCaptures prefixCaptures : CaptureMap)
    (hcaptures : state.captures = outerCaptures ++ prefixCaptures)
    (finish : SearchMachine.State → Nat → Option α) :
    SearchMachine.scanStarStateK (SearchMachine.runK machineItem)
        separator lower upper fuel state itemCount finish =
      scanStarK (SearchCode.runK sourceItem) separator lower upper fuel
        state.input prefixCaptures itemCount fun captures suffix countValue =>
          finish
            { state with
              input := suffix
              captures := outerCaptures ++ captures }
            countValue := by
  induction fuel generalizing state prefixCaptures itemCount with
  | zero =>
      have hstate :
          { state with captures := outerCaptures ++ prefixCaptures } = state := by
        cases state
        simp_all
      simp [SearchMachine.scanStarStateK, scanStarK, hstate]
  | succ fuel ih =>
      simp only [SearchMachine.scanStarStateK, scanStarK]
      have hstate :
          { state with captures := outerCaptures ++ prefixCaptures } = state := by
        cases state
        simp_all
      rw [hstate]
      congr 1
      funext _
      split
      · rw [hitem]
        apply congrArg (fun continuation =>
          SearchCode.runK sourceItem _ continuation)
        funext itemCaptures remaining
        simp only
        rw [hcaptures]
        rw [ih (itemCount + 1)
          { state with
            input := remaining
            captures := (outerCaptures ++ prefixCaptures) ++ itemCaptures }
          (prefixCaptures ++ itemCaptures)]
        · simp only [List.append_assoc]
      · simp

/-- Executing lowered first-order states is the same as executing the source search with the
    supplied continuation. -/
theorem run_lowers (lowered : Lowers source continuation machine)
    (state : SearchMachine.State) (finish : SearchMachine.State → Option α) :
    SearchMachine.runK machine state finish =
      SearchCode.runK source state.input fun captures remaining =>
        SearchMachine.runK continuation
          { state with
            input := remaining
            captures := state.captures ++ captures }
          finish := by
  induction lowered generalizing state finish with
  | accept =>
      simp [SearchCode.runK]
  | fail =>
      simp [SearchMachine.runK, SearchCode.runK]
  | literal next ih =>
      simp only [SearchMachine.runK, SearchCode.runK]
      split <;> simp [ih]
  | stringLiteral next ih =>
      simp only [SearchMachine.runK, SearchCode.runK]
      congr 1
      funext width
      split <;> simp [ih]
  | tokenRun next ih =>
      simp only [SearchMachine.runK, SearchCode.runK]
      congr 1
      funext width
      split <;> simp [ih]
  | capture next body nextIh bodyIh =>
      simp only [SearchMachine.runK, SearchCode.runK]
      rw [bodyIh _ finish]
      apply congrArg (fun continuation =>
        SearchCode.runK _ state.input continuation)
      funext bodyCaptures remaining
      simp only [SearchMachine.runK, SearchMachine.closeCapture, Option.bind_some]
      rw [nextIh _ finish]
      apply congrArg (fun continuation =>
        SearchCode.runK _ remaining continuation)
      funext tailCaptures suffix
      simp [List.append_assoc]
  | choice first second firstIh secondIh =>
      simp only [SearchMachine.runK, SearchCode.runK]
      rw [firstIh _ finish, secondIh _ finish]
  | repetition item next itemIh nextIh =>
      simp only [SearchMachine.runK, SearchCode.runK]
      rw [itemIh]
      simp only [SearchMachine.runK]
      apply congrArg (fun continuation =>
        SearchCode.runK _ state.input continuation)
      funext firstCaptures remaining
      rw [scanStarStateK_eq_scanStarK
        (machineItem := _)
        (sourceItem := _)
        (fun itemState itemFinish => by
          simpa only [SearchMachine.runK] using itemIh itemState itemFinish)
        _ _ _ _ _ _
        state.captures firstCaptures
        (by rfl)]
      apply congrArg (fun continuation =>
        scanStarK _ _ _ _ _ remaining firstCaptures 1 continuation)
      funext captures suffix itemCount
      rw [nextIh]
      apply congrArg (fun continuation =>
        SearchCode.runK _ suffix continuation)
      funext tailCaptures finalSuffix
      simp [SearchMachine.insertCaptureAt, List.append_assoc]

/-- Total lowering produces structural lowering evidence. -/
theorem lowerSearchCode_lowers (source : SearchCode) (continuation : SearchMachineCode) :
    Lowers source continuation (lowerSearchCode source continuation) := by
  induction source generalizing continuation with
  | accept =>
      simpa [lowerSearchCode] using
        (Lowers.accept (continuation := continuation))
  | fail =>
      simpa [lowerSearchCode] using
        (Lowers.fail (continuation := continuation))
  | literal text next ih =>
      simpa [lowerSearchCode] using
        (Lowers.literal (text := text) (ih continuation))
  | stringLiteral next ih =>
      simpa [lowerSearchCode] using
        (Lowers.stringLiteral (ih continuation))
  | tokenRun token length next ih =>
      simpa [lowerSearchCode] using
        (Lowers.tokenRun (token := token) (length := length) (ih continuation))
  | capture keys body next bodyIh nextIh =>
      simpa [lowerSearchCode] using
        (Lowers.capture
          (keys := keys)
          (nextIh continuation)
          (bodyIh (.capture keys (lowerSearchCode next continuation))))
  | choice first second firstIh secondIh =>
      simpa [lowerSearchCode] using
        (Lowers.choice (firstIh continuation) (secondIh continuation))
  | repetition separator item lower upper countKey next itemIh nextIh =>
      simpa [lowerSearchCode] using
        (Lowers.repetition
          (separator := separator)
          (lower := lower)
          (upper := upper)
          (countKey := countKey)
          (itemIh .accept)
          (nextIh continuation))

end SearchMachineCode

namespace SearchMachine

/-- Every lowered callback-free machine returns exactly the source search result. -/
theorem lowerSearchProgram_decode (program : SearchProgram) (source : String) :
    (lowerSearchProgram program).decode source = program.decode source := by
  unfold lowerSearchProgram decode SearchProgram.decode
  rw [SearchMachineCode.runK_reduce]
  rw [SearchMachineCode.runK_fuse]
  rw [SearchMachineCode.run_lowers
    (SearchMachineCode.lowerSearchCode_lowers program.code .accept)]
  simp [SearchMachine.runK]

/-- Machine lowering preserves the complete scanner for every certified ordered-search plan. -/
theorem lowerSearchPlan_decode_eq_scan {plan : SearchPlan} {grammar : Grammar}
    (hmirror : SearchPlan.MirrorsGrammar plan grammar) (source : String) :
    (lowerSearchProgram (lowerSearchPlan plan)).decode source = scan grammar source := by
  calc
    (lowerSearchProgram (lowerSearchPlan plan)).decode source =
        (lowerSearchPlan plan).decode source :=
      lowerSearchProgram_decode _ source
    _ = plan.decode source :=
      SearchProgram.lowerSearchPlan_decode plan source
    _ = scanSearch grammar source :=
      SearchPlan.decode_eq_scanSearch hmirror source
    _ = Triptych.decode grammar source :=
      scanSearch_eq_decode grammar source
    _ = scan grammar source :=
      (scan_eq_decode grammar source).symm

end SearchMachine

end Triptych
