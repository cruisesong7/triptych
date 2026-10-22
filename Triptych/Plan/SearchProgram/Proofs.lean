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

import Triptych.Plan.SearchProgram
import Triptych.Reference.Unambiguity.Proofs

/-!
# Search-program staging correctness

Lowering a resolved `SearchPlan` into continuation-fused `SearchCode` preserves the complete
ordered search, including the exact selected capture map.
-/

namespace Triptych

namespace SearchCode

private theorem findSome?_eq_none_of {xs : List α} {f : α → Option β}
    (hnone : ∀ x ∈ xs, f x = none) :
    xs.findSome? f = none := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      rw [List.findSome?_cons, hnone head (by simp)]
      exact ih fun x hx => hnone x (by simp [hx])

private theorem findSome?_bind_of_unique (xs : List α) (accepts : α → Bool)
    (candidate : α → Option β) (finish : β → Option γ)
    (hnodup : xs.Nodup)
    (hunique : ∀ a ∈ xs, ∀ b ∈ xs,
      accepts a = true → accepts b = true → a = b) :
    xs.findSome? (fun x =>
        if accepts x then (candidate x).bind finish else none) =
      (xs.findSome? fun x =>
        if accepts x then candidate x else none).bind finish := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      rw [List.nodup_cons] at hnodup
      cases haccepts : accepts head with
      | false =>
          simp only [List.findSome?_cons, haccepts, Bool.false_eq_true, ite_false]
          apply ih hnodup.2
          intro a ha b hb haa hab
          exact hunique a (by simp [ha]) b (by simp [hb]) haa hab
      | true =>
          have htail : ∀ x ∈ tail, accepts x = false := by
            intro x hx
            cases hxAccepts : accepts x with
            | false => rfl
            | true =>
                have heq :=
                  hunique head (by simp) x (by simp [hx]) haccepts hxAccepts
                subst x
                exact (hnodup.1 hx).elim
          have hleft :
              tail.findSome? (fun x =>
                if accepts x then (candidate x).bind finish else none) = none :=
            findSome?_eq_none_of fun x hx => by simp [htail x hx]
          have hright :
              tail.findSome? (fun x =>
                if accepts x then candidate x else none) = none :=
            findSome?_eq_none_of fun x hx => by simp [htail x hx]
          simp only [List.findSome?_cons, haccepts, ↓reduceIte, hleft, hright]
          cases hcandidate : candidate head with
          | none => rfl
          | some resultValue =>
              cases hfinish : finish resultValue <;>
                simp [Option.bind, hfinish]

/-- A committed search prefix selects its capture candidate independently of the continuation. -/
theorem runK_committed (code : SearchCode) (hcommitted : code.committed = true) {α : Type}
    (input : List Char) (k : CaptureMap → List Char → Option α) :
    runK code input k =
      (runK code input fun captures remaining => some (captures, remaining)).bind
        fun result => k result.1 result.2 := by
  induction code generalizing α input k with
  | accept =>
      simp [runK]
  | fail =>
      simp [runK]
  | literal text next ih =>
      simp only [committed] at hcommitted
      simp only [runK]
      split
      · exact ih hcommitted _ _
      · rfl
  | stringLiteral =>
      simp [committed] at hcommitted
  | tokenRun token length next ih =>
      cases length with
      | atLeastOne =>
          simp [committed, fixedWidth] at hcommitted
      | exactly width =>
          simp only [committed, fixedWidth, Bool.true_and] at hcommitted
          simp only [runK]
          let accepts := fun candidateWidth =>
            termPrefixOk token (.exactly width) input candidateWidth
          let candidate := fun candidateWidth =>
            runK next (input.drop candidateWidth)
              fun captures remaining => some (captures, remaining)
          let finish := fun result : CaptureMap × List Char =>
            k result.1 result.2
          have hpointwise :
              (fun candidateWidth =>
                if accepts candidateWidth then
                  runK next (input.drop candidateWidth) k
                else none) =
              (fun candidateWidth =>
                if accepts candidateWidth then
                  (candidate candidateWidth).bind finish
                else none) := by
            funext candidateWidth
            simp only [accepts, candidate, finish]
            split
            · exact ih hcommitted _ _
            · rfl
          rw [hpointwise]
          exact findSome?_bind_of_unique
            (List.range (input.length + 1)) accepts candidate finish
            List.nodup_range
            (by
              intro a ha b hb haa hab
              exact termPrefixOk_index_unique token (.exactly width) input rfl haa hab)
      | between lower upper =>
          simp only [committed, fixedWidth, Bool.and_eq_true] at hcommitted
          let accepts := fun candidateWidth =>
            termPrefixOk token (.between lower upper) input candidateWidth
          let candidate := fun candidateWidth =>
            runK next (input.drop candidateWidth)
              fun captures remaining => some (captures, remaining)
          let finish := fun result : CaptureMap × List Char =>
            k result.1 result.2
          simp only [runK]
          have hpointwise :
              (fun candidateWidth =>
                if accepts candidateWidth then
                  runK next (input.drop candidateWidth) k
                else none) =
              (fun candidateWidth =>
                if accepts candidateWidth then
                  (candidate candidateWidth).bind finish
                else none) := by
            funext candidateWidth
            simp only [accepts, candidate, finish]
            split
            · exact ih hcommitted.2 _ _
            · rfl
          rw [hpointwise]
          exact findSome?_bind_of_unique
            (List.range (input.length + 1)) accepts candidate finish
            List.nodup_range
            (by
              intro a ha b hb haa hab
              exact termPrefixOk_index_unique token (.between lower upper) input
                hcommitted.1 haa hab)
  | capture keys body next bodyIh nextIh =>
      simp only [committed, Bool.and_eq_true] at hcommitted
      simp only [runK]
      let bodyCandidate :=
        runK body input fun captures remaining => some (captures, remaining)
      have hleft :
          runK body input
              (fun bodyCaptures remaining =>
                runK next remaining fun tailCaptures suffix =>
                  k
                    (keys.map (·,
                        String.ofList
                          (input.take (input.length - remaining.length))) ++
                      bodyCaptures ++ tailCaptures)
                    suffix) =
            bodyCandidate.bind fun bodyResult =>
              runK next bodyResult.2 fun tailCaptures suffix =>
                k
                  (keys.map (·,
                      String.ofList
                        (input.take (input.length - bodyResult.2.length))) ++
                    bodyResult.1 ++ tailCaptures)
                  suffix := by
        exact bodyIh hcommitted.1 _ _
      have hright :
          runK body input
              (fun bodyCaptures remaining =>
                runK next remaining fun tailCaptures suffix =>
                  some
                    (keys.map (·,
                        String.ofList
                          (input.take (input.length - remaining.length))) ++
                      bodyCaptures ++ tailCaptures,
                    suffix)) =
            bodyCandidate.bind fun bodyResult =>
              runK next bodyResult.2 fun tailCaptures suffix =>
                some
                  (keys.map (·,
                      String.ofList
                        (input.take (input.length - bodyResult.2.length))) ++
                    bodyResult.1 ++ tailCaptures,
                  suffix) := by
        exact bodyIh hcommitted.1 _ _
      rw [hleft, hright]
      cases hbodyCandidate : bodyCandidate with
      | none => rfl
      | some bodyResult =>
          rcases bodyResult with ⟨bodyCaptures, remaining⟩
          simp only [Option.bind_some]
          let nextCandidate :=
            runK next remaining fun captures suffix => some (captures, suffix)
          have hnextLeft :
              runK next remaining
                  (fun tailCaptures suffix =>
                    k
                      (keys.map (·,
                          String.ofList
                            (input.take (input.length - remaining.length))) ++
                        bodyCaptures ++ tailCaptures)
                      suffix) =
                nextCandidate.bind fun nextResult =>
                  k
                    (keys.map (·,
                        String.ofList
                          (input.take (input.length - remaining.length))) ++
                      bodyCaptures ++ nextResult.1)
                    nextResult.2 :=
            nextIh hcommitted.2 _ _
          have hnextRight :
              runK next remaining
                  (fun tailCaptures suffix =>
                    some
                      (keys.map (·,
                          String.ofList
                            (input.take (input.length - remaining.length))) ++
                        bodyCaptures ++ tailCaptures,
                      suffix)) =
                nextCandidate.bind fun nextResult =>
                  some
                    (keys.map (·,
                        String.ofList
                          (input.take (input.length - remaining.length))) ++
                      bodyCaptures ++ nextResult.1,
                    nextResult.2) :=
            nextIh hcommitted.2 _ _
          rw [hnextLeft, hnextRight]
          cases nextCandidate <;> rfl
  | choice =>
      simp [committed] at hcommitted
  | repetition =>
      simp [committed] at hcommitted

private theorem runK_sharedCapture (keys : List String) (body firstNext secondNext merged : SearchCode)
    (hcommitted : body.committed = true)
    (hmerged : ∀ (input : List Char) (k : CaptureMap → List Char → Option α),
      runK merged input k = runK (.choice firstNext secondNext) input k)
    (input : List Char) (k : CaptureMap → List Char → Option α) :
    runK (.capture keys body merged) input k =
      runK (.choice (.capture keys body firstNext) (.capture keys body secondNext)) input k := by
  simp only [runK]
  let bodyCandidate :=
    runK body input fun captures remaining => some (captures, remaining)
  have hrun (next : SearchCode) :
      runK body input
          (fun bodyCaptures remaining =>
            runK next remaining fun tailCaptures suffix =>
              k
                (keys.map (·,
                    String.ofList (input.take (input.length - remaining.length))) ++
                  bodyCaptures ++ tailCaptures)
                suffix) =
        bodyCandidate.bind fun bodyResult =>
          runK next bodyResult.2 fun tailCaptures suffix =>
            k
              (keys.map (·,
                  String.ofList (input.take (input.length - bodyResult.2.length))) ++
                bodyResult.1 ++ tailCaptures)
              suffix := by
    exact runK_committed body hcommitted _ _
  rw [hrun merged, hrun firstNext, hrun secondNext]
  cases hbodyCandidate : bodyCandidate with
  | none => rfl
  | some bodyResult =>
      rcases bodyResult with ⟨bodyCaptures, remaining⟩
      simp only [Option.bind_some]
      simpa only [runK] using
        hmerged remaining fun tailCaptures suffix =>
          k
            (keys.map (·,
                String.ofList (input.take (input.length - remaining.length))) ++
              bodyCaptures ++ tailCaptures)
            suffix

/-- Factoring a shared fixed-width token run preserves source-ordered continuation search. -/
private theorem runK_sharedTokenRun (token : TokClass) (length : LenSpec)
    (firstNext secondNext merged : SearchCode)
    (hfixed : fixedWidth length = true)
    (hmerged : ∀ (input : List Char) (k : CaptureMap → List Char → Option α),
      runK merged input k = runK (.choice firstNext secondNext) input k)
    (input : List Char) (k : CaptureMap → List Char → Option α) :
    runK (.tokenRun token length merged) input k =
      runK
        (.choice
          (.tokenRun token length firstNext)
          (.tokenRun token length secondNext))
        input k := by
  let accepts := fun candidateWidth =>
    termPrefixOk token length input candidateWidth
  let selected :=
    (List.range (input.length + 1)).findSome? fun candidateWidth =>
      if accepts candidateWidth then some (input.drop candidateWidth) else none
  have hrun (next : SearchCode) :
      runK (.tokenRun token length next) input k =
        selected.bind fun remaining => runK next remaining k := by
    simpa only [runK, accepts, selected, Option.bind_some] using
      findSome?_bind_of_unique
        (List.range (input.length + 1))
        accepts
        (fun candidateWidth => some (input.drop candidateWidth))
        (fun remaining => runK next remaining k)
        List.nodup_range
        (by
          intro a ha b hb haa hab
          exact termPrefixOk_index_unique token length input hfixed haa hab)
  rw [show
    runK
        (.choice
          (.tokenRun token length firstNext)
          (.tokenRun token length secondNext))
        input k =
      scanOrElse
        (runK (.tokenRun token length firstNext) input k)
        (fun _ => runK (.tokenRun token length secondNext) input k) by
      simp only [runK]]
  rw [hrun merged, hrun firstNext, hrun secondNext]
  cases hselected : selected with
  | none =>
      simp [scanOrElse]
  | some remaining =>
      simp only [Option.bind_some]
      simpa only [runK] using hmerged remaining k

/-- Merging two search branches preserves their source-ordered continuation semantics. -/
theorem runK_merge (first second : SearchCode) (input : List Char)
    (k : CaptureMap → List Char → Option α) :
    runK (merge first second) input k =
      runK (.choice first second) input k := by
  induction first, second using merge.induct generalizing input k with
  | case1 second =>
      simp [merge, runK, scanOrElse]
  | case2 first hfirst =>
      cases first <;> simp_all [merge, runK, scanOrElse]
  | case3 firstNext text secondNext ih =>
      simp only [merge, ↓reduceIte, runK]
      by_cases hpref : text.toList.isPrefixOf input = true
      · simp only [hpref, ↓reduceIte]
        simpa only [runK] using ih (input.drop text.toList.length) k
      · simp only [hpref]
        rfl
  | case4 firstText firstNext secondText secondNext htext =>
      simp [merge, htext]
  | case5 firstToken firstLength firstNext secondToken secondLength secondNext hshared ih =>
      rcases hshared with ⟨rfl, rfl, hfixed⟩
      simp only [merge, hfixed, and_self, ↓reduceIte]
      exact runK_sharedTokenRun firstToken firstLength firstNext secondNext
        (merge firstNext secondNext) hfixed ih input k
  | case6 firstToken firstLength firstNext secondToken secondLength secondNext hshared =>
      simp [merge, hshared]
  | case7 firstKeys firstBody firstNext secondKeys secondBody secondNext hshared ih =>
      rcases hshared with ⟨rfl, rfl, hcommitted⟩
      simp only [merge, hcommitted, and_self, ↓reduceIte]
      exact runK_sharedCapture firstKeys firstBody firstNext secondNext
        (merge firstNext secondNext) hcommitted ih input k
  | case8 firstKeys firstBody firstNext secondKeys secondBody secondNext hshared =>
      simp [merge, hshared]
  | case9 first second hfirst hsecond hliteral htoken hcapture =>
      simp_all [merge]

/-- Prefix factoring never creates more staged control-flow nodes than the original choice
    tree. -/
theorem nodeCount_merge_le (first second : SearchCode) :
    (merge first second).nodeCount ≤
      (SearchCode.choice first second).nodeCount := by
  induction first, second using merge.induct with
  | case1 second =>
      simp [merge, nodeCount]
  | case2 first hfirst =>
      cases first <;> simp_all [merge, nodeCount] <;> omega
  | case3 firstNext text secondNext ih =>
      simp [merge, nodeCount]
      simp only [nodeCount] at ih
      omega
  | case4 firstText firstNext secondText secondNext htext =>
      simp [merge, htext, nodeCount]
  | case5 firstToken firstLength firstNext secondToken secondLength secondNext hshared ih =>
      rcases hshared with ⟨rfl, rfl, hfixed⟩
      simp [merge, hfixed, nodeCount]
      simp only [nodeCount] at ih
      omega
  | case6 firstToken firstLength firstNext secondToken secondLength secondNext hshared =>
      simp [merge, hshared, nodeCount]
  | case7 firstKeys firstBody firstNext secondKeys secondBody secondNext hshared ih =>
      rcases hshared with ⟨rfl, rfl, hcommitted⟩
      simp [merge, hcommitted, nodeCount]
      simp only [nodeCount] at ih
      omega
  | case8 firstKeys firstBody firstNext secondKeys secondBody secondNext hshared =>
      simp [merge, hshared, nodeCount]
  | case9 first second hfirst hsecond hliteral htoken hcapture =>
      simp_all [merge, nodeCount]

/-- The proof-preserving reduction cannot increase static staged-program size. -/
theorem nodeCount_reduce_le (code : SearchCode) :
    code.reduce.nodeCount ≤ code.nodeCount := by
  induction code with
  | accept | fail =>
      simp [SearchCode.reduce, nodeCount]
  | literal text next ih | stringLiteral next ih | tokenRun _ _ next ih =>
      simp [SearchCode.reduce, nodeCount, ih]
  | capture keys body next bodyIh nextIh =>
      simp [SearchCode.reduce, nodeCount]
      omega
  | choice first second firstIh secondIh =>
      simp only [SearchCode.reduce, nodeCount]
      calc
        (merge first.reduce second.reduce).nodeCount ≤
            (SearchCode.choice first.reduce second.reduce).nodeCount :=
          nodeCount_merge_le first.reduce second.reduce
        _ ≤ (SearchCode.choice first second).nodeCount := by
          simp only [nodeCount]
          omega
  | repetition separator item lower upper countKey next itemIh nextIh =>
      simp [SearchCode.reduce, nodeCount]
      omega

/-- Removing statically failing choice arms preserves every continuation result. -/
theorem runK_reduce (code : SearchCode) (input : List Char)
    (k : CaptureMap → List Char → Option α) :
    runK code.reduce input k = runK code input k := by
  induction code generalizing input k with
  | accept =>
      simp [SearchCode.reduce, runK]
  | fail =>
      simp [SearchCode.reduce, runK]
  | literal text next ih =>
      simp only [SearchCode.reduce, runK]
      split <;> simp [ih]
  | stringLiteral next ih =>
      simp only [SearchCode.reduce, runK]
      congr 1
      funext width
      split <;> simp [ih]
  | tokenRun token length next ih =>
      simp only [SearchCode.reduce, runK]
      congr 1
      funext width
      split <;> simp [ih]
  | capture keys body next bodyIh nextIh =>
      simp only [SearchCode.reduce, runK]
      rw [bodyIh]
      apply congrArg (fun continuation =>
        runK body input continuation)
      funext bodyCaptures remaining
      rw [nextIh]
  | choice first second firstIh secondIh =>
      simp only [SearchCode.reduce]
      rw [runK_merge]
      simp only [runK]
      rw [firstIh, secondIh]
  | repetition separator item lower upper countKey next itemIh nextIh =>
      simp only [SearchCode.reduce, runK]
      rw [itemIh]
      apply congrArg (fun continuation =>
        runK item input continuation)
      funext firstCaptures remaining
      have hfinish :
          (fun (captures : CaptureMap) (suffix : List Char) (itemCount : Nat) =>
            runK next.reduce suffix fun (tailCaptures : CaptureMap) finalSuffix =>
              k (((countKey ++ "#count", toString itemCount) :: captures) ++
                tailCaptures) finalSuffix) =
          (fun (captures : CaptureMap) (suffix : List Char) (itemCount : Nat) =>
            runK next suffix fun (tailCaptures : CaptureMap) finalSuffix =>
              k (((countKey ++ "#count", toString itemCount) :: captures) ++
                tailCaptures) finalSuffix) := by
        funext captures suffix itemCount
        rw [nextIh]
      rw [hfinish]
      apply congrArg (fun scanItem =>
        scanStarK scanItem separator.toList lower upper input.length
          remaining firstCaptures 1
          (fun (captures : CaptureMap) (suffix : List Char) (itemCount : Nat) =>
            runK next suffix fun (tailCaptures : CaptureMap) finalSuffix =>
              k (((countKey ++ "#count", toString itemCount) :: captures) ++
                tailCaptures) finalSuffix))
      funext itemInput itemK
      exact itemIh itemInput itemK

mutual

private theorem runK_compilesPattern {pattern : SearchPattern} {next code : SearchCode}
    (compiled : CompilesPattern pattern next code) (input : List Char)
    (k : CaptureMap → List Char → Option α) :
    runK code input k =
      SearchPattern.searchK pattern input fun headCaptures remaining =>
        runK next remaining fun tailCaptures suffix =>
          k (headCaptures ++ tailCaptures) suffix := by
  cases compiled with
  | literal =>
      simp [runK, SearchPattern.searchK]
  | stringLiteral =>
      simp [runK, SearchPattern.searchK]
  | tokenRun =>
      simp [runK, SearchPattern.searchK]
  | capture body =>
      simp only [runK, SearchPattern.searchK]
      rw [runK_compilesAlternatives body input]
      apply congrArg (fun continuation =>
        SearchPattern.searchAlternativesK _ input continuation)
      funext bodyCaptures remaining
      simp [runK, List.append_assoc]
  | repetition body =>
      simp only [runK, SearchPattern.searchK]
      rw [runK_compilesPattern body input]
      simp only [runK, List.append_nil]
      apply congrArg (fun continuation =>
        SearchPattern.searchK _ input continuation)
      funext firstCaptures remaining
      apply congrArg (fun scanItem =>
        scanStarK scanItem _ _ _ input.length
          remaining firstCaptures 1 _)
      funext itemInput itemK
      rw [runK_compilesPattern body itemInput]
      simp only [runK, List.append_nil]
  | optional body =>
      simp only [runK, SearchPattern.searchK]
      rw [runK_compilesPattern body input]
      unfold scanOrElse
      cases hpresent :
          SearchPattern.searchK _ input fun headCaptures remaining =>
            runK next remaining fun tailCaptures suffix =>
              k (headCaptures ++ tailCaptures) suffix <;>
        simp

private theorem runK_compilesSequence {patterns : List SearchPattern} {next code : SearchCode}
    (compiled : CompilesSequence patterns next code) (input : List Char)
    (k : CaptureMap → List Char → Option α) :
    runK code input k =
      SearchPattern.searchSequenceK patterns input fun headCaptures remaining =>
        runK next remaining fun tailCaptures suffix =>
          k (headCaptures ++ tailCaptures) suffix := by
  cases compiled with
  | empty =>
      simp [SearchPattern.searchSequenceK]
  | cons tail head =>
      simp only [SearchPattern.searchSequenceK]
      rw [runK_compilesPattern head input]
      apply congrArg (fun continuation =>
        SearchPattern.searchK _ input continuation)
      funext headCaptures remaining
      rw [runK_compilesSequence tail remaining
        (fun tailCaptures suffix => k (headCaptures ++ tailCaptures) suffix)]
      apply congrArg (fun continuation =>
        SearchPattern.searchSequenceK _ remaining continuation)
      funext restCaptures suffix
      simp [List.append_assoc]

private theorem runK_compilesAlternatives {alternatives : List (List SearchPattern)}
    {next code : SearchCode} (compiled : CompilesAlternatives alternatives next code)
    (input : List Char)
    (k : CaptureMap → List Char → Option α) :
    runK code input k =
      SearchPattern.searchAlternativesK alternatives input fun headCaptures remaining =>
        runK next remaining fun tailCaptures suffix =>
          k (headCaptures ++ tailCaptures) suffix := by
  cases compiled with
  | empty =>
      simp [runK, SearchPattern.searchAlternativesK]
  | cons head tail =>
      simp only [runK, SearchPattern.searchAlternativesK]
      rw [runK_compilesSequence head input]
      rw [runK_compilesAlternatives tail input]

end

end SearchCode

namespace SearchProgram

/-- Continuation fusion preserves the exact resolved-plan result. -/
theorem lowerSearchPlan_decode (plan : SearchPlan) (source : String) :
    (lowerSearchPlan plan).decode source = plan.decode source := by
  calc
    (lowerSearchPlan plan).decode source =
        (lowerSearchPlanRaw plan).decode source := by
      unfold decode lowerSearchPlan lowerSearchPlanRaw
      exact SearchCode.runK_reduce _ source.toList _
    _ = plan.decode source := by
      unfold decode SearchPlan.decode lowerSearchPlanRaw
      rw [SearchCode.runK_compilesAlternatives
        (SearchCode.compileAlternatives_correct plan.alternatives .accept) source.toList]
      apply congrArg (fun continuation =>
        SearchPattern.searchAlternativesK plan.alternatives source.toList continuation)
      funext captures remaining
      simp [SearchCode.runK]

end SearchProgram

end Triptych
