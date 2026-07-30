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

module

public import Batteries.Data.String.Lemmas

@[expose] public section

/-!
# String decomposition lemmas for external-parser bridges

External parsers commonly split a rendered format at a delimiter. These lemmas package the
routine proof that splitting a nonempty list of delimiter-free components joined by that
delimiter recovers the original components. They are parser-independent and belong in the
Cedar-free Triptych core.
-/

namespace Triptych

/-- List-level engine behind `splitToList_intercalate`: splitting a nonempty intercalation at
    its separator recovers every separator-free component. -/
theorem List.splitOnP_intercalate (parts : List (List α)) (hne : parts ≠ [])
    (p : α → Bool) (sep : α) (hsep : p sep = true)
    (hparts : ∀ part ∈ parts, ∀ x ∈ part, p x = false) :
    List.splitOnP p ([sep].intercalate parts) = parts := by
  induction parts with
  | nil => exact (hne rfl).elim
  | cons part rest ih =>
      cases rest with
      | nil =>
          rw [List.intercalate_singleton]
          exact List.splitOnP_eq_singleton (hparts part (by simp))
      | cons next tail =>
          rw [List.intercalate_cons_cons, List.append_assoc, List.singleton_append,
            List.splitOnP_append_cons_of_forall_mem (hparts part (by simp)) sep hsep]
          congr 1
          apply ih
          · simp
          · intro item hitem x hx
            exact hparts item (by simp [hitem]) x hx

/-- Splitting a delimiter-free string produces one component. -/
theorem splitToList_noSep (s : String) (p : Char → Bool)
    (h : ∀ c ∈ s.toList, p c = false) :
    s.splitToList p = [s] := by
  rw [String.splitToList_of_valid, List.splitOnP_eq_singleton h]
  simp

/-- Splitting a nonempty delimiter-separated rendering recovers all original components,
    provided the delimiter satisfies `p` and no component character does. -/
theorem splitToList_intercalate (parts : List String) (hne : parts ≠ [])
    (p : Char → Bool) (sep : Char) (hsep : p sep = true)
    (hparts : ∀ part ∈ parts, ∀ c ∈ part.toList, p c = false) :
    (String.intercalate (String.singleton sep) parts).splitToList p = parts := by
  rw [String.splitToList_of_valid, String.toList_intercalate, String.toList_singleton]
  rw [List.splitOnP_intercalate (parts.map String.toList)]
  · simp
  · simpa using hne
  · exact hsep
  · intro chars hchars c hc
    rw [List.mem_map] at hchars
    obtain ⟨part, hpart, rfl⟩ := hchars
    exact hparts part hpart c hc

/-- Delimiter-separated rendering is injective on nonempty lists whose components do not
    contain the delimiter. -/
theorem intercalate_injective {left right : List String}
    (hleft : left ≠ []) (hright : right ≠ []) (sep : Char)
    (hleftParts :
      ∀ part ∈ left, ∀ c ∈ part.toList, decide (c = sep) = false)
    (hrightParts :
      ∀ part ∈ right, ∀ c ∈ part.toList, decide (c = sep) = false)
    (h :
      String.intercalate (String.singleton sep) left =
        String.intercalate (String.singleton sep) right) :
    left = right := by
  have hsplits := congrArg
    (fun s : String => s.splitToList (fun c => decide (c = sep))) h
  rw [splitToList_intercalate left hleft _ sep (by simp) hleftParts,
    splitToList_intercalate right hright _ sep (by simp) hrightParts] at hsplits
  exact hsplits

/-- Two-component specialization of `splitToList_intercalate`. -/
theorem splitToList_two (s₁ s₂ : String) (p : Char → Bool) (sep : Char)
    (hsep : p sep = true) (h₁ : ∀ c ∈ s₁.toList, p c = false)
    (h₂ : ∀ c ∈ s₂.toList, p c = false) :
    (s₁ ++ String.singleton sep ++ s₂).splitToList p = [s₁, s₂] := by
  have hr :
      String.intercalate (String.singleton sep) [s₁, s₂] =
        s₁ ++ String.singleton sep ++ s₂ := by
    rw [String.intercalate_cons_cons, String.intercalate_singleton]
  rw [← hr]
  apply splitToList_intercalate [s₁, s₂] (by simp) p sep hsep
  intro part hpart c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpart
  rcases hpart with rfl | rfl
  · exact h₁ c hc
  · exact h₂ c hc

/-- Four-component specialization of `splitToList_intercalate`. -/
theorem splitToList_four (s₁ s₂ s₃ s₄ : String) (p : Char → Bool) (sep : Char)
    (hsep : p sep = true) (h₁ : ∀ c ∈ s₁.toList, p c = false)
    (h₂ : ∀ c ∈ s₂.toList, p c = false) (h₃ : ∀ c ∈ s₃.toList, p c = false)
    (h₄ : ∀ c ∈ s₄.toList, p c = false) :
    (s₁ ++ String.singleton sep ++ s₂ ++ String.singleton sep ++ s₃ ++
        String.singleton sep ++ s₄).splitToList p = [s₁, s₂, s₃, s₄] := by
  have hr :
      String.intercalate (String.singleton sep) [s₁, s₂, s₃, s₄] =
        s₁ ++ String.singleton sep ++ s₂ ++ String.singleton sep ++ s₃ ++
          String.singleton sep ++ s₄ := by
    repeat rw [String.intercalate_cons_cons]
    rw [String.intercalate_singleton]
    simp only [String.append_assoc]
  rw [← hr]
  apply splitToList_intercalate [s₁, s₂, s₃, s₄] (by simp) p sep hsep
  intro part hpart c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpart
  rcases hpart with rfl | hpart
  · exact h₁ c hc
  · rcases hpart with rfl | hpart
    · exact h₂ c hc
    · rcases hpart with rfl | rfl
      · exact h₃ c hc
      · exact h₄ c hc

end Triptych
