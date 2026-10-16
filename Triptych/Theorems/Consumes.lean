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

import Triptych.Architecture.Denote

/-!
# Soundness of the consumption check

`Sym.consumes g fuel sym = true` claims that every match of `sym` is a non-empty string. This is
what lets a repetition omit its separator: each iteration still consumes input, so the
input length bounds the number of iterations, exactly as a non-empty separator does.
-/

namespace Triptych

theorem append_ne_empty_left {a b : String} (h : a ≠ "") : a ++ b ≠ "" := by
  intro hab
  apply h
  have := congrArg String.toList hab
  simp only [String.toList_append, String.toList_empty, List.append_eq_nil_iff] at this
  exact String.toList_eq_nil_iff.mp this.1

theorem append_ne_empty_right {a b : String} (h : b ≠ "") : a ++ b ≠ "" := by
  intro hab
  apply h
  have := congrArg String.toList hab
  simp only [String.toList_append, String.toList_empty, List.append_eq_nil_iff] at this
  exact String.toList_eq_nil_iff.mp this.2

theorem intercalate_ne_empty {sep p : String} {rest : List String} (h : p ≠ "") :
    String.intercalate sep (p :: rest) ≠ "" := by
  intro hint
  apply h
  have := congrArg String.toList hint
  rw [String.toList_intercalate, String.toList_empty, List.map_cons] at this
  cases rest with
  | nil =>
      simp only [List.map_nil, List.intercalate_singleton] at this
      exact String.toList_eq_nil_iff.mp this
  | cons q qs =>
      rw [List.map_cons, List.intercalate_cons_cons, List.append_eq_nil_iff,
        List.append_eq_nil_iff] at this
      exact String.toList_eq_nil_iff.mp this.1.1

theorem LenSpec.positive_sat {length : LenSpec} {n : Nat} (hpos : length.positive = true)
    (hsat : length.sat n) : 1 ≤ n := by
  cases length with
  | exactly k =>
      simp only [LenSpec.positive, decide_eq_true_eq] at hpos
      simp only [LenSpec.sat] at hsat
      omega
  | between lo hi =>
      simp only [LenSpec.positive, decide_eq_true_eq] at hpos
      simp only [LenSpec.sat] at hsat
      omega
  | atLeastOne =>
      simpa [LenSpec.sat] using hsat

/-- `consumesWith` is sound once its verdict for references is sound. -/
theorem consumesWith_sound (g : Grammar) (refConsumes : String → Bool)
    (href : ∀ name fuel s, refConsumes name = true →
      matchesSym g fuel (.ref name) s → s ≠ "") :
    ∀ sym fuel s, Sym.consumes.consumesWith refConsumes sym = true →
      matchesSym g fuel sym s → s ≠ "" := by
  intro sym
  induction sym with
  | lit text =>
      intro fuel s hconsumes hmatch
      simp only [Sym.consumes.consumesWith, Bool.not_eq_true', String.isEmpty_eq_false_iff]
        at hconsumes
      simp only [matchesSym] at hmatch
      subst hmatch
      exact hconsumes
  | str =>
      intro _ _ hconsumes
      simp [Sym.consumes.consumesWith] at hconsumes
  | term token length =>
      intro fuel s hconsumes hmatch
      simp only [Sym.consumes.consumesWith] at hconsumes
      simp only [matchesSym, matchesTerm] at hmatch
      have hlength := LenSpec.positive_sat hconsumes hmatch.2
      intro hs
      subst hs
      simp at hlength
  | ref name =>
      intro fuel s hconsumes hmatch
      exact href name fuel s hconsumes hmatch
  | rep sep item lo hi ihitem =>
      intro fuel s hconsumes hmatch
      simp only [Sym.consumes.consumesWith, Bool.and_eq_true, decide_eq_true_eq] at hconsumes
      simp only [matchesSym] at hmatch
      obtain ⟨parts, hlo, _, hitems, hs⟩ := hmatch
      cases parts with
      | nil => simp at hlo; omega
      | cons first rest =>
          subst hs
          exact intercalate_ne_empty
            (ihitem fuel first hconsumes.2 (hitems first (by simp)))

/-- A sequence with a required consuming item matches only non-empty strings. -/
theorem matchesSeq_ne_empty (g : Grammar) (fuel consumeFuel : Nat)
    (hfuel : ∀ sym s, Sym.consumes g consumeFuel sym = true →
      matchesSym g fuel sym s → s ≠ "") :
    ∀ seq s, seq.any (fun item => !item.optional && Sym.consumes g consumeFuel item.sym) = true →
      matchesSeq g fuel seq s → s ≠ "" := by
  intro seq
  induction seq with
  | nil => intro _ hany; simp at hany
  | cons item rest ih =>
      intro s hany hmatch
      simp only [List.any_cons, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hany
      unfold matchesSeq at hmatch
      by_cases hoptional : item.optional = true
      · simp only [hoptional, ite_true] at hmatch
        have hrest : rest.any (fun item => !item.optional &&
            Sym.consumes g consumeFuel item.sym) = true := by
          rcases hany with ⟨hreq, _⟩ | hrest
          · rw [hoptional] at hreq; contradiction
          · exact hrest
        rcases hmatch with ⟨s1, s2, rfl, _, hs2⟩ | hs
        · exact append_ne_empty_right (ih s2 hrest hs2)
        · exact ih s hrest hs
      · simp only [Bool.not_eq_true] at hoptional
        simp only [hoptional, Bool.false_eq_true, ite_false] at hmatch
        obtain ⟨s1, s2, rfl, hs1, hs2⟩ := hmatch
        rcases hany with ⟨_, hconsumes⟩ | hrest
        · exact append_ne_empty_left (hfuel item.sym s1 hconsumes hs1)
        · exact append_ne_empty_right (ih s2 hrest hs2)

/-- **Consumption soundness.** A symbol judged consuming matches only non-empty strings, at every
    denotation fuel. -/
theorem consumes_sound (g : Grammar) :
    ∀ consumeFuel fuel sym s, Sym.consumes g consumeFuel sym = true →
      matchesSym g fuel sym s → s ≠ "" := by
  intro consumeFuel
  induction consumeFuel with
  | zero =>
      intro fuel sym s hconsumes hmatch
      exact consumesWith_sound g (fun _ => false) (by intro _ _ _ h; simp at h)
        sym fuel s hconsumes hmatch
  | succ consumeFuel ih =>
      intro fuel sym s hconsumes hmatch
      refine consumesWith_sound g _ ?_ sym fuel s hconsumes hmatch
      intro name fuel s hname hmatch
      cases fuel with
      | zero => simp [matchesSym] at hmatch
      | succ fuel =>
          simp only [matchesSym] at hmatch
          cases hprod : g.prod? name with
          | none => simp [hprod] at hmatch
          | some production =>
              simp only [hprod, matchesProd] at hmatch hname
              obtain ⟨alt, halt, hseq⟩ := hmatch
              rw [List.all_eq_true] at hname
              exact matchesSeq_ne_empty g fuel consumeFuel (ih fuel)
                alt s (hname alt halt) hseq

end Triptych
