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

import Triptych.Architecture.Unambiguity
import Triptych.Theorems.Coherence

/-!
# Soundness of the conservative static unambiguity check

`GrammarDecodeUnique.of_unaryUnique` turns the executable syntax check
`g.unaryUnique = true` into a kernel-checked, all-input uniqueness certificate.

The only subtle leaf is a variable-length token run. `matchSym` enumerates every matching
prefix, but a full parse must leave `[]`; among `k ∈ range (cs.length + 1)`, only
`k = cs.length` can do that. Unary references preserve remainders and list cardinality, so
the leaf result lifts through the complete reference path.
-/

namespace Triptych

/-- Keep only full-consumption matcher results. -/
private def fullMatches (xs : List (CaptureMap × List Char)) :=
  xs.filter (fun x => x.2.isEmpty)

private theorem fullMatches_lit (g : Grammar) (q : String) (fuel : Nat)
    (l : String) (cs : List Char) :
    (fullMatches (matchSym g q fuel (.lit l) cs)).length ≤ 1 := by
  unfold fullMatches
  simp only [matchSym]
  split
  · calc
      (List.filter (fun x : CaptureMap × List Char => x.2.isEmpty)
        [([], cs.drop l.toList.length)]).length ≤
          [([], cs.drop l.toList.length)].length := List.length_filter_le _ _
      _ = 1 := rfl
  · simp

private theorem fullMatches_term (g : Grammar) (q : String) (fuel : Nat)
    (tok : TokClass) (ls : LenSpec) (cs : List Char) :
    (fullMatches (matchSym g q fuel (.term tok ls) cs)).length ≤ 1 := by
  unfold fullMatches
  simp only [matchSym]
  rw [List.range_succ, List.filterMap_append, List.filter_append]
  have hprefix :
      List.filter (fun x : CaptureMap × List Char => x.2.isEmpty)
        (List.filterMap (fun k =>
          if termPrefixOk tok ls cs k then some ([], cs.drop k) else none)
          (List.range cs.length)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    rw [List.mem_filterMap] at hx
    obtain ⟨k, hk, hval⟩ := hx
    rw [List.mem_range] at hk
    by_cases hok : termPrefixOk tok ls cs k = true
    · rw [hok] at hval
      simp only [if_true, Option.some.injEq] at hval
      subst x
      intro hempty
      change (cs.drop k).isEmpty = true at hempty
      rw [List.isEmpty_iff] at hempty
      have hlen := congrArg List.length hempty
      rw [List.length_drop] at hlen
      simp at hlen
      omega
    · rw [Bool.not_eq_true] at hok
      rw [hok] at hval
      simp at hval
  rw [hprefix]
  simp only [List.nil_append]
  calc
    (List.filter (fun x : CaptureMap × List Char => x.2.isEmpty)
      (List.filterMap (fun k =>
        if termPrefixOk tok ls cs k then some ([], cs.drop k) else none)
        [cs.length])).length ≤
      (List.filterMap (fun k =>
        if termPrefixOk tok ls cs k then some ([], cs.drop k) else none)
        [cs.length]).length := List.length_filter_le _ _
    _ ≤ [cs.length].length := List.length_filterMap_le _ _
    _ = 1 := rfl

private theorem fullMatches_ref (g : Grammar) (q name prodName : String)
    (fuel : Nat) (item : SymItem) (hopt : item.optional = false)
    (hprod : g.prod? name = some (Production.mk prodName [[item]]))
    (cs : List Char)
    (hinner : (fullMatches (matchSym g name fuel item.sym cs)).length ≤ 1) :
    (fullMatches (matchSym g q (fuel + 1) (.ref name) cs)).length ≤ 1 := by
  unfold fullMatches at hinner ⊢
  simp only [matchSym, hprod, matchProd, matchSeq, hopt, Bool.false_eq_true, if_false,
    List.flatMap_singleton, List.map_singleton, List.append_nil]
  simpa [List.filter_map, Function.comp_def] using hinner

private theorem unaryUniqueFrom_fullMatches (g : Grammar) :
    ∀ fuel sym, g.unaryUniqueFrom fuel sym = true → ∀ q cs,
      (fullMatches (matchSym g q fuel sym cs)).length ≤ 1 := by
  intro fuel
  induction fuel with
  | zero =>
      intro sym h q cs
      cases sym with
      | lit l => exact fullMatches_lit g q 0 l cs
      | term tok ls => exact fullMatches_term g q 0 tok ls cs
      | ref name => simp [Grammar.unaryUniqueFrom] at h
      | rep sep item lo hi => simp [Grammar.unaryUniqueFrom] at h
  | succ fuel ih =>
      intro sym h q cs
      cases sym with
      | lit l => exact fullMatches_lit g q (fuel + 1) l cs
      | term tok ls => exact fullMatches_term g q (fuel + 1) tok ls cs
      | rep sep item lo hi => simp [Grammar.unaryUniqueFrom] at h
      | ref name =>
          cases hp : g.prod? name with
          | none => simp [Grammar.unaryUniqueFrom, hp] at h
          | some p =>
              rcases p with ⟨prodName, alts⟩
              cases alts with
              | nil => simp [Grammar.unaryUniqueFrom, hp] at h
              | cons alt moreAlts =>
                  cases moreAlts with
                  | cons alt' more => simp [Grammar.unaryUniqueFrom, hp] at h
                  | nil =>
                      cases alt with
                      | nil => simp [Grammar.unaryUniqueFrom, hp] at h
                      | cons item rest =>
                          cases rest with
                          | cons item' rest' => simp [Grammar.unaryUniqueFrom, hp] at h
                          | nil =>
                              rcases item with ⟨inner, optional⟩
                              cases optional with
                              | true => simp [Grammar.unaryUniqueFrom, hp] at h
                              | false =>
                                  simp [Grammar.unaryUniqueFrom, hp] at h
                                  apply fullMatches_ref g q name prodName fuel
                                    { sym := inner, optional := false } rfl hp cs
                                  exact ih inner h name cs

private theorem decodeUnique_of_start_unary (g : Grammar) (prodName : String)
    (item : SymItem) (hopt : item.optional = false)
    (hstart : g.startProd? = some (Production.mk prodName [[item]]))
    (s : String)
    (hinner : (fullMatches
      (matchSym g "" g.prods.length item.sym s.toList)).length ≤ 1) :
    DecodeUnique g s := by
  unfold DecodeUnique fullParses
  rw [hstart]
  unfold fullMatches at hinner
  simp only [matchProd, matchSeq, hopt, Bool.false_eq_true, if_false,
    List.flatMap_singleton, List.map_singleton, List.append_nil]
  simpa [List.filter_map, Function.comp_def] using hinner

/-- A successful unary-path check is a grammar-wide, all-input uniqueness certificate. -/
theorem GrammarDecodeUnique.of_unaryUnique (g : Grammar)
    (h : g.unaryUnique = true) : GrammarDecodeUnique g := by
  intro s
  unfold Grammar.unaryUnique at h
  cases hstart : g.startProd? with
  | none => simp [DecodeUnique, fullParses, hstart]
  | some p =>
      rcases p with ⟨prodName, alts⟩
      cases alts with
      | nil => simp [hstart] at h
      | cons alt moreAlts =>
          cases moreAlts with
          | cons alt' more => simp [hstart] at h
          | nil =>
              cases alt with
              | nil => simp [hstart] at h
              | cons item rest =>
                  cases rest with
                  | cons item' rest' => simp [hstart] at h
                  | nil =>
                      rcases item with ⟨inner, optional⟩
                      cases optional with
                      | true => simp [hstart] at h
                      | false =>
                          simp [hstart] at h
                          apply decodeUnique_of_start_unary g prodName
                            { sym := inner, optional := false } rfl hstart s
                          exact unaryUniqueFrom_fullMatches g g.prods.length inner h "" s.toList

end Triptych
