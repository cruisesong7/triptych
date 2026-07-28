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

`GrammarDecodeUnique.of_staticUnique` turns the executable syntax check
`g.staticUnique = true` into a kernel-checked, all-input uniqueness certificate. The checker
combines unary reference paths with required sequences whose intermediate symbols have unique
prefix matches.

The only subtle leaf is a variable-length token run. `matchSym` enumerates every matching
prefix, but a full parse must leave `[]`; among `k ∈ range (cs.length + 1)`, only
`k = cs.length` can do that. Unary references preserve remainders and list cardinality, so
the leaf result lifts through the complete reference path. In a sequence this weaker rule is
sound only at the tail; every earlier symbol uses the stronger prefix-uniqueness theorem.
The delimiter rule proves that two token prefixes cannot both be followed by a literal whose
first character is outside the token class. The optional-head rule then separates a consuming
`X ::= ["lit"]` parse from its empty parse by the first character of the unique remainder.
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

/-! ## Required deterministic sequences -/

private theorem length_filterMap_le_one_of_unique {α β : Type} {f : α → Option β}
    {xs : List α} (hnodup : xs.Nodup)
    (hunique : ∀ a ∈ xs, ∀ b ∈ xs, ∀ x y, f a = some x → f b = some y → a = b) :
    (xs.filterMap f).length ≤ 1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      rw [List.nodup_cons] at hnodup
      cases hfa : f a with
      | none =>
          simp only [List.filterMap_cons, hfa]
          apply ih hnodup.2
          intro b hb c hc x y hbx hcy
          exact hunique b (by simp [hb]) c (by simp [hc]) x y hbx hcy
      | some x =>
          have htail : xs.filterMap f = [] := by
            rw [List.filterMap_eq_nil_iff]
            intro b hb
            cases hfb : f b with
            | none => rfl
            | some y =>
                have hab := hunique a (by simp) b (by simp [hb]) x y hfa hfb
                subst b
                exact (hnodup.1 hb).elim
          simp [hfa, htail]

private theorem termPrefixOk_index_unique (tok : TokClass) (ls : LenSpec)
    (cs : List Char) (hls : (match ls with
      | .exactly _ => true
      | .between lo hi => lo == hi
      | .atLeastOne => false) = true)
    {k j : Nat} (hk : termPrefixOk tok ls cs k = true)
    (hj : termPrefixOk tok ls cs j = true) : k = j := by
  unfold termPrefixOk at hk hj
  rw [Bool.and_eq_true] at hk hj
  have hkbound := of_decide_eq_true hk.1
  have hjbound := of_decide_eq_true hj.1
  have hmk := of_decide_eq_true hk.2
  have hmj := of_decide_eq_true hj.2
  cases ls with
  | exactly n =>
      unfold matchesTerm LenSpec.sat at hmk hmj
      have hklen := hmk.2
      have hjlen := hmj.2
      simp only [String.length_ofList, List.length_take, Nat.min_eq_left hkbound] at hklen
      simp only [String.length_ofList, List.length_take, Nat.min_eq_left hjbound] at hjlen
      omega
  | between lo hi =>
      simp only at hls
      have hlohi : lo = hi := beq_iff_eq.mp hls
      subst hi
      unfold matchesTerm LenSpec.sat at hmk hmj
      have hklen := hmk.2
      have hjlen := hmj.2
      simp only [String.length_ofList, List.length_take, Nat.min_eq_left hkbound] at hklen
      simp only [String.length_ofList, List.length_take, Nat.min_eq_left hjbound] at hjlen
      omega
  | atLeastOne => simp at hls

private theorem prefixMatches_term (g : Grammar) (q : String) (fuel : Nat)
    (tok : TokClass) (ls : LenSpec) (cs : List Char)
    (hls : (match ls with
      | .exactly _ => true
      | .between lo hi => lo == hi
      | .atLeastOne => false) = true) :
    (matchSym g q fuel (.term tok ls) cs).length ≤ 1 := by
  simp only [matchSym]
  apply length_filterMap_le_one_of_unique List.nodup_range
  intro k hk j hj x y hx hy
  by_cases hkok : termPrefixOk tok ls cs k = true
  · rw [hkok] at hx
    simp only [if_true, Option.some.injEq] at hx
    by_cases hjok : termPrefixOk tok ls cs j = true
    · exact termPrefixOk_index_unique tok ls cs hls hkok hjok
    · rw [Bool.not_eq_true] at hjok
      rw [hjok] at hy
      simp at hy
  · rw [Bool.not_eq_true] at hkok
    rw [hkok] at hx
    simp at hx

private theorem length_flatMap_le_one {α β : Type} {xs : List α} {f : α → List β}
    (hxs : xs.length ≤ 1) (hf : ∀ x ∈ xs, (f x).length ≤ 1) :
    (xs.flatMap f).length ≤ 1 := by
  cases xs with
  | nil => simp
  | cons x xs =>
      cases xs with
      | nil => simpa using hf x (by simp)
      | cons y ys => simp at hxs

private theorem length_filterMap_flatMap_le_one_of_unique {α β γ : Type}
    {f : α → Option β} {h : β → List γ} {xs : List α} (hnodup : xs.Nodup)
    (hsingle : ∀ a ∈ xs, ∀ b, f a = some b → (h b).length ≤ 1)
    (hunique : ∀ a ∈ xs, ∀ b ∈ xs, ∀ x y u v,
      f a = some x → u ∈ h x → f b = some y → v ∈ h y → a = b) :
    ((xs.filterMap f).flatMap h).length ≤ 1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      rw [List.nodup_cons] at hnodup
      cases hfa : f a with
      | none =>
          simp only [List.filterMap_cons, hfa]
          apply ih hnodup.2
          · intro b hb y hby
            exact hsingle b (by simp [hb]) y hby
          · intro b hb c hc x y u v hbx hu hcy hv
            exact hunique b (by simp [hb]) c (by simp [hc]) x y u v hbx hu hcy hv
      | some x =>
          cases hx : h x with
          | nil =>
              simp only [List.filterMap_cons, hfa, List.flatMap_cons, hx, List.nil_append]
              apply ih hnodup.2
              · intro b hb y hby
                exact hsingle b (by simp [hb]) y hby
              · intro b hb c hc y z u v hby hu hbz hv
                exact hunique b (by simp [hb]) c (by simp [hc]) y z u v hby hu hbz hv
          | cons u us =>
              have hus : us = [] := by
                have hlen := hsingle a (by simp) x hfa
                rw [hx] at hlen
                cases us with
                | nil => rfl
                | cons v vs => simp at hlen
              subst us
              have htail : (xs.filterMap f).flatMap h = [] := by
                rw [List.flatMap_eq_nil_iff]
                intro y hy
                rw [List.mem_filterMap] at hy
                obtain ⟨b, hb, hfb⟩ := hy
                cases hhy : h y with
                | nil => rfl
                | cons v vs =>
                    have hab := hunique a (by simp) b (by simp [hb]) x y u v hfa
                      (by simp [hx]) hfb (by simp [hhy])
                    subst b
                    exact (hnodup.1 hb).elim
              simp [hfa, hx, htail]

private theorem tokenPrefix_eq_of_append_delimiter (tok : TokClass) (d : Char)
    (ds : List Char) (hnot : ¬tok.mem d) : ∀ p p' r r' : List Char,
      tok.all (String.ofList p) → tok.all (String.ofList p') →
      p ++ (d :: ds) ++ r = p' ++ (d :: ds) ++ r' → p = p' := by
  intro p
  induction p with
  | nil =>
      intro p' r r' hp hp' heq
      cases p' with
      | nil => rfl
      | cons x xs =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
          have hmem : tok.mem x := by
            apply hp'
            simp [String.toList_ofList]
          exact (hnot (heq.1 ▸ hmem)).elim
  | cons x xs ih =>
      intro p' r r' hp hp' heq
      cases p' with
      | nil =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
          have hmem : tok.mem x := by
            apply hp
            simp [String.toList_ofList]
          exact (hnot (heq.1.symm ▸ hmem)).elim
      | cons y ys =>
          simp only [List.cons_append, List.cons.injEq] at heq
          rcases heq with ⟨rfl, heq⟩
          exact congrArg (List.cons x) (ih ys r r'
            (by
              intro c hc
              apply hp c
              simpa [String.toList_ofList] using List.mem_cons_of_mem x hc)
            (by
              intro c hc
              apply hp' c
              simpa [String.toList_ofList] using List.mem_cons_of_mem x hc)
            heq)

private theorem termPrefixOk_index_unique_before_delimiter (tok : TokClass) (ls : LenSpec)
    (cs : List Char) (d : Char) (ds : List Char) (hnot : ¬tok.mem d)
    {k j : Nat} (hk : termPrefixOk tok ls cs k = true)
    (hj : termPrefixOk tok ls cs j = true)
    (hkd : (d :: ds).isPrefixOf (cs.drop k) = true)
    (hjd : (d :: ds).isPrefixOf (cs.drop j) = true) : k = j := by
  unfold termPrefixOk at hk hj
  rw [Bool.and_eq_true] at hk hj
  have hkbound := of_decide_eq_true hk.1
  have hjbound := of_decide_eq_true hj.1
  have hkmatches := of_decide_eq_true hk.2
  have hjmatches := of_decide_eq_true hj.2
  obtain ⟨kr, hkdrop⟩ := List.isPrefixOf_iff_prefix.mp hkd
  obtain ⟨jr, hjdrop⟩ := List.isPrefixOf_iff_prefix.mp hjd
  have hp : cs.take k = cs.take j := by
    apply tokenPrefix_eq_of_append_delimiter tok d ds hnot
      (cs.take k) (cs.take j) kr jr hkmatches.1 hjmatches.1
    calc
      cs.take k ++ (d :: ds) ++ kr = cs.take k ++ cs.drop k := by
        rw [List.append_assoc, hkdrop]
      _ = cs := List.take_append_drop k cs
      _ = cs.take j ++ cs.drop j := (List.take_append_drop j cs).symm
      _ = cs.take j ++ (d :: ds) ++ jr := by
        rw [List.append_assoc, hjdrop]
  have hlen := congrArg List.length hp
  simp only [List.length_take, Nat.min_eq_left hkbound, Nat.min_eq_left hjbound] at hlen
  exact hlen

private theorem termThenLiteral_matches (g : Grammar) (q : String) (fuel : Nat)
    (tok : TokClass) (ls : LenSpec) (d : Char) (ds cs : List Char) (hnot : ¬tok.mem d) :
    ((matchSym g q fuel (.term tok ls) cs).flatMap (fun x =>
      (matchSym g q fuel (.lit (String.ofList (d :: ds))) x.2).map
        (fun y => (x.1 ++ y.1, y.2)))).length ≤ 1 := by
  simp only [matchSym]
  apply length_filterMap_flatMap_le_one_of_unique List.nodup_range
  · intro k hk x hx
    split <;> simp
  · intro k hk j hj x y u v hx hu hy hv
    by_cases hkok : termPrefixOk tok ls cs k = true
    · rw [hkok] at hx
      simp only [if_true, Option.some.injEq] at hx
      subst x
      by_cases hjok : termPrefixOk tok ls cs j = true
      · rw [hjok] at hy
        simp only [if_true, Option.some.injEq] at hy
        subst y
        by_cases hkd : (d :: ds).isPrefixOf (cs.drop k) = true
        · by_cases hjd : (d :: ds).isPrefixOf (cs.drop j) = true
          · exact termPrefixOk_index_unique_before_delimiter
              tok ls cs d ds hnot hkok hjok hkd hjd
          · rw [Bool.not_eq_true] at hjd
            simp [hjd] at hv
        · rw [Bool.not_eq_true] at hkd
          simp [hkd] at hu
      · rw [Bool.not_eq_true] at hjok
        rw [hjok] at hy
        simp at hy
    · rw [Bool.not_eq_true] at hkok
      rw [hkok] at hx
      simp at hx

private theorem delimiterUniqueFrom_matches (g : Grammar) :
    ∀ fuel sym delimiter, g.delimiterUniqueFrom fuel sym delimiter = true → ∀ q cs,
      ((matchSym g q fuel sym cs).flatMap (fun x =>
        (matchSym g q fuel (.lit delimiter) x.2).map
          (fun y => (x.1 ++ y.1, y.2)))).length ≤ 1 := by
  intro fuel
  induction fuel with
  | zero =>
      intro sym delimiter h q cs
      cases sym with
      | term tok ls =>
          cases hd : delimiter.toList with
          | nil => simp [Grammar.delimiterUniqueFrom, hd] at h
          | cons d ds =>
              have hmem : decide (tok.mem d) = false := by
                simpa [Grammar.delimiterUniqueFrom, hd] using h
              have hdelim : delimiter = String.ofList (d :: ds) := by
                calc
                  delimiter = String.ofList delimiter.toList := String.ofList_toList.symm
                  _ = String.ofList (d :: ds) := by rw [hd]
              rw [hdelim]
              exact termThenLiteral_matches g q 0 tok ls d ds cs (of_decide_eq_false hmem)
      | lit l => simp [Grammar.delimiterUniqueFrom] at h
      | ref name => simp [Grammar.delimiterUniqueFrom] at h
      | rep sep item lo hi => simp [Grammar.delimiterUniqueFrom] at h
  | succ fuel ih =>
      intro sym delimiter h q cs
      cases sym with
      | term tok ls =>
          cases hd : delimiter.toList with
          | nil => simp [Grammar.delimiterUniqueFrom, hd] at h
          | cons d ds =>
              have hmem : decide (tok.mem d) = false := by
                simpa [Grammar.delimiterUniqueFrom, hd] using h
              have hdelim : delimiter = String.ofList (d :: ds) := by
                calc
                  delimiter = String.ofList delimiter.toList := String.ofList_toList.symm
                  _ = String.ofList (d :: ds) := by rw [hd]
              rw [hdelim]
              exact termThenLiteral_matches g q (fuel + 1) tok ls d ds cs
                (of_decide_eq_false hmem)
      | lit l => simp [Grammar.delimiterUniqueFrom] at h
      | rep sep item lo hi => simp [Grammar.delimiterUniqueFrom] at h
      | ref name =>
          cases hp : g.prod? name with
          | none => simp [Grammar.delimiterUniqueFrom, hp] at h
          | some p =>
              rcases p with ⟨prodName, alts⟩
              cases alts with
              | nil => simp [Grammar.delimiterUniqueFrom, hp] at h
              | cons alt moreAlts =>
                  cases moreAlts with
                  | cons alt' more => simp [Grammar.delimiterUniqueFrom, hp] at h
                  | nil =>
                      cases alt with
                      | nil => simp [Grammar.delimiterUniqueFrom, hp] at h
                      | cons item rest =>
                          cases rest with
                          | cons item' rest' => simp [Grammar.delimiterUniqueFrom, hp] at h
                          | nil =>
                              rcases item with ⟨inner, optional⟩
                              cases optional with
                              | true => simp [Grammar.delimiterUniqueFrom, hp] at h
                              | false =>
                                  simp only [Grammar.delimiterUniqueFrom, hp] at h
                                  have hinner := ih inner delimiter h name cs
                                  simp only [matchSym] at hinner
                                  simp only [matchSym, hp, matchProd, matchSeq,
                                    Bool.false_eq_true, if_false, List.flatMap_singleton]
                                  simpa [List.flatMap_map, List.map_map, Function.comp_def]
                                    using hinner

private theorem headExcludes_lit_match (g : Grammar) (q : String) (fuel : Nat)
    (l : String) (c : Char) (cs : List Char) (out : CaptureMap × List Char)
    (h : g.headExcludesFrom fuel (.lit l) c = true)
    (hout : out ∈ matchSym g q fuel (.lit l) cs) : cs.head? ≠ some c := by
  cases hl : l.toList with
  | nil => simp [Grammar.headExcludesFrom, hl] at h
  | cons d ds =>
      have hdc : d ≠ c := by simpa [Grammar.headExcludesFrom, hl] using h
      simp only [matchSym] at hout
      by_cases hp : l.toList.isPrefixOf cs = true
      · obtain ⟨r, hcs⟩ := List.isPrefixOf_iff_prefix.mp hp
        rw [← hcs, hl]
        simp [hdc]
      · rw [Bool.not_eq_true] at hp
        simp [hp] at hout

private theorem headExcludes_term_match_zero (g : Grammar) (q : String)
    (tok : TokClass) (ls : LenSpec) (c : Char) (cs : List Char)
    (out : CaptureMap × List Char) (h : g.headExcludesFrom 0 (.term tok ls) c = true)
    (hout : out ∈ matchSym g q 0 (.term tok ls) cs) : cs.head? ≠ some c := by
  simp only [Grammar.headExcludesFrom] at h
  rw [Bool.and_eq_true] at h
  have hdec : decide (tok.mem c) = false := by simpa using h.2
  simp only [matchSym] at hout
  rw [List.mem_filterMap] at hout
  obtain ⟨k, hk, hval⟩ := hout
  by_cases hok : termPrefixOk tok ls cs k = true
  · rw [hok] at hval
    simp only [if_true, Option.some.injEq] at hval
    subst out
    unfold termPrefixOk at hok
    rw [Bool.and_eq_true] at hok
    have hkbound := of_decide_eq_true hok.1
    have hmatches := of_decide_eq_true hok.2
    have hkpos : 0 < k := by
      cases ls with
      | exactly n =>
          have hn : n ≠ 0 := by simpa using h.1
          unfold matchesTerm LenSpec.sat at hmatches
          have hlen := hmatches.2
          simp only [String.length_ofList, List.length_take, Nat.min_eq_left hkbound] at hlen
          omega
      | between lo hi =>
          have hlo : lo ≠ 0 := by simpa using h.1
          unfold matchesTerm LenSpec.sat at hmatches
          have hlen := hmatches.2.1
          simp only [String.length_ofList, List.length_take, Nat.min_eq_left hkbound] at hlen
          omega
      | atLeastOne =>
          unfold matchesTerm LenSpec.sat at hmatches
          have hlen := hmatches.2
          simp only [String.length_ofList, List.length_take, Nat.min_eq_left hkbound] at hlen
          omega
    intro hhead
    cases cs with
    | nil => simp at hhead
    | cons d rest =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst d
        have hmem : tok.mem c := by
          apply hmatches.1 c
          cases k with
          | zero => omega
          | succ k => simp [String.toList_ofList]
        exact (of_decide_eq_false hdec hmem).elim
  · rw [Bool.not_eq_true] at hok
    rw [hok] at hval
    simp at hval

private theorem headExcludes_term_match (g : Grammar) (q : String) (fuel : Nat)
    (tok : TokClass) (ls : LenSpec) (c : Char) (cs : List Char)
    (out : CaptureMap × List Char) (h : g.headExcludesFrom fuel (.term tok ls) c = true)
    (hout : out ∈ matchSym g q fuel (.term tok ls) cs) : cs.head? ≠ some c := by
  cases fuel with
  | zero => exact headExcludes_term_match_zero g q tok ls c cs out h hout
  | succ fuel =>
      exact headExcludes_term_match_zero g q tok ls c cs out
        (by simpa [Grammar.headExcludesFrom] using h)
        (by simpa [matchSym] using hout)

private theorem headExcludesFrom_match (g : Grammar) :
    ∀ fuel sym c, g.headExcludesFrom fuel sym c = true → ∀ q cs out,
      out ∈ matchSym g q fuel sym cs → cs.head? ≠ some c := by
  intro fuel
  induction fuel with
  | zero =>
      intro sym c h q cs out hout
      cases sym with
      | lit l => exact headExcludes_lit_match g q 0 l c cs out h hout
      | term tok ls => exact headExcludes_term_match g q 0 tok ls c cs out h hout
      | ref name => simp [Grammar.headExcludesFrom] at h
      | rep sep item lo hi => simp [Grammar.headExcludesFrom] at h
  | succ fuel ih =>
      intro sym c h q cs out hout
      cases sym with
      | lit l => exact headExcludes_lit_match g q (fuel + 1) l c cs out h hout
      | term tok ls => exact headExcludes_term_match g q (fuel + 1) tok ls c cs out h hout
      | rep sep item lo hi => simp [Grammar.headExcludesFrom] at h
      | ref name =>
          cases hp : g.prod? name with
          | none => simp [Grammar.headExcludesFrom, hp] at h
          | some p =>
              rcases p with ⟨prodName, alts⟩
              cases alts with
              | nil => simp [Grammar.headExcludesFrom, hp] at h
              | cons alt moreAlts =>
                  cases moreAlts with
                  | cons alt' more => simp [Grammar.headExcludesFrom, hp] at h
                  | nil =>
                      cases alt with
                      | nil => simp [Grammar.headExcludesFrom, hp] at h
                      | cons item rest =>
                          cases rest with
                          | cons item' rest' => simp [Grammar.headExcludesFrom, hp] at h
                          | nil =>
                              rcases item with ⟨inner, optional⟩
                              cases optional with
                              | true => simp [Grammar.headExcludesFrom, hp] at h
                              | false =>
                                  simp only [Grammar.headExcludesFrom, hp] at h
                                  simp only [matchSym, hp, matchProd, matchSeq,
                                    Bool.false_eq_true, if_false, List.flatMap_singleton] at hout
                                  simp at hout
                                  obtain ⟨m, r, hinner, rfl⟩ := hout
                                  exact ih inner c h name cs (m, r) hinner

private theorem prefixUniqueSeq_matches (g : Grammar) (fuel : Nat)
    (hsym : ∀ sym, g.prefixUniqueFrom fuel sym = true → ∀ q cs,
      (matchSym g q fuel sym cs).length ≤ 1) :
    ∀ seq, g.prefixUniqueSeqFrom fuel seq = true → ∀ q cs,
      (matchSeq g q fuel seq cs).length ≤ 1 := by
  intro seq hseq
  induction seq with
  | nil => simp [matchSeq]
  | cons item rest ih =>
      have hall := List.all_eq_true.mp hseq
      have hitem := hall item (by simp)
      have hrest : g.prefixUniqueSeqFrom fuel rest = true := by
        apply List.all_eq_true.mpr
        intro x hx
        exact hall x (by simp [hx])
      rcases item with ⟨sym, optional⟩
      cases optional with
      | true => simp at hitem
      | false =>
          simp only [Bool.not_false, Bool.true_and] at hitem
          intro q cs
          simp only [matchSeq, Bool.false_eq_true, if_false]
          apply length_flatMap_le_one (hsym sym hitem q cs)
          intro x hx
          rcases x with ⟨m, r⟩
          simp only [List.length_map]
          exact ih hrest q r

private theorem prefixUniqueFrom_matches (g : Grammar) :
    ∀ fuel sym, g.prefixUniqueFrom fuel sym = true → ∀ q cs,
      (matchSym g q fuel sym cs).length ≤ 1 := by
  intro fuel
  induction fuel with
  | zero =>
      intro sym h q cs
      cases sym with
      | lit l =>
          simp only [matchSym]
          split <;> simp
      | term tok ls =>
          cases ls with
          | exactly n => exact prefixMatches_term g q 0 tok (.exactly n) cs rfl
          | between lo hi =>
              exact prefixMatches_term g q 0 tok (.between lo hi) cs
                (by simpa [Grammar.prefixUniqueFrom] using h)
          | atLeastOne => simp [Grammar.prefixUniqueFrom] at h
      | ref name => simp [Grammar.prefixUniqueFrom] at h
      | rep sep item lo hi => simp [Grammar.prefixUniqueFrom] at h
  | succ fuel ih =>
      intro sym h q cs
      cases sym with
      | lit l =>
          simp only [matchSym]
          split <;> simp
      | term tok ls =>
          cases ls with
          | exactly n => exact prefixMatches_term g q (fuel + 1) tok (.exactly n) cs rfl
          | between lo hi =>
              exact prefixMatches_term g q (fuel + 1) tok (.between lo hi) cs
                (by simpa [Grammar.prefixUniqueFrom] using h)
          | atLeastOne => simp [Grammar.prefixUniqueFrom] at h
      | rep sep item lo hi => simp [Grammar.prefixUniqueFrom] at h
      | ref name =>
          cases hp : g.prod? name with
          | none => simp [Grammar.prefixUniqueFrom, hp] at h
          | some p =>
              rcases p with ⟨prodName, alts⟩
              cases alts with
              | nil => simp [Grammar.prefixUniqueFrom, hp] at h
              | cons alt moreAlts =>
                  cases moreAlts with
                  | cons alt' more => simp [Grammar.prefixUniqueFrom, hp] at h
                  | nil =>
                      simp only [Grammar.prefixUniqueFrom, hp] at h
                      simp only [matchSym, hp, matchProd, List.flatMap_singleton,
                        List.length_map]
                      apply prefixUniqueSeq_matches g fuel
                        (fun inner hinner => ih inner hinner)
                        alt
                      simpa [Grammar.prefixUniqueSeqFrom] using h

private theorem sequenceUniqueSeq_fullMatches (g : Grammar) (fuel : Nat) :
    ∀ seq, g.sequenceUniqueSeqFrom fuel seq = true → ∀ q cs,
      (fullMatches (matchSeq g q fuel seq cs)).length ≤ 1 := by
  intro seq
  induction seq with
  | nil =>
      intro h q cs
      exact Nat.le_trans (List.length_filter_le _ _) (by simp [matchSeq])
  | cons item rest ih =>
      cases rest with
      | nil =>
          rcases item with ⟨sym, optional⟩
          cases optional with
          | true => simp [Grammar.sequenceUniqueSeqFrom]
          | false =>
              intro h q cs
              simp only [Grammar.sequenceUniqueSeqFrom, Bool.not_false, Bool.true_and] at h
              have hsym :
                  (fullMatches (matchSym g q fuel sym cs)).length ≤ 1 := by
                rcases Bool.or_eq_true_iff.mp h with hprefix | hunary
                · exact Nat.le_trans (List.length_filter_le _ _) <|
                    prefixUniqueFrom_matches g fuel sym hprefix q cs
                · exact unaryUniqueFrom_fullMatches g fuel sym hunary q cs
              unfold fullMatches at hsym ⊢
              simp only [matchSeq, Bool.false_eq_true, if_false]
              simpa [List.filter_map, Function.comp_def] using hsym
      | cons next tail =>
          rcases item with ⟨sym, optional⟩
          cases optional with
          | true => simp [Grammar.sequenceUniqueSeqFrom]
          | false =>
              intro h q cs
              simp only [Grammar.sequenceUniqueSeqFrom, Bool.not_false, Bool.true_and] at h
              rcases Bool.or_eq_true_iff.mp h with hprefix | hdelimited
              · rw [Bool.and_eq_true] at hprefix
                unfold fullMatches
                simp only [matchSeq, Bool.false_eq_true, if_false]
                rw [List.filter_flatMap]
                apply length_flatMap_le_one
                  (prefixUniqueFrom_matches g fuel sym hprefix.1 q cs)
                intro x hx
                rcases x with ⟨m, r⟩
                rw [List.filter_map, List.length_map]
                have hpred :
                    ((fun x : CaptureMap × List Char => x.2.isEmpty) ∘
                      (fun x : CaptureMap × List Char => (m ++ x.1, x.2))) =
                      (fun x : CaptureMap × List Char => x.2.isEmpty) := rfl
                rw [hpred]
                have htail := ih hprefix.2 q r
                unfold fullMatches at htail
                unfold matchSeq at htail
                simpa only [Prod.snd] using htail
              · rcases next with ⟨nextSym, nextOptional⟩
                cases nextOptional with
                | true => simp at hdelimited
                | false =>
                    cases nextSym with
                    | lit delimiter =>
                        simp only [Bool.not_false, Bool.true_and, Bool.and_eq_true] at hdelimited
                        let pairs :=
                          (matchSym g q fuel sym cs).flatMap (fun x =>
                            (matchSym g q fuel (.lit delimiter) x.2).map
                              (fun y => (x.1 ++ y.1, y.2)))
                        have hpairs : pairs.length ≤ 1 :=
                          delimiterUniqueFrom_matches g fuel sym delimiter hdelimited.1 q cs
                        have hpairsTail : ∀ y ∈ pairs,
                            (fullMatches (matchSeq g q fuel tail y.2)).length ≤ 1 := by
                          intro y hy
                          have hnext :
                              g.sequenceUniqueSeqFrom fuel
                                ({ sym := .lit delimiter, optional := false } :: tail) =
                                true := by
                            cases tail <;>
                              simp [Grammar.sequenceUniqueSeqFrom, Grammar.prefixUniqueFrom,
                                hdelimited.2]
                          have hwhole := ih hnext q (delimiter.toList ++ y.2)
                          simpa [matchSeq, matchSym, fullMatches] using hwhole
                        have hdecomp :
                            matchSeq g q fuel
                                ({ sym := sym, optional := false } ::
                                  { sym := .lit delimiter, optional := false } :: tail) cs =
                              pairs.flatMap (fun y =>
                                (matchSeq g q fuel tail y.2).map
                                  (fun z => (y.1 ++ z.1, z.2))) := by
                          dsimp [pairs]
                          simp [matchSeq, List.flatMap_assoc, List.flatMap_map,
                            List.map_flatMap, List.append_assoc, Function.comp_def]
                        unfold fullMatches
                        rw [hdecomp, List.filter_flatMap]
                        apply length_flatMap_le_one hpairs
                        intro y hy
                        rw [List.filter_map, List.length_map]
                        have hpred :
                            ((fun x : CaptureMap × List Char => x.2.isEmpty) ∘
                              (fun z : CaptureMap × List Char => (y.1 ++ z.1, z.2))) =
                              (fun x : CaptureMap × List Char => x.2.isEmpty) := rfl
                        rw [hpred]
                        simpa [fullMatches] using hpairsTail y hy
                    | term tok ls => simp at hdelimited
                    | ref name => simp at hdelimited
                    | rep sep inner lo hi => simp at hdelimited

private theorem decodeUnique_of_start_sequence (g : Grammar) (prodName : String)
    (alt : Seq) (hstart : g.startProd? = some (Production.mk prodName [alt]))
    (s : String)
    (hseq : (fullMatches (matchSeq g "" g.prods.length alt s.toList)).length ≤ 1) :
    DecodeUnique g s := by
  unfold DecodeUnique fullParses
  rw [hstart]
  simp only [matchProd, List.flatMap_singleton, List.length_map]
  exact hseq

/-- A successful required-sequence check is a grammar-wide uniqueness certificate. -/
theorem GrammarDecodeUnique.of_sequenceUnique (g : Grammar)
    (h : g.sequenceUnique = true) : GrammarDecodeUnique g := by
  intro s
  unfold Grammar.sequenceUnique at h
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
              simp only [hstart] at h
              apply decodeUnique_of_start_sequence g prodName alt hstart s
              exact sequenceUniqueSeq_fullMatches g g.prods.length alt h "" s.toList

/-- A match of a sequence with a statically visible leading literal starts with that literal's
    first character. -/
private theorem leadingLiteral_matchSeq_head (g : Grammar) (q : String) (fuel : Nat)
    (alt : Seq) (c : Char) (cs : List Char)
    (hlead : alt.leadingLiteral? = some c)
    {out : CaptureMap × List Char} (hout : out ∈ matchSeq g q fuel alt cs) :
    cs.head? = some c := by
  cases alt with
  | nil => simp [Seq.leadingLiteral?] at hlead
  | cons item rest =>
      rcases item with ⟨sym, optional⟩
      cases optional with
      | true => simp [Seq.leadingLiteral?] at hlead
      | false =>
          cases sym with
          | lit l =>
              cases hl : l.toList with
              | nil => simp [Seq.leadingLiteral?, hl] at hlead
              | cons d ds =>
                  simp only [Seq.leadingLiteral?, hl, List.head?_cons,
                    Option.some.injEq] at hlead
                  subst d
                  by_cases hprefix : l.toList.isPrefixOf cs = true
                  · obtain ⟨tail, hcs⟩ := List.isPrefixOf_iff_prefix.mp hprefix
                    rw [← hcs, hl]
                    rfl
                  · simp [matchSeq, matchSym, hprefix] at hout
          | ref name => simp [Seq.leadingLiteral?] at hlead
          | term tok lenSpec => simp [Seq.leadingLiteral?] at hlead
          | rep sep inner lo hi => simp [Seq.leadingLiteral?] at hlead

/-- The leading-literal result also applies to a full match. -/
private theorem leadingLiteral_fullMatch_head (g : Grammar) (q : String) (fuel : Nat)
    (alt : Seq) (c : Char) (cs : List Char)
    (hlead : alt.leadingLiteral? = some c)
    {out : CaptureMap × List Char}
    (hout : out ∈ fullMatches (matchSeq g q fuel alt cs)) :
    cs.head? = some c :=
  leadingLiteral_matchSeq_head g q fuel alt c cs hlead (List.mem_filter.mp hout).1

private theorem length_append_le_one_of_exclusive {α : Type} (xs ys : List α)
    (hxs : xs.length ≤ 1) (hys : ys.length ≤ 1)
    (hexclusive : xs ≠ [] → ys ≠ [] → False) :
    (xs ++ ys).length ≤ 1 := by
  cases xs with
  | nil => simpa using hys
  | cons x xs =>
      cases xs with
      | cons y tail => simp at hxs
      | nil =>
          cases ys with
          | nil => simp
          | cons y tail => exact (hexclusive (by simp) (by simp)).elim

private theorem optionalLiteralRefSequence_fullMatches_exact (g : Grammar)
    (q name prodName l : String) (fuel : Nat) (rest : Seq)
    (hprod : g.prod? name =
      some (Production.mk prodName [[{ sym := .lit l, optional := true }]]))
    (cs : List Char)
    (hrest : ∀ input, (fullMatches (matchSeq g q (fuel + 1) rest input)).length ≤ 1)
    (c : Char) (ds : List Char) (hl : l.toList = c :: ds)
    (hexcludes : ∀ out, out ∈ matchSeq g q (fuel + 1) rest cs →
      cs.head? ≠ some c) :
    (fullMatches (matchSeq g q (fuel + 1)
      ({ sym := .ref name, optional := false } :: rest) cs)).length ≤ 1 := by
  by_cases hp : l.toList.isPrefixOf cs = true
  · have hpresent := hrest (cs.drop l.toList.length)
    have habsent := hrest cs
    have he :
        fullMatches (matchSeq g q (fuel + 1) rest (cs.drop l.toList.length)) ≠ [] →
        fullMatches (matchSeq g q (fuel + 1) rest cs) ≠ [] → False := by
      intro hpre habs
      have hhead : cs.head? = some c := by
        obtain ⟨r, hcs⟩ := List.isPrefixOf_iff_prefix.mp hp
        rw [← hcs, hl]
        rfl
      cases hx : fullMatches (matchSeq g q (fuel + 1) rest cs) with
      | nil => exact (habs hx).elim
      | cons out outs =>
          have houtFull : out ∈ fullMatches (matchSeq g q (fuel + 1) rest cs) := by
            rw [hx]
            simp
          exact (hexcludes out (List.mem_filter.mp houtFull).1 hhead).elim
    have happ := length_append_le_one_of_exclusive _ _ hpresent habsent he
    simpa [matchSeq, matchSym, hprod, matchProd, hp, fullMatches, List.filter_map,
      Function.comp_def] using happ
  · rw [Bool.not_eq_true] at hp
    have habsent := hrest cs
    simpa [matchSeq, matchSym, hprod, matchProd, hp, fullMatches, List.filter_map,
      Function.comp_def] using habsent

private theorem optionalLiteralRefSequence_fullMatches (g : Grammar) :
    ∀ fuel sym l, g.optionalLiteralRef? fuel sym = some l → ∀ q rest cs c ds,
      l.toList = c :: ds →
      (∀ input, (fullMatches (matchSeq g q fuel rest input)).length ≤ 1) →
      (∀ out, out ∈ matchSeq g q fuel rest cs → cs.head? ≠ some c) →
      (fullMatches (matchSeq g q fuel
        ({ sym := sym, optional := false } :: rest) cs)).length ≤ 1 := by
  intro fuel
  cases fuel with
  | zero =>
      intro sym l h
      simp [Grammar.optionalLiteralRef?] at h
  | succ fuel =>
      intro sym l h q rest cs c ds hl hrest hexcludes
      cases sym with
      | lit lit => simp [Grammar.optionalLiteralRef?] at h
      | term tok ls => simp [Grammar.optionalLiteralRef?] at h
      | rep sep item lo hi => simp [Grammar.optionalLiteralRef?] at h
      | ref name =>
          cases hp : g.prod? name with
          | none => simp [Grammar.optionalLiteralRef?, hp] at h
          | some p =>
              rcases p with ⟨prodName, alts⟩
              cases alts with
              | nil => simp [Grammar.optionalLiteralRef?, hp] at h
              | cons alt moreAlts =>
                  cases moreAlts with
                  | cons alt' more => simp [Grammar.optionalLiteralRef?, hp] at h
                  | nil =>
                      cases alt with
                      | nil => simp [Grammar.optionalLiteralRef?, hp] at h
                      | cons item rest' =>
                          cases rest' with
                          | cons item' tail => simp [Grammar.optionalLiteralRef?, hp] at h
                          | nil =>
                              rcases item with ⟨inner, optional⟩
                              cases optional with
                              | false => simp [Grammar.optionalLiteralRef?, hp] at h
                              | true =>
                                  cases inner with
                                  | lit literal =>
                                      by_cases hempty : literal.isEmpty = true
                                      · simp [Grammar.optionalLiteralRef?, hp, hempty] at h
                                      · rw [Bool.not_eq_true] at hempty
                                        simp [Grammar.optionalLiteralRef?, hp, hempty] at h
                                        subst literal
                                        exact optionalLiteralRefSequence_fullMatches_exact
                                          g q name prodName l fuel rest hp cs hrest c ds hl
                                          hexcludes
                                  | term tok ls => simp [Grammar.optionalLiteralRef?, hp] at h
                                  | ref innerName => simp [Grammar.optionalLiteralRef?, hp] at h
                                  | rep sep item lo hi =>
                                      simp [Grammar.optionalLiteralRef?, hp] at h

/-- Pairwise-disjoint literal-leading alternatives have at most one full parse. -/
private theorem literalAlternatives_fullMatches (g : Grammar) (fuel : Nat) :
    ∀ alts, g.literalAlternativesUniqueFrom fuel alts = true → ∀ q cs,
      (fullMatches (alts.flatMap (fun alt => matchSeq g q fuel alt cs))).length ≤ 1 := by
  intro alts
  induction alts with
  | nil => simp [Grammar.literalAlternativesUniqueFrom, fullMatches]
  | cons alt alts ih =>
      intro h q cs
      cases hlead : alt.leadingLiteral? with
      | none => simp [Grammar.literalAlternativesUniqueFrom, hlead] at h
      | some c =>
          simp only [Grammar.literalAlternativesUniqueFrom, hlead, Bool.and_eq_true] at h
          rw [List.flatMap_cons]
          unfold fullMatches
          rw [List.filter_append]
          apply length_append_le_one_of_exclusive
          · exact sequenceUniqueSeq_fullMatches g fuel alt h.1 q cs
          · simpa [fullMatches] using ih h.2.2 q cs
          · intro hhead htail
            have headMem : ∃ out, out ∈
                fullMatches (matchSeq g q fuel alt cs) := by
              cases hx : fullMatches (matchSeq g q fuel alt cs) with
              | nil => exact (hhead hx).elim
              | cons x xs => exact ⟨x, by simp⟩
            have tailMem : ∃ out, out ∈
                fullMatches (alts.flatMap (fun other => matchSeq g q fuel other cs)) := by
              cases hy : fullMatches
                  (alts.flatMap (fun other => matchSeq g q fuel other cs)) with
              | nil => exact (htail hy).elim
              | cons y ys => exact ⟨y, by simp⟩
            obtain ⟨x, hx⟩ := headMem
            obtain ⟨y, hy⟩ := tailMem
            have hheadChar := leadingLiteral_fullMatch_head
              g q fuel alt c cs hlead hx
            have hyFilter := List.mem_filter.mp hy
            rw [List.mem_flatMap] at hyFilter
            obtain ⟨other, hother, hyOther⟩ := hyFilter.1
            have hdistinct := List.all_eq_true.mp h.2.1 other hother
            cases hotherLead : other.leadingLiteral? with
            | none => simp [hotherLead] at hdistinct
            | some d =>
                have hcd : (!(c == d)) = true := by
                  simpa [hotherLead] using hdistinct
                have hyFull :
                    y ∈ fullMatches (matchSeq g q fuel other cs) :=
                  List.mem_filter.mpr ⟨hyOther, hyFilter.2⟩
                have htailChar := leadingLiteral_fullMatch_head
                  g q fuel other d cs hotherLead hyFull
                have hdc : d = c := Option.some.inj (htailChar.symm.trans hheadChar)
                subst d
                simp at hcd

/-- A successful literal-leading alternative check is a grammar-wide uniqueness certificate. -/
theorem GrammarDecodeUnique.of_literalAlternativesUnique (g : Grammar)
    (h : g.literalAlternativesUnique = true) : GrammarDecodeUnique g := by
  intro s
  unfold Grammar.literalAlternativesUnique at h
  cases hstart : g.startProd? with
  | none => simp [DecodeUnique, fullParses, hstart]
  | some p =>
      simp only [hstart] at h
      unfold DecodeUnique fullParses
      rw [hstart]
      simp only [List.length_map]
      unfold matchProd
      change (fullMatches
        (p.alts.flatMap (fun alt => matchSeq g "" g.prods.length alt s.toList))).length ≤ 1
      exact literalAlternatives_fullMatches g g.prods.length p.alts h "" s.toList

/-- A required reference to one optional literal is unique when its consuming and empty
    branches are separated by the FIRST character of a sequence-unique remainder. -/
theorem GrammarDecodeUnique.of_optionalHeadUnique (g : Grammar)
    (h : g.optionalHeadUnique = true) : GrammarDecodeUnique g := by
  intro s
  unfold Grammar.optionalHeadUnique at h
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
                  rcases item with ⟨sym, optional⟩
                  cases optional with
                  | true => simp [hstart] at h
                  | false =>
                      cases hopt : g.optionalLiteralRef? g.prods.length sym with
                      | none => simp [hstart, hopt] at h
                      | some l =>
                          cases hl : l.toList with
                          | nil => simp [hstart, hopt, hl] at h
                          | cons c ds =>
                              cases rest with
                              | nil => simp [hstart, hopt, hl] at h
                              | cons next tail =>
                                  rcases next with ⟨nextSym, nextOptional⟩
                                  cases nextOptional with
                                  | true => simp [hstart, hopt, hl] at h
                                  | false =>
                                      simp only [hstart, Bool.not_false, Bool.true_and, hopt,
                                        hl, List.head?_cons] at h
                                      rw [Bool.and_eq_true] at h
                                      apply decodeUnique_of_start_sequence g prodName
                                        ({ sym := sym, optional := false } ::
                                          { sym := nextSym, optional := false } :: tail)
                                        hstart s
                                      apply optionalLiteralRefSequence_fullMatches g
                                        g.prods.length sym l hopt ""
                                        ({ sym := nextSym, optional := false } :: tail)
                                        s.toList c ds hl
                                      · intro input
                                        exact sequenceUniqueSeq_fullMatches g g.prods.length
                                          ({ sym := nextSym, optional := false } :: tail)
                                          h.1 "" input
                                      · intro out hout
                                        simp only [matchSeq, Bool.false_eq_true, if_false] at hout
                                        rw [List.mem_flatMap] at hout
                                        obtain ⟨⟨m, r⟩, hm, htail⟩ := hout
                                        exact headExcludesFrom_match g g.prods.length nextSym c
                                          h.2 "" s.toList (m, r) hm

/-- The combined static checker is sound for all inputs. -/
theorem GrammarDecodeUnique.of_staticUnique (g : Grammar)
    (h : g.staticUnique = true) : GrammarDecodeUnique g := by
  rw [Grammar.staticUnique, Bool.or_eq_true_iff, Bool.or_eq_true_iff,
    Bool.or_eq_true_iff] at h
  rcases h with ((hunary | hseq) | halts) | hoptional
  · exact GrammarDecodeUnique.of_unaryUnique g hunary
  · exact GrammarDecodeUnique.of_sequenceUnique g hseq
  · exact GrammarDecodeUnique.of_literalAlternativesUnique g halts
  · exact GrammarDecodeUnique.of_optionalHeadUnique g hoptional

/-! Executable regression checks for the accepted and rejected sequence fragments. -/

private def fixedSequenceGrammar : Grammar where
  start := "S"
  prods := [{
    name := "S"
    alts := [[
      { sym := .term .hexDigit (.exactly 8) },
      { sym := .lit "-" },
      { sym := .term .hexDigit (.exactly 4) }
    ]]
  }]

private def variableTailGrammar : Grammar where
  start := "S"
  prods := [{
    name := "S"
    alts := [[
      { sym := .lit "v" },
      { sym := .term .digit .atLeastOne }
    ]]
  }]

private def referencedSequenceGrammar : Grammar where
  start := "S"
  prods := [
    {
      name := "S"
      alts := [[
        { sym := .ref "Head" },
        { sym := .lit "-" },
        { sym := .ref "Tail" }
      ]]
    },
    {
      name := "Head"
      alts := [[{ sym := .term .hexDigit (.exactly 8) }]]
    },
    {
      name := "Tail"
      alts := [[{ sym := .term .digit .atLeastOne }]]
    }
  ]

private def variableBoundaryGrammar : Grammar where
  start := "S"
  prods := [{
    name := "S"
    alts := [[
      { sym := .term .digit .atLeastOne },
      { sym := .lit "-" }
    ]]
  }]

private def optionalSequenceGrammar : Grammar where
  start := "S"
  prods := [{
    name := "S"
    alts := [[
      { sym := .lit "-", optional := true },
      { sym := .term .digit (.exactly 2) }
    ]]
  }]

private def decimalLikeGrammar : Grammar where
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

private def taggedAlternativeGrammar : Grammar where
  start := "S"
  prods := [{
    name := "S"
    alts := [
      [
        { sym := .lit "d" },
        { sym := .term .digit .atLeastOne }
      ],
      [
        { sym := .lit "x" },
        { sym := .term .hexDigit (.exactly 2) }
      ]
    ]
  }]

private def overlappingLiteralAlternativeGrammar : Grammar where
  start := "S"
  prods := [{
    name := "S"
    alts := [
      [{ sym := .lit "a" }],
      [{ sym := .lit "another" }]
    ]
  }]

private def emptyLiteralAlternativeGrammar : Grammar where
  start := "S"
  prods := [{
    name := "S"
    alts := [
      [{ sym := .lit "" }],
      [{ sym := .lit "x" }]
    ]
  }]

#guard fixedSequenceGrammar.staticUnique
#guard variableTailGrammar.staticUnique
#guard referencedSequenceGrammar.staticUnique
#guard taggedAlternativeGrammar.staticUnique
#guard variableBoundaryGrammar.staticUnique
#guard decimalLikeGrammar.staticUnique
#guard !optionalSequenceGrammar.staticUnique
#guard !overlappingLiteralAlternativeGrammar.staticUnique
#guard !emptyLiteralAlternativeGrammar.staticUnique

private theorem fixedSequenceGrammar_unique : GrammarDecodeUnique fixedSequenceGrammar :=
  GrammarDecodeUnique.of_staticUnique fixedSequenceGrammar (by decide)

private theorem variableTailGrammar_unique : GrammarDecodeUnique variableTailGrammar :=
  GrammarDecodeUnique.of_staticUnique variableTailGrammar (by decide)

private theorem referencedSequenceGrammar_unique :
    GrammarDecodeUnique referencedSequenceGrammar :=
  GrammarDecodeUnique.of_staticUnique referencedSequenceGrammar (by decide)

private theorem taggedAlternativeGrammar_unique :
    GrammarDecodeUnique taggedAlternativeGrammar :=
  GrammarDecodeUnique.of_staticUnique taggedAlternativeGrammar (by decide)

private theorem variableBoundaryGrammar_unique :
    GrammarDecodeUnique variableBoundaryGrammar :=
  GrammarDecodeUnique.of_staticUnique variableBoundaryGrammar (by decide)

private theorem decimalLikeGrammar_unique : GrammarDecodeUnique decimalLikeGrammar :=
  GrammarDecodeUnique.of_staticUnique decimalLikeGrammar (by decide)

end Triptych
