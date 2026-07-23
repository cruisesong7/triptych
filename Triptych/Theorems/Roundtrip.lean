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

import Triptych.Architecture.Decode

/-!
# `decode` ↔ `IsWf` roundtrip

The executable capture extractor `decode` (from `Triptych.Architecture.Decode`) and the
denotational well-formedness predicate `IsWf` (from `Triptych.Architecture.Denote`) agree
on acceptance, for every
grammar in the decoder-agreeing class (`hg : g.repOk = true`):

    theorem decodeSome_iff_IsWf (g : Grammar) (hg : g.repOk = true) (s : String) :
        (decode g s).isSome = true ↔ IsWf g s

The `g.repOk` side condition is essential: it forbids empty `rep` separators AND `lo = 0`
repetitions. Both are cases where the executable `matchRep`/`matchStar` (which match
`item (sep item)*`, always ≥ 1 item, and cannot enumerate empty-separated items) disagree with
the denotation's free `parts`-list existential. The DSL rejects both at parse time, so every
generated grammar satisfies `g.repOk` (by `decide`).

The proof goes through three mutually-recursive **bridge lemmas** relating each `match*`
combinator's *reachable remainders* to the corresponding `matches*` denotation, with the
capture map `m` and the qualifier `q` (both irrelevant to which remainders are reachable)
quantified away, each threading the relevant slice of `repOk`:

    (∃ m, (m, r₂) ∈ matchSym  g q fuel sym cs) ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSym  g fuel sym (String.ofList r₁)
    (∃ m, (m, r₂) ∈ matchSeq  g q fuel seq cs) ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSeq  g fuel seq (String.ofList r₁)
    (∃ m, (m, r₂) ∈ matchProd g q fuel p  cs) ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesProd g fuel p  (String.ofList r₁)

The structure is the standard mutual fuel induction (`sym`/`seq`/`prod`, each given the next
level down):
`sym_iter` is proved by induction on `fuel` (the `ref` case at `fuel+1` drops to
`matchProd` at `fuel`; the `rep` case drops to `rep_iter` at the same fuel via a `matchStar`/
`matchRep` bridge); `seq_iter` by induction on the sequence list; `prod_iter`
over the alternatives. `decodeSome_iff_IsWf` then instantiates the prod bridge with `r₂ = []`.
-/

namespace Triptych

open List


-- lit leaf
theorem lit_leaf (g : Grammar) (q : String) (fuel : Nat) (l : String) (cs r₂ : List Char) :
    (∃ m, (m, r₂) ∈ matchSym g q fuel (Sym.lit l) cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSym g fuel (Sym.lit l) (String.ofList r₁) := by
  have hden : ∀ r₁ : List Char, matchesSym g fuel (Sym.lit l) (String.ofList r₁) ↔ r₁ = l.toList := by
    intro r₁; cases fuel <;> (
      simp only [matchesSym]; rw [← String.toList_inj, String.toList_ofList])
  cases fuel <;> (
    simp only [matchSym]
    constructor
    · rintro ⟨m, hmem⟩
      by_cases h : l.toList.isPrefixOf cs = true
      · simp only [h, if_true, List.mem_singleton] at hmem
        obtain ⟨t, ht⟩ := isPrefixOf_iff_prefix.mp h
        refine ⟨l.toList, ?_, (hden l.toList).mpr rfl⟩
        have hr₂ : r₂ = cs.drop l.toList.length := congrArg Prod.snd hmem
        subst ht; rw [hr₂, List.drop_left]
      · rw [Bool.not_eq_true] at h; rw [h] at hmem; simp at hmem
    · rintro ⟨r₁, hcs, hden'⟩
      rw [(hden r₁).mp hden'] at hcs
      have h : l.toList.isPrefixOf cs = true := by
        rw [hcs]; exact isPrefixOf_iff_prefix.mpr ⟨r₂, rfl⟩
      simp only [h, if_true]; exact ⟨[], by rw [hcs]; simp⟩)

-- term leaf
theorem term_leaf (g : Grammar) (q : String) (fuel : Nat) (tok : TokClass) (ls : LenSpec)
    (cs r₂ : List Char) :
    (∃ m, (m, r₂) ∈ matchSym g q fuel (Sym.term tok ls) cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSym g fuel (Sym.term tok ls) (String.ofList r₁) := by
  cases fuel <;> (
    simp only [matchSym, matchesSym]
    constructor
    · rintro ⟨m, hmem⟩
      rw [List.mem_filterMap] at hmem
      obtain ⟨k, hk, hval⟩ := hmem
      by_cases hok : termPrefixOk tok ls cs k = true
      · rw [hok] at hval; simp only [if_true, Option.some.injEq, Prod.mk.injEq] at hval
        refine ⟨cs.take k, ?_, ?_⟩
        · rw [← hval.2, List.take_append_drop]
        · unfold termPrefixOk at hok
          rw [Bool.and_eq_true] at hok
          exact of_decide_eq_true hok.2
      · rw [Bool.not_eq_true] at hok; rw [hok] at hval; simp at hval
    · rintro ⟨r₁, hcs, hden⟩
      refine ⟨[], ?_⟩
      rw [List.mem_filterMap]
      refine ⟨r₁.length, ?_, ?_⟩
      · rw [List.mem_range, hcs]; simp only [List.length_append]; omega
      · have hok : termPrefixOk tok ls cs r₁.length = true := by
          unfold termPrefixOk
          rw [Bool.and_eq_true]
          refine ⟨?_, ?_⟩
          · rw [decide_eq_true_eq, hcs]; simp
          · rw [decide_eq_true_eq, hcs, List.take_left]; exact hden
        rw [hok]; simp
        rw [hcs, List.drop_left])

-- present block characterization
theorem present_mem (g : Grammar) (q : String) (fuel : Nat) (item : SymItem)
    (rest : Seq) (cs r₂ : List Char) :
    (∃ m, (m, r₂) ∈ (matchSym g q fuel item.sym cs).flatMap (fun x =>
        (matchSeq g q fuel rest x.2).map (fun y => (x.1 ++ y.1, y.2))))
      ↔ ∃ r1, (∃ m1, (m1, r1) ∈ matchSym g q fuel item.sym cs)
              ∧ (∃ m2, (m2, r₂) ∈ matchSeq g q fuel rest r1) := by
  constructor
  · rintro ⟨m, hmem⟩
    rw [List.mem_flatMap] at hmem
    obtain ⟨⟨m1, r1⟩, hmem1, hmem2⟩ := hmem
    rw [List.mem_map] at hmem2
    obtain ⟨⟨m2, r₂'⟩, hmem2', heq⟩ := hmem2
    simp only [Prod.mk.injEq] at heq
    exact ⟨r1, ⟨m1, hmem1⟩, ⟨m2, by rw [← heq.2]; exact hmem2'⟩⟩
  · rintro ⟨r1, ⟨m1, hmem1⟩, ⟨m2, hmem2⟩⟩
    exact ⟨m1 ++ m2, List.mem_flatMap.mpr ⟨(m1, r1), hmem1,
      List.mem_map.mpr ⟨(m2, r₂), hmem2, rfl⟩⟩⟩

-- seq given sym at same fuel. `hsym` now requires the symbol be `repOk` (needed for the `rep`
-- case in `sym_iter`); `seq_iter` supplies that per item from the seq-level `hseqok`.
theorem seq_iter (g : Grammar) (q : String) (fuel : Nat)
    (hsym : ∀ sym, sym.repOk = true → ∀ cs r₂, (∃ m, (m, r₂) ∈ matchSym g q fuel sym cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSym g fuel sym (String.ofList r₁)) :
    ∀ seq, seq.all (fun it => it.sym.repOk) = true → ∀ cs r₂,
      (∃ m, (m, r₂) ∈ matchSeq g q fuel seq cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSeq g fuel seq (String.ofList r₁) := by
  intro seq
  induction seq with
  | nil =>
    intro _ cs r₂
    simp only [matchSeq, matchesSeq, List.mem_singleton]
    constructor
    · rintro ⟨m, heq⟩
      simp only [Prod.mk.injEq] at heq
      exact ⟨[], by rw [heq.2]; simp, rfl⟩
    · rintro ⟨r₁, hcs, hnil⟩
      have : r₁ = [] := by
        have := congrArg String.toList hnil
        rw [String.toList_ofList] at this; simpa using this
      subst this; simp at hcs
      exact ⟨[], by rw [hcs]⟩
  | cons item rest ih =>
    intro hseqok cs r₂
    rw [List.all_cons, Bool.and_eq_true] at hseqok
    have hitemok : item.sym.repOk = true := hseqok.1
    have hrestok : rest.all (fun it => it.sym.repOk) = true := hseqok.2
    have ih := ih hrestok
    have hpresent : (∃ m, (m, r₂) ∈ (matchSym g q fuel item.sym cs).flatMap (fun x =>
          (matchSeq g q fuel rest x.2).map (fun y => (x.1 ++ y.1, y.2))))
        ↔ (∃ r1 r1', cs = r1 ++ r1' ++ r₂ ∧ matchesSym g fuel item.sym (String.ofList r1)
              ∧ matchesSeq g fuel rest (String.ofList r1')) := by
      rw [present_mem]
      constructor
      · rintro ⟨rMid, hsymm, hseqm⟩
        rw [hsym item.sym hitemok] at hsymm
        obtain ⟨r1, hcs1, hden1⟩ := hsymm
        rw [ih] at hseqm
        obtain ⟨r1', hmid, hden2⟩ := hseqm
        exact ⟨r1, r1', by rw [hcs1, hmid, List.append_assoc], hden1, hden2⟩
      · rintro ⟨r1, r1', hcs, hden1, hden2⟩
        refine ⟨r1' ++ r₂, ?_, ?_⟩
        · rw [hsym item.sym hitemok]; exact ⟨r1, by rw [hcs, List.append_assoc], hden1⟩
        · rw [ih]; exact ⟨r1', rfl, hden2⟩
    unfold matchSeq matchesSeq
    by_cases hopt : item.optional = true
    · simp only [hopt, if_true]
      constructor
      · rintro ⟨m, hmem⟩
        rw [List.mem_append] at hmem
        cases hmem with
        | inl h =>
          obtain ⟨r1, r1', hcs, hd1, hd2⟩ := hpresent.mp ⟨m, h⟩
          exact ⟨r1 ++ r1', hcs, Or.inl ⟨String.ofList r1, String.ofList r1',
            by rw [String.ofList_append], hd1, hd2⟩⟩
        | inr h =>
          obtain ⟨r₁, hcs, hd⟩ := (ih cs r₂).mp ⟨m, h⟩
          exact ⟨r₁, hcs, Or.inr hd⟩
      · rintro ⟨r₁, hcs, hd⟩
        cases hd with
        | inl h =>
          obtain ⟨s1, s2, hsplit, hd1, hd2⟩ := h
          have hlist : r₁ = s1.toList ++ s2.toList := by
            have := congrArg String.toList hsplit
            rw [String.toList_ofList, String.toList_append] at this; exact this
          obtain ⟨m, hm⟩ := hpresent.mpr ⟨s1.toList, s2.toList,
            by rw [hcs, hlist, List.append_assoc],
            by rw [String.ofList_toList]; exact hd1,
            by rw [String.ofList_toList]; exact hd2⟩
          exact ⟨m, by rw [List.mem_append]; exact Or.inl hm⟩
        | inr h =>
          obtain ⟨m, hm⟩ := (ih cs r₂).mpr ⟨r₁, hcs, h⟩
          exact ⟨m, by rw [List.mem_append]; exact Or.inr hm⟩
    · simp only [Bool.not_eq_true] at hopt
      simp only [hopt, Bool.false_eq_true, if_false]
      rw [hpresent]
      constructor
      · rintro ⟨r1, r1', hcs, hd1, hd2⟩
        exact ⟨r1 ++ r1', hcs, String.ofList r1, String.ofList r1',
          by rw [String.ofList_append], hd1, hd2⟩
      · rintro ⟨r₁, hcs, s1, s2, hsplit, hd1, hd2⟩
        have hlist : r₁ = s1.toList ++ s2.toList := by
          have := congrArg String.toList hsplit
          rw [String.toList_ofList, String.toList_append] at this; exact this
        exact ⟨s1.toList, s2.toList, by rw [hcs, hlist, List.append_assoc],
          by rw [String.ofList_toList]; exact hd1,
          by rw [String.ofList_toList]; exact hd2⟩

-- prod given seq at same fuel. `hseq` now requires each alternative be `repOk`; `prod_iter`
-- supplies that per alternative from the production-level `hpok`.
theorem prod_iter (g : Grammar) (q : String) (fuel : Nat) (p : Production) (cs r₂ : List Char)
    (hpok : p.alts.all (fun alt => alt.all (fun it => it.sym.repOk)) = true)
    (hseq : ∀ seq, seq.all (fun it => it.sym.repOk) = true → ∀ cs r₂,
      (∃ m, (m, r₂) ∈ matchSeq g q fuel seq cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSeq g fuel seq (String.ofList r₁)) :
    (∃ m, (m, r₂) ∈ matchProd g q fuel p cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesProd g fuel p (String.ofList r₁) := by
  rw [List.all_eq_true] at hpok
  simp only [matchProd, matchesProd]
  constructor
  · rintro ⟨m, hmem⟩
    rw [List.mem_flatMap] at hmem
    obtain ⟨alt, halt, hm⟩ := hmem
    obtain ⟨r₁, hcs, hd⟩ := (hseq alt (by simpa using hpok alt halt) cs r₂).mp ⟨m, hm⟩
    exact ⟨r₁, hcs, alt, halt, hd⟩
  · rintro ⟨r₁, hcs, alt, halt, hd⟩
    obtain ⟨m, hm⟩ := (hseq alt (by simpa using hpok alt halt) cs r₂).mpr ⟨r₁, hcs, hd⟩
    exact ⟨m, List.mem_flatMap.mpr ⟨alt, halt, hm⟩⟩

/-! ### `rep` bridge infrastructure

The `rep` case is the one place the executable `matchRep`/`matchStar` (a `item (sep item)*`
backtracking loop, bounded by iteration fuel) must be shown to reach exactly the `parts`-list
witnesses of the `matchesSym` denotation. It works at the `List Char` level (avoiding
`String.intercalate`'s internal `.go`), then transports across `String.ofList`/`toList`.

Two side conditions are needed for the loop to match the denotation — both are captured by
`Sym.repOk` (see `Grammar.repOk`): a **non-empty separator** `sepL ≠ []` (so each iteration
consumes ≥ 1 char ⟹ the remainder length is always enough iteration fuel) and **`1 ≤ lo`**
(so the `parts`-list is non-empty, matching `matchRep`'s always-≥-1-item behavior). -/

/-- `sepL.intercalate (a :: rest)` re-expressed as a leading part followed by a `flatMap`
    that prefixes each subsequent part with the separator. Bridges `List.intercalate`
    (whose direct recursion is awkward) to the `matchStar` iteration shape. -/
theorem intercalate_cons_flatMap {α : Type _} (sepL : List α) (a : List α)
    (rest : List (List α)) :
    sepL.intercalate (a :: rest) = a ++ rest.flatMap (fun p => sepL ++ p) := by
  induction rest generalizing a with
  | nil => simp [List.intercalate_singleton]
  | cons p ps ih =>
    rw [List.intercalate_cons_cons, ih p, List.flatMap_cons]
    simp [List.append_assoc]

/-- **Star bridge.** With a non-empty separator `sepL`, the `(sep item)*` tail loop
    (`matchStar`) reaches remainder `r₂` after `k` further items iff `cs` decomposes as
    `k` separator-prefixed parts (each item-matching via `Pitem`) followed by `r₂`. The
    non-empty-`sepL` hypothesis makes each iteration consume ≥ 1 char, so `sf ≥ cs.length`
    is always enough iteration fuel — the statement is quantified over all such `sf`. Proved
    by induction on `sf`. -/
theorem matchStar_iter (matchItem : List Char → List (CaptureMap × List Char))
    (sepL : List Char) (hsepL : sepL ≠ [])
    (Pitem : List Char → Prop)
    (hitem : ∀ cs r₂, (∃ m, (m, r₂) ∈ matchItem cs) ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ Pitem r₁) :
    ∀ sf cs r₂ k, cs.length ≤ sf →
      ((∃ m, (m, r₂, k) ∈ matchStar matchItem sepL sf cs) ↔
        ∃ parts : List (List Char), parts.length = k ∧
          cs = parts.flatMap (fun p => sepL ++ p) ++ r₂ ∧ (∀ p ∈ parts, Pitem p)) := by
  intro sf
  induction sf with
  | zero =>
    intro cs r₂ k hlen
    have hcs : cs = [] := by cases cs with | nil => rfl | cons a t => simp at hlen
    subst hcs
    simp only [matchStar, List.mem_singleton]
    constructor
    · rintro ⟨m, heq⟩
      simp only [Prod.mk.injEq] at heq
      exact ⟨[], heq.2.2.symm, by simp [heq.2.1], by simp⟩
    · rintro ⟨parts, hlenk, hcs, _⟩
      have hcs' := hcs.symm
      have hpe : parts = [] ∧ r₂ = [] := by
        rw [List.append_eq_nil_iff] at hcs'
        refine ⟨?_, hcs'.2⟩
        cases parts with
        | nil => rfl
        | cons p ps =>
          exfalso
          simp only [List.flatMap_cons] at hcs'
          have := hcs'.1
          rw [List.append_eq_nil_iff, List.append_eq_nil_iff] at this
          exact hsepL this.1.1
      obtain ⟨hp, hr⟩ := hpe; subst hp; subst hr; simp at hlenk
      exact ⟨[], by simp [← hlenk]⟩
  | succ sf' ih =>
    intro cs r₂ k hlen
    have hseplen : 1 ≤ sepL.length := by
      cases sepL with | nil => exact absurd rfl hsepL | cons a t => simp
    simp only [matchStar, List.mem_cons]
    constructor
    · rintro ⟨m, hmem⟩
      cases hmem with
      | inl heq =>
        simp only [Prod.mk.injEq] at heq
        exact ⟨[], heq.2.2.symm, by simp [heq.2.1], by simp⟩
      | inr hmore =>
        by_cases hpre : sepL.isPrefixOf cs = true
        · rw [if_pos hpre] at hmore
          rw [List.mem_flatMap] at hmore
          obtain ⟨⟨m1, r1⟩, hm1, hm2⟩ := hmore
          rw [List.mem_map] at hm2
          obtain ⟨⟨m2, r2', k'⟩, hk2, heq⟩ := hm2
          simp only [Prod.mk.injEq] at heq
          have hcs1 : cs = sepL ++ cs.drop sepL.length := by
            obtain ⟨t, ht⟩ := List.isPrefixOf_iff_prefix.mp hpre
            rw [← ht]; simp
          obtain ⟨rHead, hcs1eq, hPhead⟩ := (hitem (cs.drop sepL.length) r1).mp ⟨m1, hm1⟩
          have hr1len : r1.length ≤ sf' := by
            have h1 : (cs.drop sepL.length).length ≤ sf' := by rw [List.length_drop]; omega
            have hle : r1.length ≤ (cs.drop sepL.length).length := by rw [hcs1eq]; simp
            omega
          obtain ⟨parts', hlen', hr1eq, hPall⟩ := (ih r1 r2' k' hr1len).mp ⟨m2, hk2⟩
          refine ⟨rHead :: parts', ?_, ?_, ?_⟩
          · simp [hlen', ← heq.2.2]
          · rw [← heq.2.1, List.flatMap_cons, hcs1, hcs1eq, hr1eq]; simp [List.append_assoc]
          · intro p hp
            rw [List.mem_cons] at hp
            cases hp with | inl h => subst h; exact hPhead | inr h => exact hPall p h
        · rw [Bool.not_eq_true] at hpre
          rw [if_neg (by rw [hpre]; simp)] at hmore
          simp at hmore
    · rintro ⟨parts, hlenk, hcs, hPall⟩
      cases parts with
      | nil =>
        simp at hlenk
        simp only [List.flatMap_nil, List.nil_append] at hcs
        exact ⟨[], Or.inl (by simp [← hlenk, hcs])⟩
      | cons pHead parts' =>
        rw [List.flatMap_cons] at hcs
        have hpre : sepL.isPrefixOf cs = true := by
          rw [List.isPrefixOf_iff_prefix]
          exact ⟨pHead ++ (parts'.flatMap (fun p => sepL ++ p) ++ r₂),
            by rw [hcs]; simp [List.append_assoc]⟩
        have hdrop : cs.drop sepL.length = pHead ++ (parts'.flatMap (fun p => sepL ++ p) ++ r₂) := by
          rw [hcs]; simp [List.append_assoc]
        obtain ⟨m1, hm1⟩ :=
          (hitem (cs.drop sepL.length) (parts'.flatMap (fun p => sepL ++ p) ++ r₂)).mpr
            ⟨pHead, hdrop, hPall pHead (by simp)⟩
        have hr1len : (parts'.flatMap (fun p => sepL ++ p) ++ r₂).length ≤ sf' := by
          have hcl : cs.length =
              sepL.length + pHead.length + (parts'.flatMap (fun p => sepL ++ p) ++ r₂).length := by
            rw [hcs]; simp [List.append_assoc]; omega
          omega
        obtain ⟨m2, hm2⟩ :=
          (ih (parts'.flatMap (fun p => sepL ++ p) ++ r₂) r₂ parts'.length hr1len).mpr
            ⟨parts', rfl, rfl, fun p hp => hPall p (by simp [hp])⟩
        refine ⟨m1 ++ m2, Or.inr ?_⟩
        rw [if_pos hpre, List.mem_flatMap]
        refine ⟨(m1, parts'.flatMap (fun p => sepL ++ p) ++ r₂), hm1, ?_⟩
        rw [List.mem_map]
        exact ⟨(m2, r₂, parts'.length), hm2, by simp [← hlenk]⟩

/-- **Rep loop bridge.** `matchRep` (one leading item then the `matchStar` tail) reaches
    remainder `r₂` after `n` items iff `cs` is a non-empty `parts` list (each item-matching)
    intercalated by `sepL`, followed by `r₂`, with `parts.length = n`. Combines the leading
    `hitem` application with `matchStar_iter` for the tail, using `cs.length` as the (always
    sufficient) iteration fuel. -/
theorem matchRep_iter (matchItem : List Char → List (CaptureMap × List Char))
    (sepL : List Char) (hsepL : sepL ≠ [])
    (Pitem : List Char → Prop)
    (hitem : ∀ cs r₂, (∃ m, (m, r₂) ∈ matchItem cs) ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ Pitem r₁) :
    ∀ cs r₂ n, (∃ m, (m, r₂, n) ∈ matchRep matchItem sepL cs) ↔
      ∃ parts : List (List Char), parts ≠ [] ∧ parts.length = n ∧
        cs = sepL.intercalate parts ++ r₂ ∧ (∀ p ∈ parts, Pitem p) := by
  intro cs r₂ n
  simp only [matchRep]
  constructor
  · rintro ⟨m, hmem⟩
    rw [List.mem_flatMap] at hmem
    obtain ⟨⟨m1, r1⟩, hm1, hm2⟩ := hmem
    rw [List.mem_map] at hm2
    obtain ⟨⟨m2, r2', k⟩, hk, heq⟩ := hm2
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rHead, hcs1, hPhead⟩ := (hitem cs r1).mp ⟨m1, hm1⟩
    have hr1len : r1.length ≤ cs.length := by rw [hcs1]; simp
    obtain ⟨tailParts, hlen, hr1eq, hPall⟩ :=
      (matchStar_iter matchItem sepL hsepL Pitem hitem cs.length r1 r2' k hr1len).mp ⟨m2, hk⟩
    refine ⟨rHead :: tailParts, by simp, ?_, ?_, ?_⟩
    · simp [hlen, ← heq.2.2]
    · rw [intercalate_cons_flatMap, hcs1, hr1eq, ← heq.2.1, List.append_assoc]
    · intro p hp
      rw [List.mem_cons] at hp
      cases hp with | inl h => subst h; exact hPhead | inr h => exact hPall p h
  · rintro ⟨parts, hne, hlen, hcs, hPall⟩
    cases parts with
    | nil => exact absurd rfl hne
    | cons pHead tailParts =>
      rw [intercalate_cons_flatMap] at hcs
      obtain ⟨m1, hm1⟩ := (hitem cs (tailParts.flatMap (fun p => sepL ++ p) ++ r₂)).mpr
        ⟨pHead, by rw [hcs, List.append_assoc], hPall pHead (by simp)⟩
      have hr1len : (tailParts.flatMap (fun p => sepL ++ p) ++ r₂).length ≤ cs.length := by
        rw [hcs]; simp [List.append_assoc]
      obtain ⟨m2, hm2⟩ :=
        (matchStar_iter matchItem sepL hsepL Pitem hitem cs.length
          (tailParts.flatMap (fun p => sepL ++ p) ++ r₂) r₂ tailParts.length hr1len).mpr
          ⟨tailParts, rfl, rfl, fun p hp => hPall p (by simp [hp])⟩
      refine ⟨m1 ++ m2, ?_⟩
      rw [List.mem_flatMap]
      refine ⟨(m1, tailParts.flatMap (fun p => sepL ++ p) ++ r₂), hm1, ?_⟩
      rw [List.mem_map]
      exact ⟨(m2, r₂, tailParts.length), hm2, by simp [← hlen]⟩

/-- The `rep` symbol's count-bound test as a `Bool` (`lo ≤ n` and, if `hi = some h`, `n ≤ h`),
    matching the `filterMap` guard in `matchSym`'s `rep` case. -/
def inBounds (lo : Nat) (hi : Option Nat) (n : Nat) : Bool :=
  lo ≤ n && (match hi with | none => true | some h => n ≤ h)

theorem inBounds_iff (lo : Nat) (hi : Option Nat) (n : Nat) :
    inBounds lo hi n = true ↔ (lo ≤ n ∧ ∀ h, hi = some h → n ≤ h) := by
  unfold inBounds; rw [Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2⟩; refine ⟨by simpa using h1, ?_⟩; intro h hh; subst hh; simpa using h2
  · rintro ⟨h1, h2⟩; refine ⟨by simpa using h1, ?_⟩
    cases hi with | none => simp | some h => simp; exact h2 h rfl

/-- Transport `List.intercalate` at the `List Char` level to `String.intercalate` on the
    `String.ofList`-images of the parts. -/
theorem ofList_intercalate (sep : String) (parts : List (List Char)) :
    String.ofList (sep.toList.intercalate parts)
      = String.intercalate sep (parts.map String.ofList) := by
  rw [← String.toList_inj, String.toList_ofList, String.toList_intercalate]
  congr 1; rw [List.map_map]; simp [String.toList_ofList, Function.comp]

/-- The `matchSym` `rep` count `filterMap` reaches remainder `r₂` iff some in-bounds count `n`
    is reachable in the underlying `matchRep` list. Peels the count-key capture and the bound
    guard off the `filterMap`. -/
theorem repFilter_mem (base : String) (lo : Nat) (hi : Option Nat) (r₂ : List Char)
    (L : List (CaptureMap × List Char × Nat)) :
    (∃ m, (m, r₂) ∈ L.filterMap (fun (x : CaptureMap × List Char × Nat) =>
        if lo ≤ x.2.2 && (match hi with | none => true | some h => x.2.2 ≤ h)
        then some ((base ++ "#count", toString x.2.2) :: x.1, x.2.1) else none))
      ↔ ∃ n, (∃ m', (m', r₂, n) ∈ L) ∧ inBounds lo hi n = true := by
  constructor
  · rintro ⟨m, hmem⟩
    rw [List.mem_filterMap] at hmem
    obtain ⟨⟨m', rem, n⟩, hIn, heq⟩ := hmem
    simp only at heq
    by_cases hc : inBounds lo hi n = true
    · unfold inBounds at hc; rw [if_pos hc] at heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      exact ⟨n, ⟨m', by rw [← heq.2]; exact hIn⟩, by unfold inBounds; exact hc⟩
    · unfold inBounds at hc; rw [if_neg hc] at heq; simp at heq
  · rintro ⟨n, ⟨m', hIn⟩, hb⟩
    refine ⟨(base ++ "#count", toString n) :: m', ?_⟩
    rw [List.mem_filterMap]
    refine ⟨(m', r₂, n), hIn, ?_⟩
    unfold inBounds at hb; rw [if_pos hb]

/-- A `String` is `""` iff its char list is empty — packaged for extracting `sep.toList ≠ []`
    from the `sep ≠ ""` conjunct of `Sym.repOk`. -/
theorem toList_ne_nil_of_ne (sep : String) (h : sep ≠ "") : sep.toList ≠ [] := by
  intro hc; apply h; rw [← String.toList_inj]; simpa using hc

/-- **Rep bridge.** Given the item's bridge at the SAME fuel `q`/`fuel` (`hitem`, universally
    quantified over the input/remainder so `matchStar` can re-apply it to each tail position),
    the separated-repetition symbol's reachable remainders match its `matchesRep` denotation
    (the `parts`-list existential). This is the `rep` analogue of `seq_iter`/`prod_iter`: it
    threads the sub-symbol bridge through the `item (sep item)*` loop and the count filter.
    Requires `hok : (Sym.rep …).repOk = true` — the non-empty separator and `1 ≤ lo` under
    which `matchRep`/`matchStar` provably reach exactly the denotation's `parts` witnesses. -/
theorem rep_iter (g : Grammar) (q : String) (fuel : Nat) (sep : String) (item : Sym)
    (lo : Nat) (hi : Option Nat) (cs r₂ : List Char)
    (hok : (Sym.rep sep item lo hi).repOk = true)
    (hitem : ∀ cs r₂, (∃ m, (m, r₂) ∈ matchSym g q fuel item cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSym g fuel item (String.ofList r₁)) :
    (∃ m, (m, r₂) ∈ matchSym g q fuel (Sym.rep sep item lo hi) cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSym g fuel (Sym.rep sep item lo hi) (String.ofList r₁) := by
  -- Extract `sep ≠ ""` and `1 ≤ lo` from the three-way `&&` `repOk`.
  rw [show (Sym.rep sep item lo hi).repOk
      = (decide (sep ≠ "") && decide (1 ≤ lo) && item.repOk) from rfl] at hok
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨hsep, hlo⟩, _⟩ := hok
  have hsepL : sep.toList ≠ [] := toList_ne_nil_of_ne sep hsep
  simp only [matchSym, matchesSym]
  constructor
  · intro hmem
    obtain ⟨n, hex, hb⟩ :=
      (repFilter_mem (item.refName?.getD q) lo hi r₂
        (matchRep (fun cs' => matchSym g q fuel item cs') sep.toList cs)).mp hmem
    rw [inBounds_iff] at hb
    obtain ⟨parts, hne, hlenn, hcs, hPall⟩ :=
      (matchRep_iter (fun cs' => matchSym g q fuel item cs') sep.toList hsepL
        (fun r₁ => matchesSym g fuel item (String.ofList r₁)) hitem cs r₂ n).mp hex
    refine ⟨sep.toList.intercalate parts, hcs, parts.map String.ofList, ?_, ?_, ?_, ?_⟩
    · rw [List.length_map, hlenn]; exact hb.1
    · intro h hh; rw [List.length_map, hlenn]; exact hb.2 h hh
    · intro p hp
      rw [List.mem_map] at hp
      obtain ⟨pl, hpl, hpe⟩ := hp; rw [← hpe]; exact hPall pl hpl
    · exact ofList_intercalate sep parts
  · rintro ⟨r₁, hcs, sparts, hslo, hshi, hPall, hint⟩
    -- `sparts ≠ []` because `lo ≤ sparts.length` and `1 ≤ lo`.
    have hspne : sparts ≠ [] := by
      intro hnil; rw [hnil] at hslo; simp at hslo; omega
    refine (repFilter_mem (item.refName?.getD q) lo hi r₂
      (matchRep (fun cs' => matchSym g q fuel item cs') sep.toList cs)).mpr ?_
    refine ⟨sparts.length, ?_, by rw [inBounds_iff]; exact ⟨hslo, hshi⟩⟩
    refine (matchRep_iter (fun cs' => matchSym g q fuel item cs') sep.toList hsepL
      (fun r₁ => matchesSym g fuel item (String.ofList r₁)) hitem cs r₂ sparts.length).mpr ?_
    refine ⟨sparts.map String.toList, ?_, by rw [List.length_map], ?_, ?_⟩
    · intro hnil; apply hspne; simpa using hnil
    · have hr1 : r₁ = sep.toList.intercalate (sparts.map String.toList) := by
        have := congrArg String.toList hint
        rw [String.toList_ofList, String.toList_intercalate] at this
        exact this
      rw [hcs, hr1]
    · intro p hp
      rw [List.mem_map] at hp
      obtain ⟨s, hs, hpe⟩ := hp
      rw [← hpe, String.ofList_toList]; exact hPall s hs

-- sym by lexicographic (fuel, sym) induction: fuel drops for `ref`, sym-structure drops for
-- `rep` (whose `item` is matched at the SAME fuel). q universally quantified so the ref case
-- can re-instantiate it; cs/r₂ left un-intro'd so `induction sym` generalizes them for `rep`.
theorem sym_iter (g : Grammar) (hg : g.repOk = true) :
    ∀ fuel (q : String) sym, sym.repOk = true → ∀ cs r₂,
    (∃ m, (m, r₂) ∈ matchSym g q fuel sym cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSym g fuel sym (String.ofList r₁) := by
  intro fuel
  induction fuel with
  | zero =>
    intro q sym
    induction sym with
    | lit l => intro _ cs r₂; exact lit_leaf g q 0 l cs r₂
    | term tok ls => intro _ cs r₂; exact term_leaf g q 0 tok ls cs r₂
    | rep sep item lo hi ihitem =>
      intro hok cs r₂
      have hitemok : item.repOk = true := by
        rw [show (Sym.rep sep item lo hi).repOk
            = (decide (sep ≠ "") && decide (1 ≤ lo) && item.repOk) from rfl] at hok
        rw [Bool.and_eq_true, Bool.and_eq_true] at hok; exact hok.2
      exact rep_iter g q 0 sep item lo hi cs r₂ hok (ihitem hitemok)
    | ref name =>
      intro _ cs r₂
      simp only [matchSym, matchesSym, List.not_mem_nil, exists_false]
      simp
  | succ fuel ih =>
    intro q sym
    induction sym with
    | lit l => intro _ cs r₂; exact lit_leaf g q (fuel+1) l cs r₂
    | term tok ls => intro _ cs r₂; exact term_leaf g q (fuel+1) tok ls cs r₂
    | rep sep item lo hi ihitem =>
      intro hok cs r₂
      have hitemok : item.repOk = true := by
        rw [show (Sym.rep sep item lo hi).repOk
            = (decide (sep ≠ "") && decide (1 ≤ lo) && item.repOk) from rfl] at hok
        rw [Bool.and_eq_true, Bool.and_eq_true] at hok; exact hok.2
      exact rep_iter g q (fuel+1) sep item lo hi cs r₂ hok (ihitem hitemok)
    | ref name =>
      intro _ cs r₂
      have hprod : ∀ (q' : String) p, p.alts.all (fun alt => alt.all (fun it => it.sym.repOk)) = true →
          ∀ cs r₂, (∃ m, (m, r₂) ∈ matchProd g q' fuel p cs)
            ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesProd g fuel p (String.ofList r₁) := by
        intro q' p hpok cs r₂
        exact prod_iter g q' fuel p cs r₂ hpok
          (seq_iter g q' fuel (fun sym hsymok cs r₂ => ih q' sym hsymok cs r₂))
      simp only [matchSym, matchesSym]
      cases hp : g.prod? name with
      | none => simp
      | some p =>
        have hpok : p.alts.all (fun alt => alt.all (fun it => it.sym.repOk)) = true := by
          unfold Grammar.repOk at hg
          rw [List.all_eq_true] at hg
          have hmem : p ∈ g.prods := by
            unfold Grammar.prod? at hp; exact List.mem_of_find?_eq_some hp
          simpa using hg p hmem
        simp only []
        rw [← hprod name p hpok cs r₂]
        constructor
        · rintro ⟨m, hmem⟩
          rw [List.mem_map] at hmem
          obtain ⟨⟨m0, r0⟩, hmem0, heq⟩ := hmem
          simp only [Prod.mk.injEq] at heq
          exact ⟨m0, by rw [← heq.2]; exact hmem0⟩
        · rintro ⟨m, hmem⟩
          exact ⟨_, List.mem_map.mpr ⟨(m, r₂), hmem, rfl⟩⟩

-- top-level bridges (all under the grammar-level `hg : g.repOk = true`)
theorem matchSeq_iter (g : Grammar) (hg : g.repOk = true) (q : String) (fuel : Nat) :
    ∀ seq, seq.all (fun it => it.sym.repOk) = true → ∀ cs r₂,
      (∃ m, (m, r₂) ∈ matchSeq g q fuel seq cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSeq g fuel seq (String.ofList r₁) :=
  seq_iter g q fuel (fun sym hsymok cs r₂ => sym_iter g hg fuel q sym hsymok cs r₂)

theorem matchProd_iter (g : Grammar) (hg : g.repOk = true) (q : String) (fuel : Nat)
    (p : Production) (cs r₂ : List Char)
    (hpok : p.alts.all (fun alt => alt.all (fun it => it.sym.repOk)) = true) :
    (∃ m, (m, r₂) ∈ matchProd g q fuel p cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesProd g fuel p (String.ofList r₁) :=
  prod_iter g q fuel p cs r₂ hpok (matchSeq_iter g hg q fuel)

theorem decodeSome_iff_IsWf (g : Grammar) (hg : g.repOk = true) (s : String) :
    (decode g s).isSome = true ↔ IsWf g s := by
  unfold decode IsWf
  cases hstart : g.startProd? with
  | none => simp
  | some p =>
    have hpok : p.alts.all (fun alt => alt.all (fun it => it.sym.repOk)) = true := by
      unfold Grammar.repOk at hg
      rw [List.all_eq_true] at hg
      have hmem : p ∈ g.prods := by
        unfold Grammar.startProd? Grammar.prod? at hstart
        exact List.mem_of_find?_eq_some hstart
      simpa using hg p hmem
    simp only [Option.isSome_map]
    -- head?.isSome of the filtered list ↔ ∃ elem with empty remainder
    have hhead : (((matchProd g "" g.prods.length p s.toList).filter
        (fun x => x.2.isEmpty)).head?).isSome = true
        ↔ ∃ m, (m, ([] : List Char)) ∈ matchProd g "" g.prods.length p s.toList := by
      have hne : ∀ L : List (CaptureMap × List Char), L.head?.isSome = true ↔ ∃ x, x ∈ L := by
        intro L; cases L with
        | nil => simp
        | cons a t => simp
      rw [hne]
      constructor
      · rintro ⟨x, hx⟩
        rw [List.mem_filter] at hx
        refine ⟨x.1, ?_⟩
        have hx2 : x.2 = [] := by
          have := hx.2; simp only [List.isEmpty_iff] at this; exact this
        rw [← hx2]; exact hx.1
      · rintro ⟨m, hmem⟩
        exact ⟨(m, []), by rw [List.mem_filter]; exact ⟨hmem, by simp⟩⟩
    rw [hhead, matchProd_iter g hg "" g.prods.length p s.toList [] hpok]
    constructor
    · rintro ⟨r₁, hcs, hd⟩
      have : r₁ = s.toList := by simpa using hcs.symm
      rw [this, String.ofList_toList] at hd; exact hd
    · intro hd
      exact ⟨s.toList, by simp, by rw [String.ofList_toList]; exact hd⟩

/-- `IsWf` is decidable — the executable, provably-correct validator, obtained DIRECTLY from
    the total `decode` (`(decode g s).isSome` is a decidable `Bool` test) via the roundtrip.
    This is the sole consumer of well-formedness decidability; because `decode` already exists
    (it drives `computeValue`/`envOf`), no separate boolean recognizer walk is needed.

    Requires `hg : g.repOk = true` — the roundtrip only holds for grammars in the
    decoder-agreeing class (non-empty rep separators, `1 ≤ lo`). Every DSL-generated grammar
    satisfies this by construction (and discharges it by `decide`), so downstream consumers
    supply the proof at the concrete grammar. Hence a `def` (not an `instance`): the
    decidability is conditional on `hg`. -/
@[reducible] def decIsWf (g : Grammar) (hg : g.repOk = true) : DecidablePred (IsWf g) := fun s =>
  decidable_of_iff ((decode g s).isSome = true) (decodeSome_iff_IsWf g hg s)

end Triptych
