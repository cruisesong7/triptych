import Triptych.Architecture.Decode

/-!
# Exact decoder membership lemmas

Small structural facts about `matchSym` and `matchSeq` that preserve capture maps.
`Triptych.Theorems.Roundtrip` intentionally quantifies captures away when proving recognition
equivalence; external-parser bridges often need these stronger forms to recover the exact
components selected by `decode`.
-/

namespace Triptych

theorem mem_matchSym_term_iff (g : Grammar) (q : String) (fuel : Nat)
    (tok : TokClass) (ls : LenSpec) (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym g q fuel (Sym.term tok ls) cs ↔
      m = [] ∧ ∃ p, cs = p ++ r ∧ matchesTerm tok ls (String.ofList p) := by
  simp only [matchSym]
  constructor
  · intro hmem
    rw [List.mem_filterMap] at hmem
    obtain ⟨k, hk, hval⟩ := hmem
    by_cases hok : termPrefixOk tok ls cs k = true
    · rw [hok] at hval
      simp only [if_true, Option.some.injEq, Prod.mk.injEq] at hval
      refine ⟨hval.1.symm, cs.take k, ?_, ?_⟩
      · rw [← hval.2, List.take_append_drop]
      · unfold termPrefixOk at hok
        rw [Bool.and_eq_true] at hok
        exact of_decide_eq_true hok.2
    · rw [Bool.not_eq_true] at hok
      rw [hok] at hval
      simp at hval
  · rintro ⟨rfl, p, hcs, hden⟩
    rw [List.mem_filterMap]
    refine ⟨p.length, ?_, ?_⟩
    · rw [List.mem_range, hcs]
      simp only [List.length_append]
      omega
    · have hok : termPrefixOk tok ls cs p.length = true := by
        unfold termPrefixOk
        rw [Bool.and_eq_true]
        refine ⟨?_, ?_⟩
        · rw [decide_eq_true_eq, hcs]
          simp
        · rw [decide_eq_true_eq, hcs, List.take_left]
          exact hden
      rw [hok]
      simp
      rw [hcs, List.drop_left]

theorem mem_matchSym_lit_iff (g : Grammar) (q : String) (fuel : Nat) (l : String)
    (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym g q fuel (Sym.lit l) cs ↔
      m = [] ∧ cs = l.toList ++ r := by
  simp only [matchSym]
  by_cases h : l.toList.isPrefixOf cs = true
  · simp only [h, if_true, List.mem_singleton, Prod.mk.injEq]
    obtain ⟨t, rfl⟩ := List.isPrefixOf_iff_prefix.mp h
    simp
    intro
    exact eq_comm
  · rw [Bool.not_eq_true] at h
    simp [h]
    intro _ hcs
    subst cs
    have hp : l.toList.isPrefixOf (l.toList ++ r) = true :=
      List.isPrefixOf_iff_prefix.mpr ⟨r, rfl⟩
    rw [hp] at h
    simp at h

theorem mem_matchSeq_cons_required_iff (g : Grammar) (q : String) (fuel : Nat)
    (item : SymItem) (rest : Seq) (hopt : item.optional = false)
    (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSeq g q fuel (item :: rest) cs ↔
      ∃ m₁ mid m₂,
        (m₁, mid) ∈ matchSym g q fuel item.sym cs ∧
        (m₂, r) ∈ matchSeq g q fuel rest mid ∧
        m = m₁ ++ m₂ := by
  simp only [matchSeq, hopt, Bool.false_eq_true, if_false]
  constructor
  · intro hmem
    rw [List.mem_flatMap] at hmem
    obtain ⟨⟨m₁, mid⟩, hm₁, hrest⟩ := hmem
    rw [List.mem_map] at hrest
    obtain ⟨⟨m₂, r'⟩, hm₂, heq⟩ := hrest
    simp only [Prod.mk.injEq] at heq
    exact ⟨m₁, mid, m₂, hm₁, heq.2 ▸ hm₂, heq.1.symm⟩
  · rintro ⟨m₁, mid, m₂, hm₁, hm₂, rfl⟩
    rw [List.mem_flatMap]
    exact ⟨(m₁, mid), hm₁, List.mem_map.mpr ⟨(m₂, r), hm₂, rfl⟩⟩

theorem mem_matchSeq_cons_optional_iff (g : Grammar) (q : String) (fuel : Nat)
    (item : SymItem) (rest : Seq) (hopt : item.optional = true)
    (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSeq g q fuel (item :: rest) cs ↔
      (∃ m₁ mid m₂,
        (m₁, mid) ∈ matchSym g q fuel item.sym cs ∧
        (m₂, r) ∈ matchSeq g q fuel rest mid ∧
        m = m₁ ++ m₂) ∨
      (m, r) ∈ matchSeq g q fuel rest cs := by
  simp only [matchSeq, hopt, if_true, List.mem_append]
  constructor
  · rintro (hmem | hrest)
    · rw [List.mem_flatMap] at hmem
      obtain ⟨⟨m₁, mid⟩, hm₁, htail⟩ := hmem
      rw [List.mem_map] at htail
      obtain ⟨⟨m₂, r'⟩, hm₂, heq⟩ := htail
      simp only [Prod.mk.injEq] at heq
      exact Or.inl ⟨m₁, mid, m₂, hm₁, heq.2 ▸ hm₂, heq.1.symm⟩
    · exact Or.inr hrest
  · rintro (⟨m₁, mid, m₂, hm₁, hm₂, rfl⟩ | hrest)
    · left
      rw [List.mem_flatMap]
      exact ⟨(m₁, mid), hm₁, List.mem_map.mpr ⟨(m₂, r), hm₂, rfl⟩⟩
    · exact Or.inr hrest

theorem mem_matchSym_ref_iff (g : Grammar) (q : String) (fuel : Nat)
    (name : String) (p : Production) (hprod : g.prod? name = some p)
    (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym g q (fuel + 1) (Sym.ref name) cs ↔
      ∃ inner,
        (inner, r) ∈ matchProd g name fuel p cs ∧
        m =
          (if q.isEmpty then
            [(name, String.ofList (cs.take (cs.length - r.length)))]
          else
            [(name, String.ofList (cs.take (cs.length - r.length))),
              (q ++ "." ++ name, String.ofList (cs.take (cs.length - r.length)))]) ++
            inner := by
  rw [matchSym, hprod, List.mem_map]
  constructor
  · rintro ⟨⟨inner, r'⟩, hinner, heq⟩
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨hm, rfl⟩
    exact ⟨inner, hinner, hm.symm⟩
  · rintro ⟨inner, hinner, rfl⟩
    exact ⟨(inner, r), hinner, rfl⟩

theorem mem_matchSym_ref_single_term_qualified_iff (g : Grammar) (q : String) (fuel : Nat)
    (name prodName : String) (tok : TokClass) (ls : LenSpec)
    (hprod :
      g.prod? name =
        some (Production.mk prodName [[SymItem.mk (Sym.term tok ls) false]]))
    (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym g q (fuel + 1) (Sym.ref name) cs ↔
      ∃ p,
        m =
          (if q.isEmpty then
            [(name, String.ofList p)]
          else
            [(name, String.ofList p), (q ++ "." ++ name, String.ofList p)]) ∧
        cs = p ++ r ∧
        matchesTerm tok ls (String.ofList p) := by
  rw [matchSym, hprod]
  simp [matchProd, matchSeq, mem_matchSym_term_iff]
  constructor
  · rintro ⟨a, ⟨rfl, p, hcs, hden⟩, rfl⟩
    refine ⟨p, ?_, hcs, hden⟩
    simp [hcs]
  · rintro ⟨p, rfl, hcs, hden⟩
    refine ⟨[], ⟨rfl, p, hcs, hden⟩, ?_⟩
    simp [hcs]

theorem mem_matchSym_ref_single_term_iff (g : Grammar) (fuel : Nat)
    (name prodName : String) (tok : TokClass) (ls : LenSpec)
    (hprod :
      g.prod? name =
        some (Production.mk prodName [[SymItem.mk (Sym.term tok ls) false]]))
    (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym g "" (fuel + 1) (Sym.ref name) cs ↔
      ∃ p, m = [(name, String.ofList p)] ∧ cs = p ++ r ∧
        matchesTerm tok ls (String.ofList p) := by
  simpa using
    mem_matchSym_ref_single_term_qualified_iff g "" fuel name prodName tok ls hprod cs r m

theorem mem_matchProd_of_decode_eq_some {g : Grammar} {s : String} {m : CaptureMap}
    (h : decode g s = some m) :
    ∃ p, g.startProd? = some p ∧
      (m, []) ∈ matchProd g "" g.prods.length p s.toList := by
  unfold decode at h
  cases hstart : g.startProd? with
  | none => simp [hstart] at h
  | some p =>
      refine ⟨p, rfl, ?_⟩
      simp only [hstart] at h
      generalize hfull :
          List.filter (fun x => x.snd.isEmpty)
            (matchProd g "" g.prods.length p s.toList) = full at h
      cases full with
      | nil => simp at h
      | cons x xs =>
          rcases x with ⟨xm, xr⟩
          simp only [List.head?_cons, Option.map_some, Option.some.injEq] at h
          subst m
          have hxfilter :
              (xm, xr) ∈
                List.filter (fun x => x.snd.isEmpty)
                  (matchProd g "" g.prods.length p s.toList) := by
            rw [hfull]
            exact List.Mem.head xs
          rw [List.mem_filter] at hxfilter
          have hxrest : xr = [] := by
            simpa only [List.isEmpty_iff] using hxfilter.2
          simpa [hxrest] using hxfilter.1

end Triptych
