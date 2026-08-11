import Triptych.Theorems.DecodeLemmas
import Triptych.Theorems.Roundtrip

/-!
# Capture-preserving repetition lemmas

`Roundtrip` characterizes the language recognized by separated repetitions while intentionally
quantifying capture maps away. External-parser agreement also needs the repeated captures
themselves. These lemmas retain the concatenated per-item capture maps.
-/

namespace Triptych

private theorem flatMap_map_eq {α β γ : Type} (xs : List α)
    (f : α → β) (g : β → List γ) :
    (xs.map f).flatMap g = xs.flatMap (fun x => g (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- Exact captures produced by the `(sep item)*` tail loop. -/
theorem matchStar_capture_iter
    (matchItem : List Char → List (CaptureMap × List Char))
    (sepL : List Char) (hsepL : sepL ≠ [])
    (Pitem : List Char → Prop) (captures : List Char → CaptureMap)
    (hitem :
      ∀ cs r m,
        (m, r) ∈ matchItem cs ↔
          ∃ piece, cs = piece ++ r ∧ Pitem piece ∧ m = captures piece) :
    ∀ sf cs r k m, cs.length ≤ sf →
      ((m, r, k) ∈ matchStar matchItem sepL sf cs ↔
        ∃ parts : List (List Char),
          parts.length = k ∧
          cs = parts.flatMap (fun part => sepL ++ part) ++ r ∧
          (∀ part ∈ parts, Pitem part) ∧
          m = parts.flatMap captures) := by
  intro sf
  induction sf with
  | zero =>
      intro cs r k m hlen
      have hcs : cs = [] := by
        cases cs with
        | nil => rfl
        | cons c cs => simp at hlen
      subst cs
      simp only [matchStar, List.mem_singleton]
      constructor
      · intro heq
        simp only [Prod.mk.injEq] at heq
        exact ⟨[], heq.2.2.symm, by simp [heq.2.1], by simp, heq.1⟩
      · rintro ⟨parts, hlength, hparts, _, hm⟩
        have hpartsNil : parts = [] := by
          cases parts with
          | nil => rfl
          | cons part parts =>
              have hflat :
                  (sepL ++ part) ++ parts.flatMap (fun part => sepL ++ part) = [] := by
                apply (List.append_eq_nil_iff.mp hparts.symm).1
              have hnil : sepL ++ part = [] :=
                (List.append_eq_nil_iff.mp hflat).1
              exact (hsepL (List.append_eq_nil_iff.mp hnil).1).elim
        subst parts
        simp at hlength hm hparts
        subst k
        subst m
        subst r
        rfl
  | succ sf ih =>
      intro cs r k m hlen
      have hsepLength : 1 ≤ sepL.length := by
        cases sepL with
        | nil => exact (hsepL rfl).elim
        | cons c cs => simp
      simp only [matchStar, List.mem_cons]
      constructor
      · intro hmem
        rcases hmem with hstop | hmore
        · simp only [Prod.mk.injEq] at hstop
          exact ⟨[], hstop.2.2.symm, by simp [hstop.2.1], by simp, hstop.1⟩
        · by_cases hpre : sepL.isPrefixOf cs = true
          · rw [if_pos hpre] at hmore
            rw [List.mem_flatMap] at hmore
            obtain ⟨⟨m₁, r₁⟩, hm₁, htail⟩ := hmore
            rw [List.mem_map] at htail
            obtain ⟨⟨m₂, r₂, k₂⟩, hm₂, heq⟩ := htail
            simp only [Prod.mk.injEq] at heq
            obtain ⟨piece, hpiece, hvalid, hcaptures⟩ :=
              (hitem (cs.drop sepL.length) r₁ m₁).mp hm₁
            have hprefix : cs = sepL ++ cs.drop sepL.length := by
              obtain ⟨tail, rfl⟩ := List.isPrefixOf_iff_prefix.mp hpre
              simp
            have hr₁Length : r₁.length ≤ sf := by
              have hdrop : (cs.drop sepL.length).length ≤ sf := by
                rw [List.length_drop]
                omega
              rw [hpiece] at hdrop
              simp only [List.length_append] at hdrop
              omega
            obtain ⟨parts, hpartsLength, hrest, hall, hm₂'⟩ :=
              (ih r₁ r₂ k₂ m₂ hr₁Length).mp hm₂
            refine ⟨piece :: parts, ?_, ?_, ?_, ?_⟩
            · simp [hpartsLength, ← heq.2.2]
            · rw [← heq.2.1, List.flatMap_cons, hprefix, hpiece, hrest]
              simp [List.append_assoc]
            · intro part hpart
              simp only [List.mem_cons] at hpart
              rcases hpart with rfl | hpart
              · exact hvalid
              · exact hall part hpart
            · rw [← heq.1, hcaptures, hm₂']
              simp
          · rw [Bool.not_eq_true] at hpre
            rw [if_neg (by rw [hpre]; simp)] at hmore
            simp at hmore
      · rintro ⟨parts, hpartsLength, hcs, hall, hm⟩
        cases parts with
        | nil =>
            simp at hpartsLength hm hcs
            subst k
            subst m
            subst r
            exact Or.inl rfl
        | cons piece parts =>
            rw [List.flatMap_cons] at hcs hm
            have hpre : sepL.isPrefixOf cs = true := by
              rw [List.isPrefixOf_iff_prefix]
              exact ⟨piece ++ (parts.flatMap (fun part => sepL ++ part) ++ r),
                by rw [hcs]; simp [List.append_assoc]⟩
            have hdrop :
                cs.drop sepL.length =
                  piece ++ (parts.flatMap (fun part => sepL ++ part) ++ r) := by
              rw [hcs]
              simp [List.append_assoc]
            have hm₁ :
                (captures piece, parts.flatMap (fun part => sepL ++ part) ++ r) ∈
                  matchItem (cs.drop sepL.length) :=
              (hitem _ _ _).mpr ⟨piece, hdrop, hall piece (by simp), rfl⟩
            have htailLength :
                (parts.flatMap (fun part => sepL ++ part) ++ r).length ≤ sf := by
              have htotal :
                  cs.length =
                    sepL.length + piece.length +
                      (parts.flatMap (fun part => sepL ++ part) ++ r).length := by
                rw [hcs]
                simp only [List.length_append]
                omega
              omega
            have hm₂ :
                (parts.flatMap captures, r, parts.length) ∈
                  matchStar matchItem sepL sf
                    (parts.flatMap (fun part => sepL ++ part) ++ r) :=
              (ih _ _ _ _ htailLength).mpr
                ⟨parts, rfl, rfl, fun part hpart => hall part (by simp [hpart]), rfl⟩
            right
            rw [if_pos hpre, List.mem_flatMap]
            refine ⟨(captures piece, parts.flatMap (fun part => sepL ++ part) ++ r),
              hm₁, ?_⟩
            rw [List.mem_map]
            refine ⟨(parts.flatMap captures, r, parts.length), hm₂, ?_⟩
            simp only [Prod.mk.injEq]
            simp [hm]
            simpa [Nat.add_comm] using hpartsLength

/-- Exact captures produced by `item (sep item)*`. -/
theorem matchRep_capture_iter
    (matchItem : List Char → List (CaptureMap × List Char))
    (sepL : List Char) (hsepL : sepL ≠ [])
    (Pitem : List Char → Prop) (captures : List Char → CaptureMap)
    (hitem :
      ∀ cs r m,
        (m, r) ∈ matchItem cs ↔
          ∃ piece, cs = piece ++ r ∧ Pitem piece ∧ m = captures piece)
    (cs r : List Char) (n : Nat) (m : CaptureMap) :
    (m, r, n) ∈ matchRep matchItem sepL cs ↔
      ∃ parts : List (List Char),
        parts ≠ [] ∧ parts.length = n ∧
        cs = sepL.intercalate parts ++ r ∧
        (∀ part ∈ parts, Pitem part) ∧
        m = parts.flatMap captures := by
  simp only [matchRep]
  constructor
  · intro hmem
    rw [List.mem_flatMap] at hmem
    obtain ⟨⟨m₁, r₁⟩, hm₁, htail⟩ := hmem
    rw [List.mem_map] at htail
    obtain ⟨⟨m₂, r₂, k⟩, hm₂, heq⟩ := htail
    simp only [Prod.mk.injEq] at heq
    obtain ⟨piece, hpiece, hvalid, hcaptures⟩ := (hitem cs r₁ m₁).mp hm₁
    have hr₁Length : r₁.length ≤ cs.length := by
      rw [hpiece]
      simp
    obtain ⟨parts, hpartsLength, hrest, hall, hm₂'⟩ :=
      (matchStar_capture_iter matchItem sepL hsepL Pitem captures hitem
        cs.length r₁ r₂ k m₂ hr₁Length).mp hm₂
    refine ⟨piece :: parts, by simp, ?_, ?_, ?_, ?_⟩
    · simp [hpartsLength, ← heq.2.2]
    · rw [intercalate_cons_flatMap, hpiece, hrest, ← heq.2.1, List.append_assoc]
    · intro part hpart
      simp only [List.mem_cons] at hpart
      rcases hpart with rfl | hpart
      · exact hvalid
      · exact hall part hpart
    · rw [← heq.1, hcaptures, hm₂']
      simp
  · rintro ⟨parts, hne, hpartsLength, hcs, hall, hm⟩
    cases parts with
    | nil => exact (hne rfl).elim
    | cons piece parts =>
        rw [intercalate_cons_flatMap] at hcs
        have hm₁ :
            (captures piece, parts.flatMap (fun part => sepL ++ part) ++ r) ∈
              matchItem cs :=
          (hitem _ _ _).mpr
            ⟨piece, by rw [hcs, List.append_assoc], hall piece (by simp), rfl⟩
        have htailLength :
            (parts.flatMap (fun part => sepL ++ part) ++ r).length ≤ cs.length := by
          rw [hcs]
          simp [List.append_assoc]
        have hm₂ :
            (parts.flatMap captures, r, parts.length) ∈
              matchStar matchItem sepL cs.length
                (parts.flatMap (fun part => sepL ++ part) ++ r) :=
          (matchStar_capture_iter matchItem sepL hsepL Pitem captures hitem
            cs.length _ _ _ _ htailLength).mpr
              ⟨parts, rfl, rfl, fun part hpart => hall part (by simp [hpart]), rfl⟩
        rw [List.mem_flatMap]
        refine ⟨(captures piece, parts.flatMap (fun part => sepL ++ part) ++ r), hm₁, ?_⟩
        rw [List.mem_map]
        refine ⟨(parts.flatMap captures, r, parts.length), hm₂, ?_⟩
        simp only [Prod.mk.injEq]
        simp [hm]
        simpa [Nat.add_comm] using hpartsLength

/-- Exact count and item captures produced by a separated-repetition symbol. -/
theorem mem_matchSym_rep_capture_iff
    (g : Grammar) (q : String) (fuel : Nat) (sep : String) (item : Sym)
    (lo : Nat) (hi : Option Nat) (Pitem : List Char → Prop)
    (captures : List Char → CaptureMap)
    (hsep : sep ≠ "")
    (hitem :
      ∀ cs r m,
        (m, r) ∈ matchSym g q fuel item cs ↔
          ∃ piece, cs = piece ++ r ∧ Pitem piece ∧ m = captures piece)
    (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym g q fuel (Sym.rep sep item lo hi) cs ↔
      ∃ parts : List (List Char),
        parts ≠ [] ∧
        lo ≤ parts.length ∧
        (∀ upper, hi = some upper → parts.length ≤ upper) ∧
        cs = sep.toList.intercalate parts ++ r ∧
        (∀ part ∈ parts, Pitem part) ∧
        m =
          ((item.refName?.getD q ++ "#count", toString parts.length) ::
            parts.flatMap captures) := by
  have hsepL : sep.toList ≠ [] := toList_ne_nil_of_ne sep hsep
  simp only [matchSym]
  constructor
  · intro hmem
    rw [List.mem_filterMap] at hmem
    obtain ⟨⟨m', rem, n⟩, hrep, hout⟩ := hmem
    simp only at hout
    simp at hout
    have hupper : ∀ upper, hi = some upper → n ≤ upper := by
      intro upper hu
      subst hi
      simpa using hout.1.2
    obtain ⟨parts, hne, hlength, hcs, hall, hm'⟩ :=
      (matchRep_capture_iter
        (fun cs' => matchSym g q fuel item cs') sep.toList hsepL
        Pitem captures hitem cs rem n m').mp hrep
    refine ⟨parts, hne, ?_, ?_, ?_, hall, ?_⟩
    · simpa [hlength] using hout.1.1
    · intro upper hu
      simpa [hlength] using hupper upper hu
    · simpa [hout.2.2] using hcs
    · rw [← hout.2.1, hm', hlength]
      rfl
  · rintro ⟨parts, hne, hlo, hhi, hcs, hall, rfl⟩
    rw [List.mem_filterMap]
    have hrep :
        (parts.flatMap captures, r, parts.length) ∈
          matchRep (fun cs' => matchSym g q fuel item cs') sep.toList cs :=
      (matchRep_capture_iter
        (fun cs' => matchSym g q fuel item cs') sep.toList hsepL
        Pitem captures hitem cs r parts.length (parts.flatMap captures)).mpr
          ⟨parts, hne, rfl, hcs, hall, rfl⟩
    refine ⟨(parts.flatMap captures, r, parts.length), hrep, ?_⟩
    simp only
    cases hi with
    | none => simp [hlo]
    | some upper => simp [hlo, hhi upper rfl]

/-- String-level specialization of `mem_matchSym_rep_capture_iff`. -/
theorem mem_matchSym_rep_string_capture_iff
    (g : Grammar) (q : String) (fuel : Nat) (sep : String) (item : Sym)
    (lo : Nat) (hi : Option Nat) (Pitem : String → Prop)
    (captures : String → CaptureMap)
    (hsep : sep ≠ "")
    (hitem :
      ∀ cs r m,
        (m, r) ∈ matchSym g q fuel item cs ↔
          ∃ piece, cs = piece.toList ++ r ∧ Pitem piece ∧ m = captures piece)
    (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym g q fuel (Sym.rep sep item lo hi) cs ↔
      ∃ parts : List String,
        parts ≠ [] ∧
        lo ≤ parts.length ∧
        (∀ upper, hi = some upper → parts.length ≤ upper) ∧
        cs = (String.intercalate sep parts).toList ++ r ∧
        (∀ part ∈ parts, Pitem part) ∧
        m =
          ((item.refName?.getD q ++ "#count", toString parts.length) ::
            parts.flatMap captures) := by
  let Pchars : List Char → Prop := fun piece => Pitem (String.ofList piece)
  let captureChars : List Char → CaptureMap :=
    fun piece => captures (String.ofList piece)
  have hitemChars :
      ∀ cs r m,
        (m, r) ∈ matchSym g q fuel item cs ↔
          ∃ piece, cs = piece ++ r ∧ Pchars piece ∧ m = captureChars piece := by
    intro input rest itemCaptures
    rw [hitem]
    constructor
    · rintro ⟨piece, hinput, hvalid, hcaptures⟩
      exact ⟨piece.toList, hinput, by simpa [Pchars], by simpa [captureChars]⟩
    · rintro ⟨piece, hinput, hvalid, hcaptures⟩
      exact ⟨String.ofList piece, by simpa using hinput, hvalid, hcaptures⟩
  rw [mem_matchSym_rep_capture_iff g q fuel sep item lo hi Pchars captureChars
    hsep hitemChars cs r m]
  constructor
  · rintro ⟨parts, hne, hlo, hhi, hcs, hall, hm⟩
    refine ⟨parts.map String.ofList, by simpa, by simpa, ?_, ?_, ?_, ?_⟩
    · intro upper hu
      simpa using hhi upper hu
    · have hintercalate :
          sep.toList.intercalate parts =
            (String.intercalate sep (parts.map String.ofList)).toList := by
        have h := congrArg String.toList (ofList_intercalate sep parts)
        simpa only [String.toList_ofList] using h
      rw [hintercalate] at hcs
      exact hcs
    · intro part hpart
      rw [List.mem_map] at hpart
      obtain ⟨chars, hchars, rfl⟩ := hpart
      exact hall chars hchars
    · have hflat :
          (parts.map String.ofList).flatMap captures =
            parts.flatMap captureChars := by
        simpa [captureChars] using
          (flatMap_map_eq parts String.ofList captures)
      simpa [hflat] using hm
  · rintro ⟨parts, hne, hlo, hhi, hcs, hall, hm⟩
    refine ⟨parts.map String.toList, by simpa, by simpa, ?_, ?_, ?_, ?_⟩
    · intro upper hu
      simpa using hhi upper hu
    · simpa only [String.toList_intercalate] using hcs
    · intro chars hchars
      rw [List.mem_map] at hchars
      obtain ⟨part, hpart, rfl⟩ := hchars
      simpa [Pchars] using hall part hpart
    · have hflat :
          (parts.map String.toList).flatMap captureChars =
            parts.flatMap captures := by
        simpa [captureChars] using
          (flatMap_map_eq parts String.toList captureChars)
      simpa [hflat] using hm

end Triptych
