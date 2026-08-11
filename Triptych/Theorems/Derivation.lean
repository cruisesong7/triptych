import Triptych.Architecture.Derivation
import Triptych.Theorems.Coherence
import Triptych.Theorems.DecodeLemmas
import Triptych.Theorems.Roundtrip

/-!
# Structural derivation trees

Reusable combinators for generated typed derivation trees. A generated tree carries its
rendered text and exact capture map; these predicates state that the pair is produced by the
reference decoder for every following suffix. The suffix-polymorphic form composes directly
across sequences and repetitions.
-/

namespace Triptych

private theorem flatMap_map_eq {α : Type u} {β : Type v} {γ : Type w} (xs : List α)
    (f : α → β) (g : β → List γ) :
    (xs.map f).flatMap g = xs.flatMap (fun x => g (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- Exact symbol match, uniformly in the unconsumed suffix. -/
def SymMatch (g : Grammar) (qual : String) (fuel : Nat) (sym : Sym)
    (text : String) (captures : CaptureMap) : Prop :=
  ∀ suffix, (captures, suffix) ∈ matchSym g qual fuel sym (text.toList ++ suffix)

/-- Exact sequence match, uniformly in the unconsumed suffix. -/
def SeqMatch (g : Grammar) (qual : String) (fuel : Nat) (seq : Seq)
    (text : String) (captures : CaptureMap) : Prop :=
  ∀ suffix, (captures, suffix) ∈ matchSeq g qual fuel seq (text.toList ++ suffix)

/-- Exact production match, uniformly in the unconsumed suffix. -/
def ProdMatch (g : Grammar) (qual : String) (fuel : Nat) (prod : Production)
    (text : String) (captures : CaptureMap) : Prop :=
  ∀ suffix, (captures, suffix) ∈ matchProd g qual fuel prod (text.toList ++ suffix)

theorem symMatch_lit (g : Grammar) (qual : String) (fuel : Nat) (lit : String) :
    SymMatch g qual fuel (.lit lit) lit [] := by
  intro suffix
  rw [mem_matchSym_lit_iff]
  simp

theorem symMatch_term (g : Grammar) (qual : String) (fuel : Nat)
    (tok : TokClass) (lenSpec : LenSpec) (text : String)
    (hvalid : matchesTerm tok lenSpec text) :
    SymMatch g qual fuel (.term tok lenSpec) text [] := by
  intro suffix
  rw [mem_matchSym_term_iff]
  exact ⟨rfl, text.toList, rfl, by simpa⟩

theorem symMatch_ref (g : Grammar) (qual : String) (fuel : Nat)
    (name : String) (prod : Production) (hprod : g.prod? name = some prod)
    (text : String) (captures : CaptureMap)
    (hmatch : ProdMatch g name fuel prod text captures) :
    SymMatch g qual (fuel + 1) (.ref name) text
      (referenceCaptures qual name text ++ captures) := by
  intro suffix
  rw [mem_matchSym_ref_iff g qual fuel name prod hprod]
  refine ⟨captures, hmatch suffix, ?_⟩
  simp [referenceCaptures]

theorem seqMatch_nil (g : Grammar) (qual : String) (fuel : Nat) :
    SeqMatch g qual fuel [] "" [] := by
  intro suffix
  rw [mem_matchSeq_nil_iff]
  simp

theorem seqMatch_required (g : Grammar) (qual : String) (fuel : Nat)
    (sym : Sym) (rest : Seq) (text₁ text₂ : String) (captures₁ captures₂ : CaptureMap)
    (hhead : SymMatch g qual fuel sym text₁ captures₁)
    (htail : SeqMatch g qual fuel rest text₂ captures₂) :
    SeqMatch g qual fuel (SymItem.mk sym false :: rest)
      (text₁ ++ text₂) (captures₁ ++ captures₂) := by
  intro suffix
  rw [mem_matchSeq_cons_mk_required_iff]
  refine ⟨captures₁, text₂.toList ++ suffix, captures₂, ?_, htail suffix, rfl⟩
  simpa only [String.toList_append, List.append_assoc] using
    hhead (text₂.toList ++ suffix)

theorem seqMatch_optional (g : Grammar) (qual : String) (fuel : Nat)
    (sym : Sym) (rest : Seq) (render : α → String) (captures : α → CaptureMap)
    (valid : α → Prop) (entry : Option α) (text : String) (tailCaptures : CaptureMap)
    (hvalid : OptionalValid valid entry)
    (hhead : ∀ head, valid head → SymMatch g qual fuel sym (render head) (captures head))
    (htail : SeqMatch g qual fuel rest text tailCaptures) :
    SeqMatch g qual fuel (SymItem.mk sym true :: rest)
      (renderOptional render entry ++ text)
      (capturesOptional captures entry ++ tailCaptures) := by
  cases entry with
  | none =>
      intro suffix
      rw [mem_matchSeq_cons_mk_optional_iff]
      exact Or.inr (htail suffix)
  | some head =>
      intro suffix
      rw [mem_matchSeq_cons_mk_optional_iff]
      left
      refine ⟨captures head, text.toList ++ suffix, tailCaptures, ?_,
        htail suffix, rfl⟩
      simpa only [renderOptional, capturesOptional, String.toList_append,
        List.append_assoc] using hhead head hvalid (text.toList ++ suffix)

/-- Construct one `matchStar` result from exact matches for a list of following pieces. -/
theorem mem_matchStar_of_pieces
    (matchItem : List Char → List (CaptureMap × List Char))
    (sep : List Char) (hsep : sep ≠ [])
    (pieces : List (List Char × CaptureMap))
    (hpieces :
      ∀ piece ∈ pieces, ∀ suffix,
        (piece.2, suffix) ∈ matchItem (piece.1 ++ suffix)) :
    ∀ fuel suffix,
      (pieces.flatMap (fun piece => sep ++ piece.1)).length ≤ fuel →
      (pieces.flatMap (·.2), suffix, pieces.length) ∈
        matchStar matchItem sep fuel
          (pieces.flatMap (fun piece => sep ++ piece.1) ++ suffix) := by
  induction pieces with
  | nil =>
      intro fuel suffix _
      cases fuel <;> simp [matchStar]
  | cons piece pieces ih =>
      intro fuel suffix hfuel
      cases fuel with
      | zero =>
          have hsepLength : 1 ≤ sep.length := by
            cases sep with
            | nil => exact (hsep rfl).elim
            | cons _ _ => simp
          simp only [List.flatMap_cons, List.length_append] at hfuel
          omega
      | succ fuel =>
          simp only [List.flatMap_cons, List.length_cons]
          rw [matchStar]
          right
          have hprefix :
              sep.isPrefixOf
                  (sep ++ piece.1 ++
                    pieces.flatMap (fun next => sep ++ next.1) ++ suffix) =
                true := by
            simp
          simp only [hprefix, if_true]
          have hdrop :
              List.drop sep.length
                  (sep ++ piece.1 ++
                    pieces.flatMap (fun next => sep ++ next.1) ++ suffix) =
                piece.1 ++
                  (pieces.flatMap (fun next => sep ++ next.1) ++ suffix) := by
            simp [List.append_assoc]
          rw [hdrop]
          apply List.mem_flatMap.mpr
          let remainder :=
            pieces.flatMap (fun next => sep ++ next.1) ++ suffix
          refine ⟨(piece.2, remainder), ?_, ?_⟩
          · simpa [remainder, List.append_assoc] using
              hpieces piece (by simp) remainder
          · apply List.mem_map.mpr
            refine ⟨(pieces.flatMap (·.2), suffix, pieces.length), ?_, rfl⟩
            apply ih
            · intro next hnext
              exact hpieces next (by simp [hnext])
            · have hsepLength : 1 ≤ sep.length := by
                cases sep with
                | nil => exact (hsep rfl).elim
                | cons _ _ => simp
              simp only [List.flatMap_cons, List.length_append] at hfuel ⊢
              omega

/-- Construct one `matchRep` result from exact matches for a nonempty list of pieces. -/
theorem mem_matchRep_of_pieces
    (matchItem : List Char → List (CaptureMap × List Char))
    (sep : List Char) (hsep : sep ≠ [])
    (pieces : List (List Char × CaptureMap)) (hne : pieces ≠ [])
    (hpieces :
      ∀ piece ∈ pieces, ∀ suffix,
        (piece.2, suffix) ∈ matchItem (piece.1 ++ suffix))
    (suffix : List Char) :
    (pieces.flatMap (·.2), suffix, pieces.length) ∈
      matchRep matchItem sep (sep.intercalate (pieces.map (·.1)) ++ suffix) := by
  cases pieces with
  | nil => exact (hne rfl).elim
  | cons piece pieces =>
      rw [List.map_cons, intercalate_cons_flatMap]
      rw [flatMap_map_eq]
      simp only [matchRep, List.mem_flatMap]
      let remainder :=
        pieces.flatMap (fun next => sep ++ next.1) ++ suffix
      refine ⟨(piece.2, remainder), ?_, ?_⟩
      · simpa [remainder, List.append_assoc] using
          hpieces piece (by simp) remainder
      · rw [List.mem_map]
        refine ⟨(pieces.flatMap (·.2), suffix, pieces.length), ?_, rfl⟩
        apply mem_matchStar_of_pieces matchItem sep hsep pieces
        · intro next hnext
          exact hpieces next (by simp [hnext])
        · simp only [List.length_append]
          omega

theorem symMatch_rep (g : Grammar) (qual : String) (fuel : Nat)
    (sep : String) (item : Sym) (lo : Nat) (hi : Option Nat)
    (render : α → String) (captures : α → CaptureMap) (valid : α → Prop)
    (values : List α) (hsep : sep ≠ "")
    (hvalid : RepetitionValid lo hi valid values)
    (hitem :
      ∀ x, valid x →
        SymMatch g qual fuel item (render x) (captures x)) :
    SymMatch g qual fuel (.rep sep item lo hi)
      (renderSeparated sep render values)
      (capturesSeparated (item.refName?.getD qual) captures values) := by
  intro suffix
  simp only [matchSym]
  rw [List.mem_filterMap]
  let pieces : List (List Char × CaptureMap) :=
    values.map fun x => (render x |>.toList, captures x)
  have hpieces :
      ∀ piece ∈ pieces, ∀ rest,
        (piece.2, rest) ∈
          matchSym g qual fuel item (piece.1 ++ rest) := by
    intro piece hpiece rest
    rw [List.mem_map] at hpiece
    obtain ⟨x, hx, rfl⟩ := hpiece
    exact hitem x (hvalid.2.2.2 x hx) rest
  have hpiecesNe : pieces ≠ [] := by
    simp [pieces, hvalid.1]
  have hrep :
      (pieces.flatMap (·.2), suffix, pieces.length) ∈
        matchRep (fun cs => matchSym g qual fuel item cs) sep.toList
          (sep.toList.intercalate (pieces.map (·.1)) ++ suffix) :=
    mem_matchRep_of_pieces _ sep.toList (toList_ne_nil_of_ne sep hsep)
      pieces hpiecesNe hpieces suffix
  refine ⟨(pieces.flatMap (·.2), suffix, pieces.length), ?_, ?_⟩
  · simpa [renderSeparated, pieces, String.toList_intercalate,
      List.map_map, Function.comp_def] using hrep
  · have hlength : pieces.length = values.length := by simp [pieces]
    have hcaptures : pieces.flatMap (·.2) = values.flatMap captures := by
      rw [show pieces = values.map (fun x => (render x |>.toList, captures x)) from rfl]
      simpa using
        (flatMap_map_eq values
          (fun x : α => ((render x).toList, captures x))
          (fun pair : List Char × CaptureMap => pair.2))
    simp only
    cases hi with
    | none =>
        simp [hlength, hcaptures, hvalid.2.1, capturesSeparated]
    | some upper =>
        simp [hlength, hcaptures, hvalid.2.1, hvalid.2.2.1 upper rfl,
          capturesSeparated]

theorem prodMatch_of_alt (g : Grammar) (qual : String) (fuel : Nat)
    (prod : Production) (alt : Seq) (halt : alt ∈ prod.alts)
    (text : String) (captures : CaptureMap)
    (hmatch : SeqMatch g qual fuel alt text captures) :
    ProdMatch g qual fuel prod text captures := by
  intro suffix
  rw [matchProd, List.mem_flatMap]
  exact ⟨alt, halt, hmatch suffix⟩

/-- Turn an exact full match of the start production into membership in `fullParses`. -/
theorem prodMatch_mem_fullParses (g : Grammar) (prod : Production)
    (hstart : g.startProd? = some prod) (text : String) (captures : CaptureMap)
    (hmatch : ProdMatch g "" g.prods.length prod text captures) :
    captures ∈ fullParses g text := by
  unfold fullParses
  rw [hstart, List.mem_map]
  refine ⟨(captures, []), ?_, rfl⟩
  rw [List.mem_filter]
  exact ⟨by simpa using hmatch [], rfl⟩

end Triptych
