import Outputs.IPv6.parser
import CedarSupport.String
import CedarSupport.StringInternals
import Triptych.Theorems.DecodeRepLemmas
import Triptych.Theorems.String

/-!
# IPv6 grammar capture view

Exact component, constraint, and denotation facts for Triptych's generated IPv6 grammar.
This module contains no theorem relating the grammar to Cedar's executable parser.
-/

open Cedar.Spec.Ext
open CedarSupport.String
open CedarSupport.StringInternals
open Triptych

namespace IPv6.GrammarView

def HexValid (s : String) : Prop :=
  IsHexDigitsBetween 1 4 s

def renderGroups (parts : List String) : String :=
  String.intercalate ":" parts

def hextetCaptures (parent name part : String) : CaptureMap :=
  [(name, part), (parent ++ "." ++ name, part)]

def repeatedCaptures (parent name : String) (parts : List String) : CaptureMap :=
  (name ++ "#count", toString parts.length) ::
    parts.flatMap (hextetCaptures parent name)

theorem hextet_mem (fuel : Nat) (parent name : String) (hparent : parent ≠ "")
    (hprod :
      IPv6.grammar.prod? name =
        some
          (Production.mk name
            [[SymItem.mk (Sym.term TokClass.hexDigit (LenSpec.between 1 4)) false]]))
    (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym IPv6.grammar parent (fuel + 1) (Sym.ref name) cs ↔
      ∃ part,
        m = hextetCaptures parent name part ∧
        cs = part.toList ++ r ∧ HexValid part := by
  rw [mem_matchSym_ref_single_term_qualified_iff IPv6.grammar parent fuel
    name name TokClass.hexDigit (LenSpec.between 1 4) hprod]
  constructor
  · rintro ⟨part, rfl, hcs, hvalid⟩
    exact ⟨String.ofList part, by simp [hextetCaptures, hparent], by simpa using hcs,
      by simpa [HexValid, IsHexDigitsBetween_matchesTerm] using hvalid⟩
  · rintro ⟨part, rfl, hcs, hvalid⟩
    exact ⟨part.toList, by simp [hextetCaptures, hparent], by simpa using hcs,
      by simpa [HexValid, IsHexDigitsBetween_matchesTerm] using hvalid⟩

theorem hextetRep_mem (fuel : Nat) (parent name : String) (hparent : parent ≠ "")
    (hprod :
      IPv6.grammar.prod? name =
        some
          (Production.mk name
            [[SymItem.mk (Sym.term TokClass.hexDigit (LenSpec.between 1 4)) false]]))
    (lo : Nat) (hi : Option Nat) (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈
        matchSym IPv6.grammar parent (fuel + 1)
          (Sym.rep ":" (Sym.ref name) lo hi) cs ↔
      ∃ parts : List String,
        parts ≠ [] ∧
        lo ≤ parts.length ∧
        (∀ upper, hi = some upper → parts.length ≤ upper) ∧
        cs = (renderGroups parts).toList ++ r ∧
        (∀ part ∈ parts, HexValid part) ∧
        m = repeatedCaptures parent name parts := by
  have hitem :
      ∀ cs r m,
        (m, r) ∈ matchSym IPv6.grammar parent (fuel + 1) (Sym.ref name) cs ↔
          ∃ part,
            cs = part.toList ++ r ∧
            HexValid part ∧
            m = hextetCaptures parent name part := by
    intro input rest captures
    rw [hextet_mem fuel parent name hparent hprod]
    constructor
    · rintro ⟨part, hcaptures, hinput, hvalid⟩
      exact ⟨part, hinput, hvalid, hcaptures⟩
    · rintro ⟨part, hinput, hvalid, hcaptures⟩
      exact ⟨part, hcaptures, hinput, hvalid⟩
  rw [mem_matchSym_rep_string_capture_iff IPv6.grammar parent (fuel + 1) ":"
    (Sym.ref name) lo hi HexValid (hextetCaptures parent name) (by decide)
    hitem]
  simp only [Sym.refName?, Option.getD_some]
  change _ ↔ ∃ parts : List String,
    parts ≠ [] ∧
    lo ≤ parts.length ∧
    (∀ upper, hi = some upper → parts.length ≤ upper) ∧
    cs = (String.intercalate ":" parts).toList ++ r ∧
    (∀ part ∈ parts, HexValid part) ∧
    m =
      ((name ++ "#count", toString parts.length) ::
        parts.flatMap (hextetCaptures parent name))
  rfl

inductive Addr where
  | full (parts : List String)
  | compressed (left right : List String)

namespace Addr

def render : Addr → String
  | .full parts => renderGroups parts
  | .compressed left right => renderGroups left ++ "::" ++ renderGroups right

def SyntaxValid : Addr → Prop
  | .full parts =>
      parts.length = 8 ∧ ∀ part ∈ parts, HexValid part
  | .compressed left right =>
      left.length ≤ 7 ∧ right.length ≤ 7 ∧
        (∀ part ∈ left, HexValid part) ∧
        ∀ part ∈ right, HexValid part

def Constraints : Addr → Prop
  | .full _ => True
  | .compressed left right => left.length + right.length < 8

def Valid (addr : Addr) : Prop :=
  addr.SyntaxValid ∧ addr.Constraints

def denotation : Addr → CedarExamples.IPv6.IPv6Addr
  | .full parts => CedarExamples.IPv6.toV6Addr parts
  | .compressed left right =>
      CedarExamples.IPv6.toV6Addr
        (left ++ List.replicate (8 - (left.length + right.length)) "" ++ right)

end Addr

def fullCaptures (parts : List String) : CaptureMap :=
  [("Full", renderGroups parts), ("V6Addr.Full", renderGroups parts)] ++
    repeatedCaptures "Full" "H16" parts

def sideCaptures (side name : String) (parts : List String) : CaptureMap :=
  [(side, renderGroups parts), ("Compressed." ++ side, renderGroups parts)] ++
    repeatedCaptures side name parts

def optionalSideCaptures (side name : String) (parts : List String) : CaptureMap :=
  if parts.isEmpty then [] else sideCaptures side name parts

def compressedCaptures (left right : List String) : CaptureMap :=
  [("Compressed", Addr.render (.compressed left right)),
    ("V6Addr.Compressed", Addr.render (.compressed left right))] ++
    optionalSideCaptures "Left" "H16L" left ++
    optionalSideCaptures "Right" "H16R" right

def addrCaptures : Addr → CaptureMap
  | addr@(.full parts) =>
      ("V6Addr", addr.render) :: fullCaptures parts
  | addr@(.compressed left right) =>
      ("V6Addr", addr.render) :: compressedCaptures left right

theorem full_mem (fuel : Nat) (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈
        matchSym IPv6.grammar "V6Addr" (fuel + 2) (Sym.ref "Full") cs ↔
      ∃ parts,
        m = fullCaptures parts ∧
        cs = (renderGroups parts).toList ++ r ∧
        parts.length = 8 ∧
        ∀ part ∈ parts, HexValid part := by
  rw [mem_matchSym_ref_iff IPv6.grammar "V6Addr" (fuel + 1) "Full" _ rfl]
  constructor
  · rintro ⟨inner, hinner, rfl⟩
    rw [matchProd] at hinner
    simp only [List.mem_flatMap, List.mem_singleton, exists_eq_left] at hinner
    obtain ⟨mrep, mid, mtail, hrep, htail, rfl⟩ :=
      (mem_matchSeq_cons_required_iff IPv6.grammar "Full" (fuel + 1) _ _ rfl
        cs r inner).mp hinner
    simp only [matchSeq, List.mem_singleton, Prod.mk.injEq] at htail
    obtain ⟨rfl, rfl⟩ := htail
    obtain ⟨parts, _hne, hlo, hhi, hcs, hall, rfl⟩ :=
      (hextetRep_mem fuel "Full" "H16" (by decide) rfl 8 (some 8)
        cs r mrep).mp hrep
    have hlength : parts.length = 8 := by
      have hupper := hhi 8 rfl
      omega
    have hconsumed :
        String.ofList (cs.take (cs.length - r.length)) =
          renderGroups parts := by
      simpa using consumed_eq_of_append hcs
    exact ⟨parts, by simp [fullCaptures, hconsumed], hcs, hlength, hall⟩
  · rintro ⟨parts, rfl, hcs, hlength, hall⟩
    refine ⟨repeatedCaptures "Full" "H16" parts, ?_, ?_⟩
    · rw [matchProd]
      simp only [List.mem_flatMap, List.mem_singleton, exists_eq_left]
      rw [mem_matchSeq_cons_required_iff IPv6.grammar "Full" (fuel + 1) _ _ rfl]
      refine ⟨repeatedCaptures "Full" "H16" parts, r, [], ?_,
        by simp [matchSeq], by simp⟩
      exact
        (hextetRep_mem fuel "Full" "H16" (by decide) rfl 8 (some 8)
          cs r (repeatedCaptures "Full" "H16" parts)).mpr
          ⟨parts, by
            intro hnil
            simp [hnil] at hlength,
            by omega, by
              intro upper hu
              simp at hu
              subst upper
              omega,
            hcs, hall, rfl⟩
    · have hconsumed :
          String.ofList (cs.take (cs.length - r.length)) =
            renderGroups parts := by
        simpa using consumed_eq_of_append hcs
      simp [fullCaptures, hconsumed]

theorem side_mem (fuel : Nat) (side name : String) (hside : side ≠ "")
    (hsideProd :
      IPv6.grammar.prod? side =
        some
          (Production.mk side
            [[SymItem.mk (Sym.rep ":" (Sym.ref name) 1 (some 7)) false]]))
    (hnameProd :
      IPv6.grammar.prod? name =
        some
          (Production.mk name
            [[SymItem.mk (Sym.term TokClass.hexDigit (LenSpec.between 1 4)) false]]))
    (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈
        matchSym IPv6.grammar "Compressed" (fuel + 2) (Sym.ref side) cs ↔
      ∃ parts,
        m = sideCaptures side name parts ∧
        cs = (renderGroups parts).toList ++ r ∧
        parts ≠ [] ∧
        parts.length ≤ 7 ∧
        ∀ part ∈ parts, HexValid part := by
  rw [mem_matchSym_ref_iff IPv6.grammar "Compressed" (fuel + 1)
    side _ hsideProd]
  constructor
  · rintro ⟨inner, hinner, rfl⟩
    rw [matchProd] at hinner
    simp only [List.mem_flatMap, List.mem_singleton, exists_eq_left] at hinner
    obtain ⟨mrep, mid, mtail, hrep, htail, rfl⟩ :=
      (mem_matchSeq_cons_required_iff IPv6.grammar side (fuel + 1) _ _ rfl
        cs r inner).mp hinner
    simp only [matchSeq, List.mem_singleton, Prod.mk.injEq] at htail
    obtain ⟨rfl, rfl⟩ := htail
    obtain ⟨parts, hne, _hlo, hhi, hcs, hall, rfl⟩ :=
      (hextetRep_mem fuel side name hside hnameProd 1 (some 7)
        cs r mrep).mp hrep
    have hlength : parts.length ≤ 7 := hhi 7 rfl
    have hconsumed :
        String.ofList (cs.take (cs.length - r.length)) =
          renderGroups parts := by
      simpa using consumed_eq_of_append hcs
    exact
      ⟨parts, by simp [sideCaptures, hconsumed], hcs, hne, hlength, hall⟩
  · rintro ⟨parts, rfl, hcs, hne, hlength, hall⟩
    refine ⟨repeatedCaptures side name parts, ?_, ?_⟩
    · rw [matchProd]
      simp only [List.mem_flatMap, List.mem_singleton, exists_eq_left]
      rw [mem_matchSeq_cons_required_iff IPv6.grammar side (fuel + 1) _ _ rfl]
      refine ⟨repeatedCaptures side name parts, r, [], ?_,
        by simp [matchSeq], by simp⟩
      exact
        (hextetRep_mem fuel side name hside hnameProd 1 (some 7)
          cs r (repeatedCaptures side name parts)).mpr
          ⟨parts, hne, by
            cases parts with
            | nil => exact (hne rfl).elim
            | cons _ _ => simp,
            by
              intro upper hu
              simp at hu
              subst upper
              exact hlength,
            hcs, hall, rfl⟩
    · have hconsumed :
          String.ofList (cs.take (cs.length - r.length)) =
            renderGroups parts := by
        simpa using consumed_eq_of_append hcs
      simp [sideCaptures, hconsumed]

theorem optional_side_cons_mem (fuel : Nat) (side name : String)
    (hside : side ≠ "")
    (hsideProd :
      IPv6.grammar.prod? side =
        some
          (Production.mk side
            [[SymItem.mk (Sym.rep ":" (Sym.ref name) 1 (some 7)) false]]))
    (hnameProd :
      IPv6.grammar.prod? name =
        some
          (Production.mk name
            [[SymItem.mk (Sym.term TokClass.hexDigit (LenSpec.between 1 4)) false]]))
    (rest : Seq) (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈
        matchSeq IPv6.grammar "Compressed" (fuel + 2)
          (SymItem.mk (Sym.ref side) true :: rest) cs ↔
      ∃ parts mid mrest,
        m = optionalSideCaptures side name parts ++ mrest ∧
        cs = (renderGroups parts).toList ++ mid ∧
        parts.length ≤ 7 ∧
        (∀ part ∈ parts, HexValid part) ∧
        (mrest, r) ∈
          matchSeq IPv6.grammar "Compressed" (fuel + 2) rest mid := by
  rw [mem_matchSeq_cons_optional_iff IPv6.grammar "Compressed" (fuel + 2) _ _ rfl]
  constructor
  · rintro (⟨mside, mid, mrest, hmem, hrest, rfl⟩ | hrest)
    · obtain ⟨parts, rfl, hcs, hne, hlength, hall⟩ :=
        (side_mem fuel side name hside hsideProd hnameProd cs mid mside).mp hmem
      have hnonempty : parts.isEmpty = false := by
        simpa [List.isEmpty_iff] using hne
      exact
        ⟨parts, mid, mrest, by simp [optionalSideCaptures, hnonempty],
          hcs, hlength, hall, hrest⟩
    · exact
        ⟨[], cs, m, by simp [optionalSideCaptures], by simp [renderGroups],
          by simp, by simp, hrest⟩
  · rintro ⟨parts, mid, mrest, hm, hcs, hlength, hall, hrest⟩
    cases parts with
    | nil =>
        simp only [optionalSideCaptures, List.isEmpty_nil, if_true,
          List.nil_append] at hm
        simp only [renderGroups, String.intercalate_nil, String.toList_empty,
          List.nil_append] at hcs
        subst mrest
        subst mid
        exact Or.inr hrest
    | cons part parts =>
        apply Or.inl
        refine ⟨sideCaptures side name (part :: parts), mid, mrest, ?_,
          hrest, ?_⟩
        · exact
            (side_mem fuel side name hside hsideProd hnameProd cs mid
              (sideCaptures side name (part :: parts))).mpr
              ⟨part :: parts, rfl, hcs, by simp, hlength, hall⟩
        · simpa [optionalSideCaptures] using hm

theorem compressed_mem (fuel : Nat) (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈
        matchSym IPv6.grammar "V6Addr" (fuel + 3)
          (Sym.ref "Compressed") cs ↔
      ∃ left right,
        m = compressedCaptures left right ∧
        cs = (Addr.render (.compressed left right)).toList ++ r ∧
        left.length ≤ 7 ∧
        right.length ≤ 7 ∧
        (∀ part ∈ left, HexValid part) ∧
        ∀ part ∈ right, HexValid part := by
  rw [mem_matchSym_ref_iff IPv6.grammar "V6Addr" (fuel + 2)
    "Compressed" _ rfl]
  constructor
  · rintro ⟨inner, hinner, rfl⟩
    rw [matchProd] at hinner
    simp only [List.mem_flatMap, List.mem_singleton, exists_eq_left] at hinner
    obtain ⟨left, afterLeft, mleftTail, rfl, hleftcs, hleftLength, hleft,
        htail⟩ :=
      (optional_side_cons_mem fuel "Left" "H16L" (by decide) rfl rfl _
        cs r inner).mp hinner
    obtain ⟨mcolon, afterColon, mrightTail, hcolon, hrightTail, rfl⟩ :=
      (mem_matchSeq_cons_required_iff IPv6.grammar "Compressed" (fuel + 2)
        _ _ rfl afterLeft r mleftTail).mp htail
    obtain ⟨rfl, hcoloncs⟩ :=
      (mem_matchSym_lit_iff IPv6.grammar "Compressed" (fuel + 2)
        "::" afterLeft afterColon mcolon).mp hcolon
    obtain ⟨right, afterRight, mnil, rfl, hrightcs, hrightLength, hright,
        hnil⟩ :=
      (optional_side_cons_mem fuel "Right" "H16R" (by decide) rfl rfl []
        afterColon r mrightTail).mp hrightTail
    simp only [matchSeq, List.mem_singleton, Prod.mk.injEq] at hnil
    obtain ⟨rfl, rfl⟩ := hnil
    have hcs :
        cs = (Addr.render (.compressed left right)).toList ++ r := by
      simp [hleftcs, hcoloncs, hrightcs, Addr.render, String.toList_append,
        List.append_assoc]
    have hconsumed :
        String.ofList (cs.take (cs.length - r.length)) =
          Addr.render (.compressed left right) := by
      simpa using consumed_eq_of_append hcs
    exact
      ⟨left, right, by simp [compressedCaptures, hconsumed], hcs,
        hleftLength, hrightLength, hleft, hright⟩
  · rintro ⟨left, right, rfl, hcs, hleftLength, hrightLength, hleft, hright⟩
    let leftCaptures := optionalSideCaptures "Left" "H16L" left
    let rightCaptures := optionalSideCaptures "Right" "H16R" right
    refine ⟨leftCaptures ++ rightCaptures, ?_, ?_⟩
    · rw [matchProd]
      simp only [List.mem_flatMap, List.mem_singleton, exists_eq_left]
      rw [optional_side_cons_mem fuel "Left" "H16L" (by decide) rfl rfl]
      refine
        ⟨left,
          "::".toList ++ (renderGroups right).toList ++ r,
          rightCaptures,
          by simp [leftCaptures], ?_, hleftLength, hleft, ?_⟩
      · simp [hcs, Addr.render, String.toList_append, List.append_assoc]
      · rw [mem_matchSeq_cons_required_iff IPv6.grammar "Compressed"
          (fuel + 2) _ _ rfl]
        refine
          ⟨[], (renderGroups right).toList ++ r, rightCaptures,
            ?_, ?_, by simp⟩
        · exact
            (mem_matchSym_lit_iff IPv6.grammar "Compressed" (fuel + 2)
              "::" _ _ []).mpr ⟨rfl, rfl⟩
        · rw [optional_side_cons_mem fuel "Right" "H16R"
            (by decide) rfl rfl]
          exact
            ⟨right, r, [], by simp [rightCaptures], rfl,
              hrightLength, hright, by simp [matchSeq]⟩
    · have hconsumed :
          String.ofList (cs.take (cs.length - r.length)) =
            Addr.render (.compressed left right) := by
        simpa using consumed_eq_of_append hcs
      simp [compressedCaptures, leftCaptures, rightCaptures, hconsumed]

theorem v6Addr_mem (fuel : Nat) (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈
        matchSym IPv6.grammar "" (fuel + 4) (Sym.ref "V6Addr") cs ↔
      ∃ addr : Addr,
        m = addrCaptures addr ∧
        cs = addr.render.toList ++ r ∧
        addr.SyntaxValid := by
  rw [mem_matchSym_ref_iff IPv6.grammar "" (fuel + 3) "V6Addr" _ rfl]
  constructor
  · rintro ⟨inner, hinner, rfl⟩
    rw [matchProd] at hinner
    simp only [List.mem_flatMap, List.mem_cons, List.mem_singleton,
      exists_eq_or_imp, exists_eq_left] at hinner
    rcases hinner with hfull | hcompressed
    · obtain ⟨mfull, mid, mtail, hfull, htail, rfl⟩ :=
        (mem_matchSeq_cons_required_iff IPv6.grammar "V6Addr"
          (fuel + 3) _ _ rfl cs r inner).mp hfull
      simp only [matchSeq, List.mem_singleton, Prod.mk.injEq] at htail
      obtain ⟨rfl, rfl⟩ := htail
      obtain ⟨parts, rfl, hcs, hlength, hall⟩ :=
        (full_mem (fuel + 1) cs r mfull).mp hfull
      have hconsumed :
          String.ofList (cs.take (cs.length - r.length)) =
            renderGroups parts := by
        simpa using consumed_eq_of_append hcs
      exact
        ⟨.full parts, by simp [addrCaptures, Addr.render, hconsumed],
          by simpa [Addr.render] using hcs, hlength, hall⟩
    · rcases hcompressed with hcompressed | ⟨alt, halt, _⟩
      · obtain ⟨mcompressed, mid, mtail, hcompressed, htail, rfl⟩ :=
        (mem_matchSeq_cons_required_iff IPv6.grammar "V6Addr"
          (fuel + 3) _ _ rfl cs r inner).mp hcompressed
        simp only [matchSeq, List.mem_singleton, Prod.mk.injEq] at htail
        obtain ⟨rfl, rfl⟩ := htail
        obtain ⟨left, right, rfl, hcs, hleftLength, hrightLength, hleft,
            hright⟩ :=
          (compressed_mem fuel cs r mcompressed).mp hcompressed
        have hconsumed :
            String.ofList (cs.take (cs.length - r.length)) =
              Addr.render (.compressed left right) := by
          simpa using consumed_eq_of_append hcs
        exact
          ⟨.compressed left right,
            by simp [addrCaptures, hconsumed], hcs,
            hleftLength, hrightLength, hleft, hright⟩
      · simp at halt
  · rintro ⟨addr, rfl, hcs, hvalid⟩
    cases addr with
    | full parts =>
        refine ⟨fullCaptures parts, ?_, ?_⟩
        · rw [matchProd]
          simp only [List.mem_flatMap, List.mem_cons, List.mem_singleton,
            exists_eq_or_imp, exists_eq_left]
          left
          rw [mem_matchSeq_cons_required_iff IPv6.grammar "V6Addr"
            (fuel + 3) _ _ rfl]
          refine ⟨fullCaptures parts, r, [], ?_,
            by simp [matchSeq], by simp⟩
          exact
            (full_mem (fuel + 1) cs r (fullCaptures parts)).mpr
              ⟨parts, rfl, by simpa [Addr.render] using hcs, hvalid.1, hvalid.2⟩
        · have hconsumed :
              String.ofList (cs.take (cs.length - r.length)) =
                renderGroups parts := by
            simpa [Addr.render] using consumed_eq_of_append hcs
          simp [addrCaptures, Addr.render, hconsumed]
    | compressed left right =>
        refine ⟨compressedCaptures left right, ?_, ?_⟩
        · rw [matchProd]
          simp only [List.mem_flatMap, List.mem_cons, List.mem_singleton,
            exists_eq_or_imp, exists_eq_left]
          right
          left
          rw [mem_matchSeq_cons_required_iff IPv6.grammar "V6Addr"
            (fuel + 3) _ _ rfl]
          refine ⟨compressedCaptures left right, r, [], ?_,
            by simp [matchSeq], by simp⟩
          exact
            (compressed_mem fuel cs r (compressedCaptures left right)).mpr
              ⟨left, right, rfl, hcs, hvalid.1, hvalid.2.1,
                hvalid.2.2.1, hvalid.2.2.2⟩
        · have hconsumed :
              String.ofList (cs.take (cs.length - r.length)) =
                Addr.render (.compressed left right) := by
            simpa using consumed_eq_of_append hcs
          simp [addrCaptures, hconsumed]

def prefixCaptures : Option String → CaptureMap
  | none => []
  | some pre => [("Prefix", pre)]

theorem prefix_mem (fuel : Nat) (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈
        matchSym IPv6.grammar "" (fuel + 1) (Sym.ref "Prefix") cs ↔
      ∃ pre,
        m = prefixCaptures (some pre) ∧
        cs = pre.toList ++ r ∧
        IsDigitsBetween 1 3 pre := by
  rw [mem_matchSym_ref_single_term_iff IPv6.grammar fuel
    "Prefix" "Prefix" TokClass.digit (LenSpec.between 1 3) rfl]
  constructor
  · rintro ⟨pre, rfl, hcs, hvalid⟩
    exact
      ⟨String.ofList pre, by simp [prefixCaptures], by simpa using hcs,
        by simpa [IsDigitsBetween_matchesTerm] using hvalid⟩
  · rintro ⟨pre, rfl, hcs, hvalid⟩
    exact
      ⟨pre.toList, by simp [prefixCaptures], by simpa using hcs,
        by simpa [IsDigitsBetween_matchesTerm] using hvalid⟩

def OptionalPrefixSyntax : Option String → Prop
  | none => True
  | some pre => IsDigitsBetween 1 3 pre

def PrefixConstraints (pre : String) : Prop :=
  (pre.startsWith "0" → pre = "0") ∧ natOf pre ≤ 128

def OptionalPrefixConstraints : Option String → Prop
  | none => True
  | some pre => PrefixConstraints pre

def OptionalPrefixValid (pre : Option String) : Prop :=
  OptionalPrefixSyntax pre ∧ OptionalPrefixConstraints pre

def renderNet (addr : Addr) (pre : Option String) : String :=
  addr.render ++
    match pre with
    | none => ""
    | some p => "/" ++ p

def netCaptures (addr : Addr) (pre : Option String) : CaptureMap :=
  addrCaptures addr ++ prefixCaptures pre

structure View where
  addr : Addr
  «prefix» : Option String

namespace View

def render (v : View) : String :=
  renderNet v.addr v.«prefix»

def captures (v : View) : CaptureMap :=
  netCaptures v.addr v.«prefix»

def SyntaxValid (v : View) : Prop :=
  v.addr.SyntaxValid ∧ OptionalPrefixSyntax v.«prefix»

def Constraints (v : View) : Prop :=
  v.addr.Constraints ∧ OptionalPrefixConstraints v.«prefix»

def Valid (v : View) : Prop :=
  v.SyntaxValid ∧ v.Constraints

def denotation (v : View) : CedarExamples.IPv6.IPv6Net :=
  match v.addr with
  | .full parts =>
      CedarExamples.IPv6.toIPv6Net parts [] [] (v.«prefix».getD "")
  | .compressed left right =>
      CedarExamples.IPv6.toIPv6Net [] left right (v.«prefix».getD "")

end View

theorem v6Net_match_sound (fuel : Nat) (cs r : List Char) (m : CaptureMap)
    (hmem :
      (m, r) ∈
        matchProd IPv6.grammar "" (fuel + 4)
          (Production.mk "V6Net"
            [[SymItem.mk (Sym.ref "V6Addr") false],
              [SymItem.mk (Sym.ref "V6Addr") false,
                SymItem.mk (Sym.lit "/") false,
                SymItem.mk (Sym.ref "Prefix") false]]) cs) :
    ∃ v : View,
      m = v.captures ∧
      cs = v.render.toList ++ r ∧
      v.SyntaxValid := by
  rw [matchProd] at hmem
  simp only [List.mem_flatMap, List.mem_cons, exists_eq_or_imp] at hmem
  rcases hmem with hbare | hprefix
  · obtain ⟨maddr, mid, mtail, haddr, htail, rfl⟩ :=
      (mem_matchSeq_cons_required_iff IPv6.grammar "" (fuel + 4) _ _ rfl
        cs r m).mp hbare
    simp only [matchSeq, List.mem_singleton, Prod.mk.injEq] at htail
    obtain ⟨rfl, rfl⟩ := htail
    obtain ⟨addr, rfl, hcs, hvalid⟩ :=
      (v6Addr_mem fuel cs r maddr).mp haddr
    exact
      ⟨⟨addr, none⟩, by simp [View.captures, netCaptures, prefixCaptures],
        by simpa [View.render, renderNet] using hcs, hvalid, trivial⟩
  · rcases hprefix with hprefix | ⟨alt, halt, _⟩
    · obtain ⟨maddr, afterAddr, mtail, haddr, htail, rfl⟩ :=
        (mem_matchSeq_cons_required_iff IPv6.grammar "" (fuel + 4) _ _ rfl
          cs r m).mp hprefix
      obtain ⟨mslash, afterSlash, mprefixTail, hslash, hprefixTail, rfl⟩ :=
        (mem_matchSeq_cons_required_iff IPv6.grammar "" (fuel + 4) _ _ rfl
          afterAddr r mtail).mp htail
      obtain ⟨mprefix, afterPrefix, mnil, hpre, hnil, rfl⟩ :=
        (mem_matchSeq_cons_required_iff IPv6.grammar "" (fuel + 4) _ _ rfl
          afterSlash r mprefixTail).mp hprefixTail
      simp only [matchSeq, List.mem_singleton, Prod.mk.injEq] at hnil
      obtain ⟨rfl, rfl⟩ := hnil
      obtain ⟨addr, rfl, haddrCs, haddrValid⟩ :=
        (v6Addr_mem fuel cs afterAddr maddr).mp haddr
      obtain ⟨rfl, hslashCs⟩ :=
        (mem_matchSym_lit_iff IPv6.grammar "" (fuel + 4)
          "/" afterAddr afterSlash mslash).mp hslash
      obtain ⟨pre, rfl, hpreCs, hpreValid⟩ :=
        (prefix_mem (fuel + 3) afterSlash r mprefix).mp hpre
      refine
        ⟨⟨addr, some pre⟩,
          by simp [View.captures, netCaptures, prefixCaptures],
          ?_, haddrValid, hpreValid⟩
      simp [haddrCs, hslashCs, hpreCs, View.render, renderNet,
        String.toList_append, List.append_assoc]
    · simp at halt

theorem decode_ipv6_sound {s : String} {m : CaptureMap}
    (h : decode IPv6.grammar s = some m) :
    ∃ v : View,
      m = v.captures ∧
      s = v.render ∧
      v.SyntaxValid := by
  obtain ⟨p, hstart, hmem⟩ := mem_matchProd_of_decode_eq_some h
  have hp :
      p =
        Production.mk "V6Net"
          [[SymItem.mk (Sym.ref "V6Addr") false],
            [SymItem.mk (Sym.ref "V6Addr") false,
              SymItem.mk (Sym.lit "/") false,
              SymItem.mk (Sym.ref "Prefix") false]] := by
    have hknown :
        IPv6.grammar.startProd? =
          some
            (Production.mk "V6Net"
              [[SymItem.mk (Sym.ref "V6Addr") false],
                [SymItem.mk (Sym.ref "V6Addr") false,
                  SymItem.mk (Sym.lit "/") false,
                  SymItem.mk (Sym.ref "Prefix") false]]) := rfl
    rw [hknown] at hstart
    exact (Option.some.inj hstart).symm
  subst p
  have hxmem :
      (m, ([] : List Char)) ∈
        matchProd IPv6.grammar "" 10
          (Production.mk "V6Net"
            [[SymItem.mk (Sym.ref "V6Addr") false],
              [SymItem.mk (Sym.ref "V6Addr") false,
                SymItem.mk (Sym.lit "/") false,
                SymItem.mk (Sym.ref "Prefix") false]]) s.toList := by
    simpa [IPv6.grammar] using hmem
  obtain ⟨v, hm, hs, hvalid⟩ :=
    v6Net_match_sound 6 s.toList [] m hxmem
  refine ⟨v, hm, ?_, hvalid⟩
  rw [← String.toList_inj]
  simpa using hs

private theorem renderGroups_cons_toList (part : String) (parts : List String) :
    (renderGroups (part :: parts)).toList =
      part.toList ++
        match parts with
        | [] => []
        | _ => ':' :: (renderGroups parts).toList := by
  cases parts <;> simp [renderGroups, String.toList_append]

private theorem neColonOfHexValid {s : String} (h : HexValid s) :
    ∀ c ∈ s.toList, c ≠ ':' := by
  intro c hc heq
  subst c
  have hm := h.1 ':' hc
  simp [TokClass.mem] at hm

private theorem splitDoubleColonAux_consume_renderGroups
    (current suffix : List Char) (parts : List String)
    (hall : ∀ part ∈ parts, HexValid part) :
    legacySplitDoubleColonAux current ((renderGroups parts).toList ++ suffix) =
      legacySplitDoubleColonAux (current ++ (renderGroups parts).toList) suffix := by
  induction parts generalizing current with
  | nil => simp [renderGroups]
  | cons part parts ih =>
      cases parts with
      | nil =>
          simpa [renderGroups] using
            splitDoubleColonAux_consume_noColon current part.toList suffix
              (neColonOfHexValid (hall part (by simp)))
      | cons next tail =>
          have hpart := hall part (by simp)
          have hnext := hall next (by simp)
          have htail : ∀ item ∈ next :: tail, HexValid item := by
            intro item hitem
            exact hall item (by simp [hitem])
          have hnextList : next.toList ≠ [] := by
            intro heq
            have hlen := hnext.2.1
            rw [← String.length_toList, heq] at hlen
            simp at hlen
          obtain ⟨c, cs, hcList⟩ := List.exists_cons_of_ne_nil hnextList
          have hc : c ≠ ':' := neColonOfHexValid hnext c (by simp [hcList])
          obtain ⟨tailChars, hrenderTail⟩ :
              ∃ tailChars, (renderGroups (next :: tail)).toList = c :: tailChars := by
            rw [renderGroups_cons_toList, hcList]
            exact ⟨_, rfl⟩
          have hnonmatch :
              ∀ rest, ':' = ':' →
                (renderGroups (next :: tail)).toList ++ suffix =
                  ':' :: rest → False := by
            intro rest _ heq
            rw [hrenderTail] at heq
            injection heq with heq
            exact hc heq
          rw [renderGroups_cons_toList]
          simp only [List.cons_append, List.append_assoc]
          rw [splitDoubleColonAux_consume_noColon current part.toList
            (':' :: ((renderGroups (next :: tail)).toList ++ suffix))
            (neColonOfHexValid hpart)]
          rw [legacySplitDoubleColonAux.eq_2 (current ++ part.toList) ':'
            ((renderGroups (next :: tail)).toList ++ suffix) hnonmatch]
          have hrec := ih ((current ++ part.toList) ++ [':']) htail
          rw [hrec]
          congr 1
          simp only [List.append_assoc, List.singleton_append]

private theorem splitDoubleColonAux_renderGroups_eq_singleton
    (parts : List String) (hall : ∀ part ∈ parts, HexValid part) :
    legacySplitDoubleColonAux [] (renderGroups parts).toList = [renderGroups parts] := by
  have h := splitDoubleColonAux_consume_renderGroups [] [] parts hall
  simpa [legacySplitDoubleColonAux] using h

private theorem splitOn_renderGroups_eq_singleton
    (parts : List String) (hall : ∀ part ∈ parts, HexValid part) :
    (renderGroups parts).splitOn "::" = [renderGroups parts] := by
  rw [splitOnDoubleColon_eq]
  exact splitDoubleColonAux_renderGroups_eq_singleton parts hall

private theorem splitOn_renderGroups_doubleColon_renderGroups
    (left right : List String)
    (hleft : ∀ part ∈ left, HexValid part)
    (hright : ∀ part ∈ right, HexValid part) :
    (renderGroups left ++ "::" ++ renderGroups right).splitOn "::" =
      [renderGroups left, renderGroups right] := by
  rw [splitOnDoubleColon_eq]
  simp only [String.toList_append]
  rw [show "::".toList = [':', ':'] by rfl]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  change
    legacySplitDoubleColonAux []
        ((renderGroups left).toList ++ ':' :: ':' :: (renderGroups right).toList) =
      [renderGroups left, renderGroups right]
  rw [splitDoubleColonAux_consume_renderGroups []
    (':' :: ':' :: (renderGroups right).toList) left hleft]
  rw [legacySplitDoubleColonAux.eq_1]
  rw [splitDoubleColonAux_renderGroups_eq_singleton right hright]
  simp

private theorem renderGroups_nonempty {parts : List String}
    (hne : parts ≠ []) (hall : ∀ part ∈ parts, HexValid part) :
    renderGroups parts ≠ "" := by
  cases parts with
  | nil => exact (hne rfl).elim
  | cons part parts =>
      intro hempty
      have hpart : part ≠ "" := by
        intro h
        have hlength := (hall part (by simp)).2.1
        simp [h] at hlength
      cases parts with
      | nil => exact hpart (by simpa [renderGroups] using hempty)
      | cons next tail =>
          have hprefix :
              part.toList.isPrefixOf (renderGroups (part :: next :: tail)).toList =
                true := by
            rw [renderGroups_cons_toList]
            exact List.isPrefixOf_iff_prefix.mpr ⟨_, rfl⟩
          rw [hempty] at hprefix
          simp at hprefix
          exact hpart hprefix

private theorem noColonOfHexValid {s : String} (h : HexValid s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = ':')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  exact neColonOfHexValid h c hc

theorem renderGroups_injective {left right : List String}
    (hleft : ∀ part ∈ left, HexValid part)
    (hright : ∀ part ∈ right, HexValid part)
    (h : renderGroups left = renderGroups right) :
    left = right := by
  cases left with
  | nil =>
      cases right with
      | nil => rfl
      | cons part parts =>
          have hne : renderGroups (part :: parts) ≠ "" :=
            renderGroups_nonempty (by simp) hright
          simp [renderGroups] at h
          apply (hne _).elim
          simpa [renderGroups] using h.symm
  | cons part parts =>
      cases right with
      | nil =>
          have hne : renderGroups (part :: parts) ≠ "" :=
            renderGroups_nonempty (by simp) hleft
          simp [renderGroups] at h
          apply (hne _).elim
          simpa [renderGroups] using h
      | cons item items =>
          apply Triptych.intercalate_injective (left := part :: parts)
            (right := item :: items) (by simp) (by simp) ':'
          · intro segment hsegment c hc
            exact noColonOfHexValid (hleft segment hsegment) c hc
          · intro segment hsegment c hc
            exact noColonOfHexValid (hright segment hsegment) c hc
          · simpa [renderGroups] using h

theorem Addr.render_injective {left right : Addr}
    (hleft : left.SyntaxValid) (hright : right.SyntaxValid)
    (h : left.render = right.render) :
    left = right := by
  cases left with
  | full leftParts =>
      cases right with
      | full rightParts =>
          congr 1
          exact renderGroups_injective hleft.2 hright.2 h
      | compressed rightLeft rightRight =>
          have hsplits := congrArg (fun s : String => s.splitOn "::") h
          simp only [Addr.render] at hsplits
          rw [splitOn_renderGroups_eq_singleton leftParts hleft.2,
            splitOn_renderGroups_doubleColon_renderGroups rightLeft rightRight
              hright.2.2.1 hright.2.2.2] at hsplits
          simp at hsplits
  | compressed leftLeft leftRight =>
      cases right with
      | full rightParts =>
          have hsplits := congrArg (fun s : String => s.splitOn "::") h
          simp only [Addr.render] at hsplits
          rw [splitOn_renderGroups_doubleColon_renderGroups leftLeft leftRight
              hleft.2.2.1 hleft.2.2.2,
            splitOn_renderGroups_eq_singleton rightParts hright.2] at hsplits
          simp at hsplits
      | compressed rightLeft rightRight =>
          have hsplits := congrArg (fun s : String => s.splitOn "::") h
          simp only [Addr.render] at hsplits
          rw [splitOn_renderGroups_doubleColon_renderGroups leftLeft leftRight
              hleft.2.2.1 hleft.2.2.2,
            splitOn_renderGroups_doubleColon_renderGroups rightLeft rightRight
              hright.2.2.1 hright.2.2.2] at hsplits
          simp only [List.cons.injEq, and_true] at hsplits
          have hleftParts :=
            renderGroups_injective hleft.2.2.1 hright.2.2.1 hsplits.1
          have hrightParts :=
            renderGroups_injective hleft.2.2.2 hright.2.2.2 hsplits.2
          subst rightLeft
          subst rightRight
          rfl

private theorem noSlashAppend {s₁ s₂ : String}
    (h₁ : ∀ c ∈ s₁.toList, (fun x : Char => decide (x = '/')) c = false)
    (h₂ : ∀ c ∈ s₂.toList, (fun x : Char => decide (x = '/')) c = false) :
    ∀ c ∈ (s₁ ++ s₂).toList, (fun x : Char => decide (x = '/')) c = false := by
  intro c hc
  rw [String.toList_append] at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact h₁ c hc
  · exact h₂ c hc

private theorem noSlashOfHexValid {s : String} (h : HexValid s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = '/')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq
  subst c
  have hm := h.1 '/' hc
  simp [TokClass.mem] at hm

private theorem noSlashColon :
    ∀ c ∈ ":".toList, (fun x : Char => decide (x = '/')) c = false := by
  simp

private theorem noSlashDoubleColon :
    ∀ c ∈ "::".toList, (fun x : Char => decide (x = '/')) c = false := by
  simp

private theorem noSlashRenderGroups {parts : List String}
    (hall : ∀ part ∈ parts, HexValid part) :
    ∀ c ∈ (renderGroups parts).toList,
      (fun x : Char => decide (x = '/')) c = false := by
  induction parts with
  | nil => simp [renderGroups]
  | cons part parts ih =>
      cases parts with
      | nil =>
          simpa [renderGroups] using noSlashOfHexValid (hall part (by simp))
      | cons next tail =>
          have hpart := noSlashOfHexValid (hall part (by simp))
          have htail := ih (fun item hitem => hall item (by simp [hitem]))
          simpa [renderGroups, String.append_assoc] using
            noSlashAppend hpart (noSlashAppend noSlashColon htail)

private theorem noSlashAddr (addr : Addr) (h : addr.SyntaxValid) :
    ∀ c ∈ addr.render.toList,
      (fun x : Char => decide (x = '/')) c = false := by
  cases addr with
  | full parts =>
      exact noSlashRenderGroups h.2
  | compressed left right =>
      simpa [Addr.render, String.append_assoc] using
        noSlashAppend (noSlashRenderGroups h.2.2.1)
          (noSlashAppend noSlashDoubleColon (noSlashRenderGroups h.2.2.2))

private theorem noSlashOfDigitsBetween {lo hi : Nat} {s : String}
    (h : IsDigitsBetween lo hi s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = '/')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq
  subst c
  have hm := h.1 '/' hc
  simp [TokClass.mem] at hm

theorem View.render_injective {left right : View}
    (hleft : left.SyntaxValid) (hright : right.SyntaxValid)
    (h : left.render = right.render) :
    left = right := by
  have hleftAddr := noSlashAddr left.addr hleft.1
  have hrightAddr := noSlashAddr right.addr hright.1
  cases left with
  | mk leftAddr leftPre =>
      cases right with
      | mk rightAddr rightPre =>
          cases leftPre with
          | none =>
              have hsplitLeft :
                  (View.render ⟨leftAddr, none⟩).splitToList (· = '/') =
                    [leftAddr.render] := by
                simpa [View.render, renderNet] using
                  splitToListNoSep leftAddr.render
                    (fun x : Char => decide (x = '/')) hleftAddr
              cases rightPre with
              | none =>
                  have hsplitRight :
                      (View.render ⟨rightAddr, none⟩).splitToList (· = '/') =
                        [rightAddr.render] := by
                    simpa [View.render, renderNet] using
                      splitToListNoSep rightAddr.render
                        (fun x : Char => decide (x = '/')) hrightAddr
                  have hsplits :=
                    congrArg (fun s : String => s.splitToList (· = '/')) h
                  rw [hsplitLeft, hsplitRight] at hsplits
                  have haddr :
                      leftAddr.render = rightAddr.render := by
                    simpa using hsplits
                  have heq :=
                    Addr.render_injective hleft.1 hright.1 haddr
                  change leftAddr = rightAddr at heq
                  subst rightAddr
                  rfl
              | some rightPre =>
                  have hsplitRight :
                      (View.render ⟨rightAddr, some rightPre⟩).splitToList
                          (· = '/') =
                        [rightAddr.render, rightPre] := by
                    simpa [View.render, renderNet, String.append_assoc] using
                      splitToListEq rightAddr.render rightPre
                        (fun x : Char => decide (x = '/')) '/' (by simp)
                        hrightAddr (noSlashOfDigitsBetween hright.2)
                  have hsplits :=
                    congrArg (fun s : String => s.splitToList (· = '/')) h
                  rw [hsplitLeft, hsplitRight] at hsplits
                  simp at hsplits
          | some leftPre =>
              have hsplitLeft :
                  (View.render ⟨leftAddr, some leftPre⟩).splitToList
                      (· = '/') =
                    [leftAddr.render, leftPre] := by
                simpa [View.render, renderNet, String.append_assoc] using
                  splitToListEq leftAddr.render leftPre
                    (fun x : Char => decide (x = '/')) '/' (by simp)
                    hleftAddr (noSlashOfDigitsBetween hleft.2)
              cases rightPre with
              | none =>
                  have hsplitRight :
                      (View.render ⟨rightAddr, none⟩).splitToList (· = '/') =
                        [rightAddr.render] := by
                    simpa [View.render, renderNet] using
                      splitToListNoSep rightAddr.render
                        (fun x : Char => decide (x = '/')) hrightAddr
                  have hsplits :=
                    congrArg (fun s : String => s.splitToList (· = '/')) h
                  rw [hsplitLeft, hsplitRight] at hsplits
                  simp at hsplits
              | some rightPre =>
                  have hsplitRight :
                      (View.render ⟨rightAddr, some rightPre⟩).splitToList
                          (· = '/') =
                        [rightAddr.render, rightPre] := by
                    simpa [View.render, renderNet, String.append_assoc] using
                      splitToListEq rightAddr.render rightPre
                        (fun x : Char => decide (x = '/')) '/' (by simp)
                        hrightAddr (noSlashOfDigitsBetween hright.2)
                  have hsplits :=
                    congrArg (fun s : String => s.splitToList (· = '/')) h
                  rw [hsplitLeft, hsplitRight] at hsplits
                  simp only [List.cons.injEq, and_true] at hsplits
                  have heq :=
                    Addr.render_injective hleft.1 hright.1 hsplits.1
                  change leftAddr = rightAddr at heq
                  subst rightAddr
                  have hpre := hsplits.2
                  subst rightPre
                  rfl

private theorem left_wf_of_parts {parts : List String}
    (hne : parts ≠ []) (hlength : parts.length ≤ 7)
    (hall : ∀ part ∈ parts, HexValid part) :
    IPv6.IsWf.Left (renderGroups parts) := by
  exact
    ⟨parts, by
      cases parts with
      | nil => exact (hne rfl).elim
      | cons _ _ => simp,
      hlength, hall, rfl⟩

private theorem right_wf_of_parts {parts : List String}
    (hne : parts ≠ []) (hlength : parts.length ≤ 7)
    (hall : ∀ part ∈ parts, HexValid part) :
    IPv6.IsWf.Right (renderGroups parts) := by
  exact
    ⟨parts, by
      cases parts with
      | nil => exact (hne rfl).elim
      | cons _ _ => simp,
      hlength, hall, rfl⟩

theorem surface_addr_wf (addr : Addr) (h : addr.SyntaxValid) :
    IPv6.IsWf.V6Addr addr.render := by
  cases addr with
  | full parts =>
      left
      exact
        ⟨parts, Nat.le_of_eq h.1.symm, Nat.le_of_eq h.1, h.2, rfl⟩
  | compressed leftParts rightParts =>
      right
      have hright :
          IPv6.IsWf.Right (renderGroups rightParts) ∨
            renderGroups rightParts = "" := by
        cases rightParts with
        | nil =>
            exact Or.inr (by simp [renderGroups])
        | cons part parts =>
            exact Or.inl
              (right_wf_of_parts (by simp) h.2.1 h.2.2.2)
      cases leftParts with
      | nil =>
          right
          exact
            ⟨renderGroups rightParts,
              by simp [Addr.render, renderGroups, String.append_assoc],
              hright⟩
      | cons part parts =>
          left
          refine
            ⟨renderGroups (part :: parts), "::" ++ renderGroups rightParts,
              by simp [Addr.render, String.append_assoc], ?_, ?_⟩
          · exact
              left_wf_of_parts (by simp) h.1 h.2.2.1
          · exact ⟨renderGroups rightParts, rfl, hright⟩

theorem surface_wf_of_view (v : View) (h : v.SyntaxValid) :
    IPv6.IsWf.V6Net v.render := by
  cases v with
  | mk addr pre =>
      cases pre with
      | none =>
          left
          simpa [View.render, renderNet] using surface_addr_wf addr h.1
      | some pre =>
          right
          refine ⟨addr.render, pre, ?_⟩
          exact
            ⟨⟨by simpa [View.render, renderNet, String.append_assoc],
                surface_addr_wf addr h.1⟩,
              h.2⟩

theorem decode_eq_of_view (v : View) (h : v.SyntaxValid) :
    decode IPv6.grammar v.render = some v.captures := by
  have hgrammar : Triptych.IsWf IPv6.grammar v.render :=
    (IPv6.IsWfGrammar_equiv v.render).mpr (surface_wf_of_view v h)
  have hsome : (decode IPv6.grammar v.render).isSome = true :=
    (decodeSome_iff_IsWf IPv6.grammar (by decide) v.render).mpr hgrammar
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨parsed, hcaptures, hrenders, hsyntax⟩ := decode_ipv6_sound hm
  have heq : parsed = v :=
    View.render_injective hsyntax h hrenders.symm
  subst parsed
  simpa [hcaptures] using hm

private theorem optionMap_or {α β : Type} (f : α → β)
    (left right : Option α) :
    Option.map f (left.or right) =
      (Option.map f left).or (Option.map f right) := by
  cases left <;> cases right <;> rfl

@[simp] private theorem captureToEnv_nil (key : String) :
    CaptureMap.toEnv [] key = none := by
  simp [CaptureMap.toEnv]

@[simp] private theorem captureToEnv_cons_same
    (key captured : String) (rest : CaptureMap) :
    CaptureMap.toEnv ((key, captured) :: rest) key = some captured := by
  simp [CaptureMap.toEnv]

@[simp] private theorem captureToEnv_cons_ne
    (name captured key : String) (rest : CaptureMap) (hne : name ≠ key) :
    CaptureMap.toEnv ((name, captured) :: rest) key =
      CaptureMap.toEnv rest key := by
  simp [CaptureMap.toEnv, hne]

@[simp] private theorem captureToEnv_append
    (left right : CaptureMap) (key : String) :
    (left ++ right).toEnv key = (left.toEnv key).or (right.toEnv key) := by
  induction left with
  | nil => simp [CaptureMap.toEnv]
  | cons entry left ih =>
      rcases entry with ⟨name, captured⟩
      by_cases heq : name == key
      · simp [CaptureMap.toEnv, heq]
      · simp [CaptureMap.toEnv, heq, ih, optionMap_or]

@[simp] private theorem captureToEnvList_append
    (left right : CaptureMap) (key : String) :
    (left ++ right).toEnvList key =
      left.toEnvList key ++ right.toEnvList key := by
  simp [CaptureMap.toEnvList, List.filter_append]

@[simp] private theorem captureToEnvList_nil (key : String) :
    CaptureMap.toEnvList [] key = [] := by
  simp [CaptureMap.toEnvList]

@[simp] private theorem captureToEnvList_cons_same
    (key captured : String) (rest : CaptureMap) :
    CaptureMap.toEnvList ((key, captured) :: rest) key =
      captured :: CaptureMap.toEnvList rest key := by
  simp [CaptureMap.toEnvList]

@[simp] private theorem captureToEnvList_cons_ne
    (name captured key : String) (rest : CaptureMap) (hne : name ≠ key) :
    CaptureMap.toEnvList ((name, captured) :: rest) key =
      CaptureMap.toEnvList rest key := by
  simp [CaptureMap.toEnvList, hne]

@[simp] private theorem hextetFlatMap_toEnv_absent
    (parts : List String) (parent name key : String)
    (hname : name ≠ key) (hqualified : parent ++ "." ++ name ≠ key) :
    CaptureMap.toEnv (parts.flatMap (hextetCaptures parent name)) key = none := by
  induction parts with
  | nil => simp [CaptureMap.toEnv]
  | cons part parts ih =>
      rw [List.flatMap_cons, captureToEnv_append, ih]
      simp [hextetCaptures, CaptureMap.toEnv, hname, hqualified]

@[simp] private theorem hextetFlatMap_toEnvList_self
    (parts : List String) (parent name : String)
    (hqualified : parent ++ "." ++ name ≠ name) :
    CaptureMap.toEnvList (parts.flatMap (hextetCaptures parent name)) name =
      parts := by
  induction parts with
  | nil => rfl
  | cons part parts ih =>
      rw [List.flatMap_cons, captureToEnvList_append, ih]
      simp [hextetCaptures, CaptureMap.toEnvList, hqualified]

@[simp] private theorem hextetFlatMap_toEnvList_absent
    (parts : List String) (parent name key : String)
    (hname : name ≠ key) (hqualified : parent ++ "." ++ name ≠ key) :
    CaptureMap.toEnvList (parts.flatMap (hextetCaptures parent name)) key =
      [] := by
  induction parts with
  | nil => rfl
  | cons part parts ih =>
      rw [List.flatMap_cons, captureToEnvList_append, ih]
      simp [hextetCaptures, CaptureMap.toEnvList, hname, hqualified]

@[simp] private theorem readNat_repr (n : Nat) :
    Triptych.readNat n.repr = n := by
  simpa [Nat.toString_eq_repr] using CedarSupport.String.readNat_toString n

@[simp] theorem captures_h16l_count (v : View) :
    v.captures.toEnv.natVal "H16L#count" =
      match v.addr with
      | .full _ => 0
      | .compressed left _ => left.length := by
  cases v with
  | mk addr pre =>
      cases addr with
      | full parts =>
          cases pre <;>
            simp [View.captures, netCaptures, addrCaptures, fullCaptures,
              repeatedCaptures, prefixCaptures, hextetCaptures,
              Triptych.Env.natVal]
      | compressed left right =>
          cases left <;> cases right <;> cases pre <;>
            simp [View.captures, netCaptures, addrCaptures, compressedCaptures,
              optionalSideCaptures, sideCaptures, repeatedCaptures, prefixCaptures,
              hextetCaptures, Triptych.Env.natVal]

@[simp] theorem captures_h16r_count (v : View) :
    v.captures.toEnv.natVal "H16R#count" =
      match v.addr with
      | .full _ => 0
      | .compressed _ right => right.length := by
  cases v with
  | mk addr pre =>
      cases addr with
      | full parts =>
          cases pre <;>
            simp [View.captures, netCaptures, addrCaptures, fullCaptures,
              repeatedCaptures, prefixCaptures, hextetCaptures,
              Triptych.Env.natVal]
      | compressed left right =>
          cases left <;> cases right <;> cases pre <;>
            simp [View.captures, netCaptures, addrCaptures, compressedCaptures,
              optionalSideCaptures, sideCaptures, repeatedCaptures, prefixCaptures,
              hextetCaptures, Triptych.Env.natVal]

@[simp] theorem captures_prefix (v : View) :
    (v.captures.toEnv "Prefix").getD "" = v.«prefix».getD "" := by
  cases v with
  | mk addr pre =>
      cases addr with
      | full parts =>
          cases pre <;>
            simp [View.captures, netCaptures, addrCaptures, fullCaptures,
              repeatedCaptures, prefixCaptures, hextetCaptures]
      | compressed left right =>
          cases left <;> cases right <;> cases pre <;>
            simp [View.captures, netCaptures, addrCaptures, compressedCaptures,
              optionalSideCaptures, sideCaptures, repeatedCaptures, prefixCaptures,
              hextetCaptures]

@[simp] theorem captures_h16 (v : View) :
    v.captures.toEnvList "H16" =
      match v.addr with
      | .full parts => parts
      | .compressed _ _ => [] := by
  cases v with
  | mk addr pre =>
      cases addr with
      | full parts =>
          cases pre <;>
            simp [View.captures, netCaptures, addrCaptures, fullCaptures,
              repeatedCaptures, prefixCaptures, hextetCaptures]
      | compressed left right =>
          cases left <;> cases right <;> cases pre <;>
            simp [View.captures, netCaptures, addrCaptures, compressedCaptures,
              optionalSideCaptures, sideCaptures, repeatedCaptures, prefixCaptures,
              hextetCaptures]

@[simp] theorem captures_h16l (v : View) :
    v.captures.toEnvList "H16L" =
      match v.addr with
      | .full _ => []
      | .compressed left _ => left := by
  cases v with
  | mk addr pre =>
      cases addr with
      | full parts =>
          cases pre <;>
            simp [View.captures, netCaptures, addrCaptures, fullCaptures,
              repeatedCaptures, prefixCaptures, hextetCaptures]
      | compressed left right =>
          cases left <;> cases right <;> cases pre <;>
            simp [View.captures, netCaptures, addrCaptures, compressedCaptures,
              optionalSideCaptures, sideCaptures, repeatedCaptures, prefixCaptures,
              hextetCaptures]

@[simp] theorem captures_h16r (v : View) :
    v.captures.toEnvList "H16R" =
      match v.addr with
      | .full _ => []
      | .compressed _ right => right := by
  cases v with
  | mk addr pre =>
      cases addr with
      | full parts =>
          cases pre <;>
            simp [View.captures, netCaptures, addrCaptures, fullCaptures,
              repeatedCaptures, prefixCaptures, hextetCaptures]
      | compressed left right =>
          cases left <;> cases right <;> cases pre <;>
            simp [View.captures, netCaptures, addrCaptures, compressedCaptures,
              optionalSideCaptures, sideCaptures, repeatedCaptures, prefixCaptures,
              hextetCaptures]

theorem constraints_of_decode (v : View)
    (h : decode IPv6.grammar v.render = some v.captures) :
    IPv6.SatisfiesWfConstraints v.render ↔ v.Constraints := by
  rw [IPv6.SatisfiesWfConstraints_of_decode h]
  cases v with
  | mk addr pre =>
      cases addr <;> cases pre <;>
        simp [IPv6.WfConstraints, View.Constraints, Addr.Constraints,
          OptionalPrefixConstraints, PrefixConstraints, natOf, Triptych.readNat,
          and_assoc] <;>
        omega

/-- Accepted strings in the proof-facing IPv6 component normal form. -/
theorem isValid_iff_view (s : String) :
    IPv6.IsValid s ↔ ∃ v : View, v.render = s ∧ v.Valid := by
  constructor
  · rintro ⟨hgrammar, hconstraints⟩
    have hengine : Triptych.IsWf IPv6.grammar s :=
      (IPv6.IsWfGrammar_equiv s).mpr hgrammar
    have hsome : (decode IPv6.grammar s).isSome = true :=
      (decodeSome_iff_IsWf IPv6.grammar (by decide) s).mpr hengine
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨v, hcaptures, hrenders, hsyntax⟩ := decode_ipv6_sound hm
    have hdecode : decode IPv6.grammar v.render = some v.captures := by
      rw [← hrenders, ← hcaptures]
      exact hm
    have hviewConstraints : v.Constraints :=
      (constraints_of_decode v hdecode).mp (by simpa [hrenders] using hconstraints)
    exact ⟨v, hrenders.symm, hsyntax, hviewConstraints⟩
  · rintro ⟨v, hrender, hsyntax, hconstraints⟩
    have hdecode := decode_eq_of_view v hsyntax
    refine ⟨?_, ?_⟩
    · simpa [hrender] using surface_wf_of_view v hsyntax
    · have hsurface := (constraints_of_decode v hdecode).mpr hconstraints
      simpa [hrender] using hsurface

/-- The generated value is the denotation of every syntax-valid IPv6 view. -/
theorem computeValue_eq_of_view (v : View) (h : v.SyntaxValid) :
    IPv6.computeValue v.render = some v.denotation := by
  rw [IPv6.computeValue_of_decode (decode_eq_of_view v h)]
  cases v with
  | mk addr pre =>
      cases addr <;> simp [IPv6.value, View.denotation]

end IPv6.GrammarView
