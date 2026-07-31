import Generated.IPv4.parser
import CedarSupport.IPAddrInternals
import CedarSupport.String
import CedarSupport.StringInternals
import Triptych.Theorems.DecodeLemmas
import Triptych.Theorems.String

/-!
# IPv4 grammar capture view

Exact component, constraint, and denotation facts for Triptych's generated IPv4 grammar.
This module contains no theorem relating the grammar to Cedar's executable parser.
-/

open Cedar.Spec.Ext
open CedarSupport.String
open CedarSupport.StringInternals
open Triptych

namespace IPv4.GrammarView

open CedarSupport.IPAddrInternals

def OctetConstraints (s : String) : Prop :=
  (s.startsWith "0" → s = "0") ∧ natOf s ≤ 255

def OctetWf (s : String) : Prop :=
  IsDigitsBetween 1 3 s ∧ OctetConstraints s

def PrefixConstraints (size : Nat) (s : String) : Prop :=
  (s.startsWith "0" → s = "0") ∧ natOf s ≤ size

def PrefixWf (digits size : Nat) (s : String) : Prop :=
  IsDigitsBetween 1 digits s ∧ PrefixConstraints size s

def OptionalPrefixSyntax : Option String → Prop
  | none => True
  | some pre => IsDigitsBetween 1 2 pre

def OptionalPrefixConstraints : Option String → Prop
  | none => True
  | some pre => PrefixConstraints 32 pre

def OptionalPrefixWf : Option String → Prop
  | none => True
  | some pre => PrefixWf 2 32 pre

theorem optionalPrefixWf_iff (pre : Option String) :
    OptionalPrefixWf pre ↔ OptionalPrefixSyntax pre ∧ OptionalPrefixConstraints pre := by
  cases pre <;> simp [OptionalPrefixWf, OptionalPrefixSyntax, OptionalPrefixConstraints,
    PrefixWf]

def renderV4 (o₁ o₂ o₃ o₄ : String) (pre : Option String) : String :=
  o₁ ++ "." ++ o₂ ++ "." ++ o₃ ++ "." ++ o₄ ++
    match pre with
    | none => ""
    | some p => "/" ++ p

def v4AddrCaptures (o₁ o₂ o₃ o₄ : String) : CaptureMap :=
  let addr := o₁ ++ "." ++ o₂ ++ "." ++ o₃ ++ "." ++ o₄
  [("V4Addr", addr),
    ("Oct1", o₁), ("V4Addr.Oct1", o₁),
    ("Oct2", o₂), ("V4Addr.Oct2", o₂),
    ("Oct3", o₃), ("V4Addr.Oct3", o₃),
    ("Oct4", o₄), ("V4Addr.Oct4", o₄)]

def v4NetCaptures (o₁ o₂ o₃ o₄ : String) : Option String → CaptureMap
  | none => v4AddrCaptures o₁ o₂ o₃ o₄
  | some pre => v4AddrCaptures o₁ o₂ o₃ o₄ ++ [("Prefix", pre)]

/-- Proof-facing normal form for one selected IPv4 parse. This is the shape Triptych should
    eventually generate from the grammar, hiding decoder fuel, remainders, and capture maps
    from external-parser proofs. -/
structure View where
  oct1 : String
  oct2 : String
  oct3 : String
  oct4 : String
  cidrPrefix : Option String

namespace View

def render (v : View) : String :=
  renderV4 v.oct1 v.oct2 v.oct3 v.oct4 v.cidrPrefix

def captures (v : View) : CaptureMap :=
  v4NetCaptures v.oct1 v.oct2 v.oct3 v.oct4 v.cidrPrefix

def SyntaxValid (v : View) : Prop :=
  IsDigitsBetween 1 3 v.oct1 ∧ IsDigitsBetween 1 3 v.oct2 ∧
    IsDigitsBetween 1 3 v.oct3 ∧ IsDigitsBetween 1 3 v.oct4 ∧
    OptionalPrefixSyntax v.cidrPrefix

def Valid (v : View) : Prop :=
  OctetWf v.oct1 ∧ OctetWf v.oct2 ∧ OctetWf v.oct3 ∧ OctetWf v.oct4 ∧
    OptionalPrefixWf v.cidrPrefix

def denotation (v : View) : CedarExamples.IPv4.IPv4Net :=
  CedarExamples.IPv4.toIPv4Net v.oct1 v.oct2 v.oct3 v.oct4 (v.cidrPrefix.getD "")

end View

theorem octet_mem (fuel : Nat) (name : String)
    (hprod :
      IPv4.grammar.prod? name =
        some
          (Production.mk name
            [[SymItem.mk (Sym.term TokClass.digit (LenSpec.between 1 3)) false]]))
    (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym IPv4.grammar "V4Addr" (fuel + 1) (Sym.ref name) cs ↔
      ∃ octet,
        m = [(name, octet), ("V4Addr." ++ name, octet)] ∧
        cs = octet.toList ++ r ∧ IsDigitsBetween 1 3 octet := by
  rw [mem_matchSym_ref_single_term_qualified_iff IPv4.grammar "V4Addr" fuel
    name name TokClass.digit (LenSpec.between 1 3) hprod]
  constructor
  · rintro ⟨p, hm, hcs, hwf⟩
    refine ⟨String.ofList p, ?_, ?_, ?_⟩
    · simpa using hm
    · simpa using hcs
    · simpa [IsDigitsBetween_matchesTerm] using hwf
  · rintro ⟨octet, rfl, hcs, hwf⟩
    refine ⟨octet.toList, ?_, ?_, ?_⟩
    · simp
    · simpa using hcs
    · simpa [IsDigitsBetween_matchesTerm] using hwf

theorem v4Addr_mem (fuel : Nat) (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym IPv4.grammar "" (fuel + 2) (Sym.ref "V4Addr") cs ↔
      ∃ o₁ o₂ o₃ o₄,
        m = v4AddrCaptures o₁ o₂ o₃ o₄ ∧
        cs = (o₁ ++ "." ++ o₂ ++ "." ++ o₃ ++ "." ++ o₄).toList ++ r ∧
        IsDigitsBetween 1 3 o₁ ∧ IsDigitsBetween 1 3 o₂ ∧
        IsDigitsBetween 1 3 o₃ ∧ IsDigitsBetween 1 3 o₄ := by
  rw [mem_matchSym_ref_iff IPv4.grammar "" (fuel + 1) "V4Addr" _ rfl]
  constructor
  · rintro ⟨inner, hinner, rfl⟩
    rw [matchProd] at hinner
    simp only [List.mem_flatMap, List.mem_singleton, exists_eq_left] at hinner
    obtain ⟨m₁, r₁, mt₁, h₁, ht₁, rfl⟩ :=
      (mem_matchSeq_cons_required_iff IPv4.grammar "V4Addr" (fuel + 1) _ _ rfl
        cs r inner).mp hinner
    obtain ⟨md₁, rd₁, mt₂, hd₁, ht₂, rfl⟩ :=
      (mem_matchSeq_cons_required_iff IPv4.grammar "V4Addr" (fuel + 1) _ _ rfl
        r₁ r mt₁).mp ht₁
    obtain ⟨m₂, r₂, mt₃, h₂, ht₃, rfl⟩ :=
      (mem_matchSeq_cons_required_iff IPv4.grammar "V4Addr" (fuel + 1) _ _ rfl
        rd₁ r mt₂).mp ht₂
    obtain ⟨md₂, rd₂, mt₄, hd₂, ht₄, rfl⟩ :=
      (mem_matchSeq_cons_required_iff IPv4.grammar "V4Addr" (fuel + 1) _ _ rfl
        r₂ r mt₃).mp ht₃
    obtain ⟨m₃, r₃, mt₅, h₃, ht₅, rfl⟩ :=
      (mem_matchSeq_cons_required_iff IPv4.grammar "V4Addr" (fuel + 1) _ _ rfl
        rd₂ r mt₄).mp ht₄
    obtain ⟨md₃, rd₃, mt₆, hd₃, ht₆, rfl⟩ :=
      (mem_matchSeq_cons_required_iff IPv4.grammar "V4Addr" (fuel + 1) _ _ rfl
        r₃ r mt₅).mp ht₅
    obtain ⟨m₄, r₄, mnil, h₄, hnil, rfl⟩ :=
      (mem_matchSeq_cons_required_iff IPv4.grammar "V4Addr" (fuel + 1) _ _ rfl
        rd₃ r mt₆).mp ht₆
    simp only [matchSeq, List.mem_singleton, Prod.mk.injEq] at hnil
    obtain ⟨rfl, rfl⟩ := hnil
    obtain ⟨o₁, rfl, hcs, hwf₁⟩ := (octet_mem fuel "Oct1" rfl _ _ _).mp h₁
    obtain ⟨rfl, hd₁cs⟩ :=
      (mem_matchSym_lit_iff IPv4.grammar "V4Addr" (fuel + 1) "." _ _ _).mp hd₁
    obtain ⟨o₂, rfl, ho₂, hwf₂⟩ := (octet_mem fuel "Oct2" rfl _ _ _).mp h₂
    obtain ⟨rfl, hd₂cs⟩ :=
      (mem_matchSym_lit_iff IPv4.grammar "V4Addr" (fuel + 1) "." _ _ _).mp hd₂
    obtain ⟨o₃, rfl, ho₃, hwf₃⟩ := (octet_mem fuel "Oct3" rfl _ _ _).mp h₃
    obtain ⟨rfl, hd₃cs⟩ :=
      (mem_matchSym_lit_iff IPv4.grammar "V4Addr" (fuel + 1) "." _ _ _).mp hd₃
    obtain ⟨o₄, rfl, ho₄, hwf₄⟩ := (octet_mem fuel "Oct4" rfl _ _ _).mp h₄
    have hparts :
        cs =
          (o₁ ++ "." ++ o₂ ++ "." ++ o₃ ++ "." ++ o₄).toList ++ r := by
      simp [hcs, hd₁cs, ho₂, hd₂cs, ho₃, hd₃cs, ho₄, String.toList_append,
        List.append_assoc]
    have hconsumed :
      String.ofList (cs.take (cs.length - r.length)) =
          o₁ ++ "." ++ o₂ ++ "." ++ o₃ ++ "." ++ o₄ := by
      simpa only [String.ofList_toList] using consumed_eq_of_append hparts
    exact ⟨o₁, o₂, o₃, o₄,
      by simp [v4AddrCaptures, hconsumed, String.append_assoc], hparts,
      hwf₁, hwf₂, hwf₃, hwf₄⟩
  · rintro ⟨o₁, o₂, o₃, o₄, rfl, hcs, hwf₁, hwf₂, hwf₃, hwf₄⟩
    refine ⟨
      [("Oct1", o₁), ("V4Addr.Oct1", o₁),
        ("Oct2", o₂), ("V4Addr.Oct2", o₂),
        ("Oct3", o₃), ("V4Addr.Oct3", o₃),
        ("Oct4", o₄), ("V4Addr.Oct4", o₄)], ?_, ?_⟩
    · rw [matchProd]
      simp only [List.mem_flatMap, List.mem_singleton, exists_eq_left]
      rw [mem_matchSeq_cons_required_iff IPv4.grammar "V4Addr" (fuel + 1) _ _ rfl]
      refine ⟨[("Oct1", o₁), ("V4Addr.Oct1", o₁)],
        '.' :: (o₂ ++ "." ++ o₃ ++ "." ++ o₄).toList ++ r,
        [("Oct2", o₂), ("V4Addr.Oct2", o₂),
          ("Oct3", o₃), ("V4Addr.Oct3", o₃),
          ("Oct4", o₄), ("V4Addr.Oct4", o₄)], ?_, ?_, by simp⟩
      · exact (octet_mem fuel "Oct1" rfl _ _ _).mpr
          ⟨o₁, rfl, by
            simpa [String.toList_append, List.append_assoc] using hcs, hwf₁⟩
      · rw [mem_matchSeq_cons_required_iff IPv4.grammar "V4Addr" (fuel + 1) _ _ rfl]
        refine ⟨[], (o₂ ++ "." ++ o₃ ++ "." ++ o₄).toList ++ r,
          [("Oct2", o₂), ("V4Addr.Oct2", o₂),
            ("Oct3", o₃), ("V4Addr.Oct3", o₃),
            ("Oct4", o₄), ("V4Addr.Oct4", o₄)], ?_, ?_, by simp⟩
        · exact (mem_matchSym_lit_iff IPv4.grammar "V4Addr" (fuel + 1) "." _ _ _).mpr
            ⟨rfl, by simp⟩
        · rw [mem_matchSeq_cons_required_iff IPv4.grammar "V4Addr" (fuel + 1) _ _ rfl]
          refine ⟨[("Oct2", o₂), ("V4Addr.Oct2", o₂)],
            '.' :: (o₃ ++ "." ++ o₄).toList ++ r,
            [("Oct3", o₃), ("V4Addr.Oct3", o₃),
              ("Oct4", o₄), ("V4Addr.Oct4", o₄)], ?_, ?_, by simp⟩
          · exact (octet_mem fuel "Oct2" rfl _ _ _).mpr
              ⟨o₂, rfl, by simp [String.toList_append, List.append_assoc], hwf₂⟩
          · rw [mem_matchSeq_cons_required_iff IPv4.grammar "V4Addr" (fuel + 1) _ _ rfl]
            refine ⟨[], (o₃ ++ "." ++ o₄).toList ++ r,
              [("Oct3", o₃), ("V4Addr.Oct3", o₃),
                ("Oct4", o₄), ("V4Addr.Oct4", o₄)], ?_, ?_, by simp⟩
            · exact
                (mem_matchSym_lit_iff IPv4.grammar "V4Addr" (fuel + 1) "." _ _ _).mpr
                  ⟨rfl, by simp⟩
            · rw [mem_matchSeq_cons_required_iff IPv4.grammar "V4Addr"
                (fuel + 1) _ _ rfl]
              refine ⟨[("Oct3", o₃), ("V4Addr.Oct3", o₃)],
                '.' :: o₄.toList ++ r,
                [("Oct4", o₄), ("V4Addr.Oct4", o₄)], ?_, ?_, by simp⟩
              · exact (octet_mem fuel "Oct3" rfl _ _ _).mpr
                  ⟨o₃, rfl, by simp [String.toList_append, List.append_assoc], hwf₃⟩
              · rw [mem_matchSeq_cons_required_iff IPv4.grammar "V4Addr"
                  (fuel + 1) _ _ rfl]
                refine ⟨[], o₄.toList ++ r,
                  [("Oct4", o₄), ("V4Addr.Oct4", o₄)], ?_, ?_, by simp⟩
                · exact
                    (mem_matchSym_lit_iff IPv4.grammar "V4Addr"
                      (fuel + 1) "." _ _ _).mpr ⟨rfl, by simp⟩
                · rw [mem_matchSeq_cons_required_iff IPv4.grammar "V4Addr"
                    (fuel + 1) _ _ rfl]
                  refine ⟨[("Oct4", o₄), ("V4Addr.Oct4", o₄)], r, [],
                    ?_, by simp [matchSeq], by simp⟩
                  exact (octet_mem fuel "Oct4" rfl _ _ _).mpr
                    ⟨o₄, rfl, rfl, hwf₄⟩
    · have hconsumed :
          String.ofList (cs.take (cs.length - r.length)) =
            o₁ ++ "." ++ o₂ ++ "." ++ o₃ ++ "." ++ o₄ := by
        simpa only [String.ofList_toList] using consumed_eq_of_append hcs
      simp [v4AddrCaptures, hconsumed, String.append_assoc]

theorem prefix_mem (fuel : Nat) (cs r : List Char) (m : CaptureMap) :
    (m, r) ∈ matchSym IPv4.grammar "" (fuel + 1) (Sym.ref "Prefix") cs ↔
      ∃ pre,
        m = [("Prefix", pre)] ∧
        cs = pre.toList ++ r ∧ IsDigitsBetween 1 2 pre := by
  rw [mem_matchSym_ref_single_term_iff IPv4.grammar fuel "Prefix" "Prefix"
    TokClass.digit (LenSpec.between 1 2) rfl]
  constructor
  · rintro ⟨p, rfl, hcs, hwf⟩
    exact ⟨String.ofList p, by simp, by simpa using hcs,
      by simpa [IsDigitsBetween_matchesTerm] using hwf⟩
  · rintro ⟨pre, rfl, hcs, hwf⟩
    exact ⟨pre.toList, by simp, by simpa using hcs,
      by simpa [IsDigitsBetween_matchesTerm] using hwf⟩

theorem v4Net_match_sound (fuel : Nat) (cs r : List Char) (m : CaptureMap)
    (hmem :
      (m, r) ∈
        matchProd IPv4.grammar "" (fuel + 2)
          (Production.mk "V4Net"
            [[SymItem.mk (Sym.ref "V4Addr") false],
              [SymItem.mk (Sym.ref "V4Addr") false,
                SymItem.mk (Sym.lit "/") false,
                SymItem.mk (Sym.ref "Prefix") false]]) cs) :
    ∃ o₁ o₂ o₃ o₄ pre,
      m = v4NetCaptures o₁ o₂ o₃ o₄ pre ∧
      cs = (renderV4 o₁ o₂ o₃ o₄ pre).toList ++ r ∧
      IsDigitsBetween 1 3 o₁ ∧ IsDigitsBetween 1 3 o₂ ∧
      IsDigitsBetween 1 3 o₃ ∧ IsDigitsBetween 1 3 o₄ ∧
      OptionalPrefixSyntax pre := by
  rw [matchProd] at hmem
  simp only [List.mem_flatMap, List.mem_cons, List.mem_singleton,
    exists_eq_or_imp, exists_eq_left] at hmem
  rcases hmem with hbare | hprefixAlt
  · obtain ⟨maddr, mid, mnil, haddr, hnil, rfl⟩ :=
      (mem_matchSeq_cons_required_iff IPv4.grammar "" (fuel + 2) _ _ rfl
        cs r m).mp hbare
    simp only [matchSeq, List.mem_singleton, Prod.mk.injEq] at hnil
    obtain ⟨rfl, rfl⟩ := hnil
    obtain ⟨o₁, o₂, o₃, o₄, rfl, hcs, h₁, h₂, h₃, h₄⟩ :=
      (v4Addr_mem fuel cs r maddr).mp haddr
    exact ⟨o₁, o₂, o₃, o₄, none, by simp [v4NetCaptures],
      by simpa [renderV4] using hcs, h₁, h₂, h₃, h₄, trivial⟩
  · obtain ⟨maddr, raddr, mtail, haddr, htail, rfl⟩ :=
      (mem_matchSeq_cons_required_iff IPv4.grammar "" (fuel + 2) _ _ rfl
        cs r m).mp (by
          rcases hprefixAlt with hprefixAlt | ⟨a, ha, _⟩
          · exact hprefixAlt
          · simp at ha)
    obtain ⟨mslash, rslash, mprefixTail, hslash, hprefixTail, rfl⟩ :=
      (mem_matchSeq_cons_required_iff IPv4.grammar "" (fuel + 2) _ _ rfl
        raddr r mtail).mp htail
    obtain ⟨mprefix, rprefix, mnil, hpre, hnil, rfl⟩ :=
      (mem_matchSeq_cons_required_iff IPv4.grammar "" (fuel + 2) _ _ rfl
        rslash r mprefixTail).mp hprefixTail
    simp only [matchSeq, List.mem_singleton, Prod.mk.injEq] at hnil
    obtain ⟨rfl, rfl⟩ := hnil
    obtain ⟨o₁, o₂, o₃, o₄, rfl, hcs, h₁, h₂, h₃, h₄⟩ :=
      (v4Addr_mem fuel cs raddr maddr).mp haddr
    obtain ⟨rfl, hslashcs⟩ :=
      (mem_matchSym_lit_iff IPv4.grammar "" (fuel + 2) "/" _ _ _).mp hslash
    obtain ⟨pre, rfl, hprecs, hp⟩ :=
      (prefix_mem (fuel + 1) rslash r mprefix).mp hpre
    refine ⟨o₁, o₂, o₃, o₄, some pre, by simp [v4NetCaptures], ?_,
      h₁, h₂, h₃, h₄, hp⟩
    simp [hcs, hslashcs, hprecs, renderV4, String.toList_append, List.append_assoc]

theorem decode_ipv4_sound {s : String} {m : CaptureMap}
    (h : decode IPv4.grammar s = some m) :
    ∃ o₁ o₂ o₃ o₄ pre,
      m = v4NetCaptures o₁ o₂ o₃ o₄ pre ∧
      s = renderV4 o₁ o₂ o₃ o₄ pre ∧
      IsDigitsBetween 1 3 o₁ ∧ IsDigitsBetween 1 3 o₂ ∧
      IsDigitsBetween 1 3 o₃ ∧ IsDigitsBetween 1 3 o₄ ∧
      OptionalPrefixSyntax pre := by
  obtain ⟨p, hstart, hmem⟩ := mem_matchProd_of_decode_eq_some h
  have hp :
      p =
        Production.mk "V4Net"
          [[SymItem.mk (Sym.ref "V4Addr") false],
            [SymItem.mk (Sym.ref "V4Addr") false,
              SymItem.mk (Sym.lit "/") false,
              SymItem.mk (Sym.ref "Prefix") false]] := by
    have hknown :
        IPv4.grammar.startProd? =
          some
            (Production.mk "V4Net"
              [[SymItem.mk (Sym.ref "V4Addr") false],
                [SymItem.mk (Sym.ref "V4Addr") false,
                  SymItem.mk (Sym.lit "/") false,
                  SymItem.mk (Sym.ref "Prefix") false]]) := rfl
    rw [hknown] at hstart
    exact (Option.some.inj hstart).symm
  subst p
  have hxmem :
      (m, ([] : List Char)) ∈
        matchProd IPv4.grammar "" 7
          (Production.mk "V4Net"
            [[SymItem.mk (Sym.ref "V4Addr") false],
              [SymItem.mk (Sym.ref "V4Addr") false,
                SymItem.mk (Sym.lit "/") false,
                SymItem.mk (Sym.ref "Prefix") false]]) s.toList := by
    simpa [IPv4.grammar] using hmem
  obtain ⟨o₁, o₂, o₃, o₄, pre, hm, hs, h₁, h₂, h₃, h₄, hp⟩ :=
    v4Net_match_sound 5 s.toList [] m hxmem
  refine ⟨o₁, o₂, o₃, o₄, pre, hm, ?_, h₁, h₂, h₃, h₄, hp⟩
  rw [← String.toList_inj]
  simpa using hs

theorem decode_parts_of_surface_wf {s : String} (h : IPv4.IsWf.V4Net s) :
    ∃ o₁ o₂ o₃ o₄ pre,
      decode IPv4.grammar s = some (v4NetCaptures o₁ o₂ o₃ o₄ pre) ∧
      s = renderV4 o₁ o₂ o₃ o₄ pre ∧
      IsDigitsBetween 1 3 o₁ ∧ IsDigitsBetween 1 3 o₂ ∧
      IsDigitsBetween 1 3 o₃ ∧ IsDigitsBetween 1 3 o₄ ∧
      OptionalPrefixSyntax pre := by
  have hwf : Triptych.IsWf IPv4.grammar s := (IPv4.IsWfGrammar_equiv s).mpr h
  have hsome : (decode IPv4.grammar s).isSome = true :=
    (decodeSome_iff_IsWf IPv4.grammar (by decide) s).mpr hwf
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨o₁, o₂, o₃, o₄, pre, rfl, hs, h₁, h₂, h₃, h₄, hp⟩ :=
    decode_ipv4_sound hm
  exact ⟨o₁, o₂, o₃, o₄, pre, hm, hs, h₁, h₂, h₃, h₄, hp⟩

/-- A surface-well-formed string has one decoder-selected view with exact captures. -/
theorem decode_view_of_surface_wf {s : String} (h : IPv4.IsWf.V4Net s) :
    ∃ v : View,
      decode IPv4.grammar s = some v.captures ∧ v.render = s ∧ v.SyntaxValid := by
  obtain ⟨o₁, o₂, o₃, o₄, pre, hdecode, hs, h₁, h₂, h₃, h₄, hp⟩ :=
    decode_parts_of_surface_wf h
  exact ⟨⟨o₁, o₂, o₃, o₄, pre⟩, hdecode, hs.symm, h₁, h₂, h₃, h₄, hp⟩

theorem wf_constraints_of_decode (s o₁ o₂ o₃ o₄ : String) (pre : Option String)
    (h : decode IPv4.grammar s = some (v4NetCaptures o₁ o₂ o₃ o₄ pre)) :
    IPv4.SatisfiesWfConstraints s ↔
      OctetConstraints o₁ ∧ OctetConstraints o₂ ∧
      OctetConstraints o₃ ∧ OctetConstraints o₄ ∧
      OptionalPrefixConstraints pre := by
  have nonneg (x : String) : (0 : Int) ≤ natOf x := by
    simp [natOf]
  rw [IPv4.SatisfiesWfConstraints_of_decode h]
  cases pre with
  | none =>
    unfold IPv4.WfConstraints
    simp [v4NetCaptures, v4AddrCaptures, CaptureMap.toEnv]
    simp only [nonneg, true_and]
    have hempty : natOf "" = 0 := by simp [natOf, readNat]
    simp [OctetConstraints, OptionalPrefixConstraints, PrefixConstraints,
      hempty, and_assoc]
  | some pre =>
    unfold IPv4.WfConstraints
    simp [v4NetCaptures, v4AddrCaptures, CaptureMap.toEnv]
    simp only [nonneg, true_and]
    simp [OctetConstraints, OptionalPrefixConstraints, PrefixConstraints, and_assoc]

theorem format_compute_of_decode (s o₁ o₂ o₃ o₄ : String) (pre : Option String)
    (h : decode IPv4.grammar s = some (v4NetCaptures o₁ o₂ o₃ o₄ pre)) :
    IPv4.computeValue s =
      some (CedarExamples.IPv4.toIPv4Net o₁ o₂ o₃ o₄ (pre.getD "")) := by
  rw [IPv4.computeValue_of_decode h]
  cases pre <;>
    simp [IPv4.value, v4NetCaptures, v4AddrCaptures, CaptureMap.toEnv]

private theorem noDotOfDigitsBetween {lo hi : Nat} {s : String}
    (h : IsDigitsBetween lo hi s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = '.')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq
  subst c
  have hdigit := h.1 '.' hc
  simp [TokClass.mem] at hdigit

private theorem noSlashOfDigitsBetween {lo hi : Nat} {s : String}
    (h : IsDigitsBetween lo hi s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = '/')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq
  subst c
  have hdigit := h.1 '/' hc
  simp [TokClass.mem] at hdigit

private theorem noSlashAppend {s₁ s₂ : String}
    (h₁ : ∀ c ∈ s₁.toList, (fun x : Char => decide (x = '/')) c = false)
    (h₂ : ∀ c ∈ s₂.toList, (fun x : Char => decide (x = '/')) c = false) :
    ∀ c ∈ (s₁ ++ s₂).toList, (fun x : Char => decide (x = '/')) c = false := by
  intro c hc
  rw [String.toList_append] at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact h₁ c hc
  · exact h₂ c hc

private theorem noSlashDot :
    ∀ c ∈ ".".toList, (fun x : Char => decide (x = '/')) c = false := by
  simp

private theorem noSlashOfDigitAddr {o₁ o₂ o₃ o₄ : String}
    (h₁ : IsDigitsBetween 1 3 o₁) (h₂ : IsDigitsBetween 1 3 o₂)
    (h₃ : IsDigitsBetween 1 3 o₃) (h₄ : IsDigitsBetween 1 3 o₄) :
    ∀ c ∈ (o₁ ++ "." ++ o₂ ++ "." ++ o₃ ++ "." ++ o₄).toList,
      (fun x : Char => decide (x = '/')) c = false := by
  simpa [String.append_assoc] using
    noSlashAppend (noSlashOfDigitsBetween h₁)
      (noSlashAppend noSlashDot
        (noSlashAppend (noSlashOfDigitsBetween h₂)
          (noSlashAppend noSlashDot
            (noSlashAppend (noSlashOfDigitsBetween h₃)
              (noSlashAppend noSlashDot (noSlashOfDigitsBetween h₄))))))

private theorem digitAddr_injective {o₁ o₂ o₃ o₄ p₁ p₂ p₃ p₄ : String}
    (ho₁ : IsDigitsBetween 1 3 o₁) (ho₂ : IsDigitsBetween 1 3 o₂)
    (ho₃ : IsDigitsBetween 1 3 o₃) (ho₄ : IsDigitsBetween 1 3 o₄)
    (hp₁ : IsDigitsBetween 1 3 p₁) (hp₂ : IsDigitsBetween 1 3 p₂)
    (hp₃ : IsDigitsBetween 1 3 p₃) (hp₄ : IsDigitsBetween 1 3 p₄)
    (h :
      o₁ ++ "." ++ o₂ ++ "." ++ o₃ ++ "." ++ o₄ =
        p₁ ++ "." ++ p₂ ++ "." ++ p₃ ++ "." ++ p₄) :
    o₁ = p₁ ∧ o₂ = p₂ ∧ o₃ = p₃ ∧ o₄ = p₄ := by
  have hparts :
      [o₁, o₂, o₃, o₄] = [p₁, p₂, p₃, p₄] := by
    apply Triptych.intercalate_injective (left := [o₁, o₂, o₃, o₄])
      (right := [p₁, p₂, p₃, p₄]) (by simp) (by simp) '.'
    · intro part hpart c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpart
      rcases hpart with rfl | rfl | rfl | rfl
      · exact noDotOfDigitsBetween ho₁ c hc
      · exact noDotOfDigitsBetween ho₂ c hc
      · exact noDotOfDigitsBetween ho₃ c hc
      · exact noDotOfDigitsBetween ho₄ c hc
    · intro part hpart c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpart
      rcases hpart with rfl | rfl | rfl | rfl
      · exact noDotOfDigitsBetween hp₁ c hc
      · exact noDotOfDigitsBetween hp₂ c hc
      · exact noDotOfDigitsBetween hp₃ c hc
      · exact noDotOfDigitsBetween hp₄ c hc
    · repeat rw [String.intercalate_cons_cons]
      rw [String.intercalate_singleton]
      simpa [String.append_assoc] using h
  simpa using hparts

theorem renderV4_injective {o₁ o₂ o₃ o₄ p₁ p₂ p₃ p₄ : String}
    {pre₁ pre₂ : Option String}
    (ho₁ : IsDigitsBetween 1 3 o₁) (ho₂ : IsDigitsBetween 1 3 o₂)
    (ho₃ : IsDigitsBetween 1 3 o₃) (ho₄ : IsDigitsBetween 1 3 o₄)
    (hp₁ : IsDigitsBetween 1 3 p₁) (hp₂ : IsDigitsBetween 1 3 p₂)
    (hp₃ : IsDigitsBetween 1 3 p₃) (hp₄ : IsDigitsBetween 1 3 p₄)
    (hpre₁ : OptionalPrefixSyntax pre₁)
    (hpre₂ : OptionalPrefixSyntax pre₂)
    (h : renderV4 o₁ o₂ o₃ o₄ pre₁ = renderV4 p₁ p₂ p₃ p₄ pre₂) :
    o₁ = p₁ ∧ o₂ = p₂ ∧ o₃ = p₃ ∧ o₄ = p₄ ∧ pre₁ = pre₂ := by
  let addr₁ := o₁ ++ "." ++ o₂ ++ "." ++ o₃ ++ "." ++ o₄
  let addr₂ := p₁ ++ "." ++ p₂ ++ "." ++ p₃ ++ "." ++ p₄
  have haddr₁ :
      ∀ c ∈ addr₁.toList, (fun x : Char => decide (x = '/')) c = false :=
    noSlashOfDigitAddr ho₁ ho₂ ho₃ ho₄
  have haddr₂ :
      ∀ c ∈ addr₂.toList, (fun x : Char => decide (x = '/')) c = false :=
    noSlashOfDigitAddr hp₁ hp₂ hp₃ hp₄
  cases pre₁ with
  | none =>
    have hsplit₁ : (renderV4 o₁ o₂ o₃ o₄ none).splitToList (· = '/') = [addr₁] := by
      simpa [renderV4, addr₁, String.append_assoc] using
        splitToListNoSep addr₁ (fun x : Char => decide (x = '/')) haddr₁
    cases pre₂ with
    | none =>
      have hsplit₂ :
          (renderV4 p₁ p₂ p₃ p₄ none).splitToList (· = '/') = [addr₂] := by
        simpa [renderV4, addr₂, String.append_assoc] using
          splitToListNoSep addr₂ (fun x : Char => decide (x = '/')) haddr₂
      have hsplits := congrArg (fun s : String => s.splitToList (· = '/')) h
      rw [hsplit₁, hsplit₂] at hsplits
      have haddr : addr₁ = addr₂ := by simpa using hsplits
      obtain ⟨h₁, h₂, h₃, h₄⟩ :=
        digitAddr_injective ho₁ ho₂ ho₃ ho₄ hp₁ hp₂ hp₃ hp₄ haddr
      exact ⟨h₁, h₂, h₃, h₄, rfl⟩
    | some pre₂ =>
      have hsplit₂ :
          (renderV4 p₁ p₂ p₃ p₄ (some pre₂)).splitToList (· = '/') =
            [addr₂, pre₂] := by
        simpa [renderV4, addr₂, String.append_assoc] using
          splitToListEq addr₂ pre₂ (fun x : Char => decide (x = '/')) '/'
            (by simp) haddr₂ (noSlashOfDigitsBetween hpre₂)
      have hsplits := congrArg (fun s : String => s.splitToList (· = '/')) h
      rw [hsplit₁, hsplit₂] at hsplits
      simp at hsplits
  | some pre₁ =>
    have hsplit₁ :
        (renderV4 o₁ o₂ o₃ o₄ (some pre₁)).splitToList (· = '/') =
          [addr₁, pre₁] := by
      simpa [renderV4, addr₁, String.append_assoc] using
        splitToListEq addr₁ pre₁ (fun x : Char => decide (x = '/')) '/'
          (by simp) haddr₁ (noSlashOfDigitsBetween hpre₁)
    cases pre₂ with
    | none =>
      have hsplit₂ :
          (renderV4 p₁ p₂ p₃ p₄ none).splitToList (· = '/') = [addr₂] := by
        simpa [renderV4, addr₂, String.append_assoc] using
          splitToListNoSep addr₂ (fun x : Char => decide (x = '/')) haddr₂
      have hsplits := congrArg (fun s : String => s.splitToList (· = '/')) h
      rw [hsplit₁, hsplit₂] at hsplits
      simp at hsplits
    | some pre₂ =>
      have hsplit₂ :
          (renderV4 p₁ p₂ p₃ p₄ (some pre₂)).splitToList (· = '/') =
            [addr₂, pre₂] := by
        simpa [renderV4, addr₂, String.append_assoc] using
          splitToListEq addr₂ pre₂ (fun x : Char => decide (x = '/')) '/'
            (by simp) haddr₂ (noSlashOfDigitsBetween hpre₂)
      have hsplits := congrArg (fun s : String => s.splitToList (· = '/')) h
      rw [hsplit₁, hsplit₂] at hsplits
      simp at hsplits
      have haddr : addr₁ = addr₂ := hsplits.1
      have hpre : pre₁ = pre₂ := hsplits.2
      obtain ⟨h₁, h₂, h₃, h₄⟩ :=
        digitAddr_injective ho₁ ho₂ ho₃ ho₄ hp₁ hp₂ hp₃ hp₄ haddr
      exact ⟨h₁, h₂, h₃, h₄, by simp [hpre]⟩

theorem surface_wf_of_parts {s o₁ o₂ o₃ o₄ : String} {pre : Option String}
    (hs : s = renderV4 o₁ o₂ o₃ o₄ pre)
    (h₁ : IsDigitsBetween 1 3 o₁) (h₂ : IsDigitsBetween 1 3 o₂)
    (h₃ : IsDigitsBetween 1 3 o₃) (h₄ : IsDigitsBetween 1 3 o₄)
    (hp : OptionalPrefixSyntax pre) :
    IPv4.IsWf.V4Net s := by
  have haddr :
      IPv4.IsWf.V4Addr (o₁ ++ "." ++ o₂ ++ "." ++ o₃ ++ "." ++ o₄) :=
    ⟨o₁, o₂, o₃, o₄, ⟨⟨⟨⟨rfl, h₁⟩, h₂⟩, h₃⟩, h₄⟩⟩
  cases pre with
  | none =>
    left
    rw [hs]
    simpa [renderV4] using haddr
  | some pre =>
    right
    refine ⟨o₁ ++ "." ++ o₂ ++ "." ++ o₃ ++ "." ++ o₄, pre, ?_⟩
    exact ⟨⟨by simpa [renderV4, String.append_assoc] using hs, haddr⟩, hp⟩

theorem decode_eq_of_parts {s o₁ o₂ o₃ o₄ : String} {pre : Option String}
    (hs : s = renderV4 o₁ o₂ o₃ o₄ pre)
    (h₁ : IsDigitsBetween 1 3 o₁) (h₂ : IsDigitsBetween 1 3 o₂)
    (h₃ : IsDigitsBetween 1 3 o₃) (h₄ : IsDigitsBetween 1 3 o₄)
    (hp : OptionalPrefixSyntax pre) :
    decode IPv4.grammar s = some (v4NetCaptures o₁ o₂ o₃ o₄ pre) := by
  obtain ⟨p₁, p₂, p₃, p₄, parsedPre, hdecode, hparsed, hp₁, hp₂, hp₃, hp₄,
      hparsedPre⟩ :=
    decode_parts_of_surface_wf (surface_wf_of_parts hs h₁ h₂ h₃ h₄ hp)
  have hrender :
      renderV4 p₁ p₂ p₃ p₄ parsedPre = renderV4 o₁ o₂ o₃ o₄ pre := by
    rw [← hparsed, hs]
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :=
    renderV4_injective hp₁ hp₂ hp₃ hp₄ h₁ h₂ h₃ h₄ hparsedPre hp hrender
  exact hdecode

theorem isValid_iff_parts (s : String) :
    IPv4.IsValid s ↔
      ∃ o₁ o₂ o₃ o₄ pre,
        s = renderV4 o₁ o₂ o₃ o₄ pre ∧
        OctetWf o₁ ∧ OctetWf o₂ ∧ OctetWf o₃ ∧ OctetWf o₄ ∧
        OptionalPrefixWf pre := by
  constructor
  · rintro ⟨hgrammar, hconstraints⟩
    obtain ⟨o₁, o₂, o₃, o₄, pre, hdecode, hs, h₁, h₂, h₃, h₄, hp⟩ :=
      decode_parts_of_surface_wf hgrammar
    obtain ⟨hc₁, hc₂, hc₃, hc₄, hcpre⟩ :=
      (wf_constraints_of_decode s o₁ o₂ o₃ o₄ pre hdecode).mp hconstraints
    exact ⟨o₁, o₂, o₃, o₄, pre, hs,
      ⟨h₁, hc₁⟩, ⟨h₂, hc₂⟩, ⟨h₃, hc₃⟩, ⟨h₄, hc₄⟩,
      (optionalPrefixWf_iff pre).mpr ⟨hp, hcpre⟩⟩
  · rintro ⟨o₁, o₂, o₃, o₄, pre, hs, h₁, h₂, h₃, h₄, hp⟩
    obtain ⟨hsyntaxPre, hconstraintsPre⟩ := (optionalPrefixWf_iff pre).mp hp
    have hdecode :=
      decode_eq_of_parts hs h₁.1 h₂.1 h₃.1 h₄.1 hsyntaxPre
    have hconstraints : IPv4.SatisfiesWfConstraints s :=
      (wf_constraints_of_decode s o₁ o₂ o₃ o₄ pre hdecode).mpr
        ⟨h₁.2, h₂.2, h₃.2, h₄.2, hconstraintsPre⟩
    exact
      ⟨surface_wf_of_parts hs h₁.1 h₂.1 h₃.1 h₄.1 hsyntaxPre, hconstraints⟩

/-- Accepted strings in the proof-facing component normal form. -/
theorem isValid_iff_view (s : String) :
    IPv4.IsValid s ↔ ∃ v : View, v.render = s ∧ v.Valid := by
  rw [isValid_iff_parts]
  constructor
  · rintro ⟨o₁, o₂, o₃, o₄, pre, hs, h₁, h₂, h₃, h₄, hp⟩
    exact ⟨⟨o₁, o₂, o₃, o₄, pre⟩, hs.symm, h₁, h₂, h₃, h₄, hp⟩
  · rintro ⟨⟨o₁, o₂, o₃, o₄, pre⟩, hs, h₁, h₂, h₃, h₄, hp⟩
    exact ⟨o₁, o₂, o₃, o₄, pre, hs.symm, h₁, h₂, h₃, h₄, hp⟩

theorem computeValue_eq_of_parts {s o₁ o₂ o₃ o₄ : String} {pre : Option String}
    (hs : s = renderV4 o₁ o₂ o₃ o₄ pre)
    (h₁ : OctetWf o₁) (h₂ : OctetWf o₂) (h₃ : OctetWf o₃) (h₄ : OctetWf o₄)
    (hp : OptionalPrefixWf pre) :
    IPv4.computeValue s =
      some (CedarExamples.IPv4.toIPv4Net o₁ o₂ o₃ o₄ (pre.getD "")) := by
  obtain ⟨hsyntaxPre, _⟩ := (optionalPrefixWf_iff pre).mp hp
  exact format_compute_of_decode s o₁ o₂ o₃ o₄ pre
    (decode_eq_of_parts hs h₁.1 h₂.1 h₃.1 h₄.1 hsyntaxPre)

/-- The generated value is a direct projection of any valid view rendering the input. -/
theorem computeValue_eq_of_view {s : String} (v : View)
    (hs : v.render = s) (hv : v.Valid) :
    IPv4.computeValue s = some v.denotation := by
  exact computeValue_eq_of_parts hs.symm hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2

end IPv4.GrammarView
