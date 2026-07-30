import IPv4.parser
import CedarSupport.IPAddrInternals
import CedarSupport.String
import CedarSupport.StringInternals
import Triptych.Theorems.DecodeLemmas
import Triptych.Theorems.String

/-! Axiom-clean bridges from Triptych's IPv4 predicates to Cedar's executable parser stages. -/

open Cedar.Spec.Ext
open CedarSupport.String
open CedarSupport.StringInternals
open Triptych

namespace IPv4.CedarBridge

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

theorem parseNumV4_eq_some {s : String} (hwf : IsDigitsBetween 1 3 s)
    (hcanonical : s.startsWith "0" → s = "0") (hbound : natOf s ≤ 255) :
    parseNumV4 s = some (BitVec.ofNat 8 (readNat s)) := by
  have hdigits : Triptych.IsDigits s := ⟨hwf.1, hwf.2.1⟩
  have hcedar : _root_.IsDigits s := (digits_iff s).mp hdigits
  have hread := readNat_eq s hcedar
  have hboundNat : readNat s ≤ 255 := by
    change (readNat s : Int) ≤ 255 at hbound
    omega
  unfold parseNumV4
  dsimp only
  split
  · rw [hread]
    simp [hboundNat]
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exfalso
    apply h
    exact ⟨⟨hwf.2.1, hwf.2.2⟩, hcanonical⟩

theorem parseNumV4_sound {s : String} {a : BitVec 8} (h : parseNumV4 s = some a) :
    IsDigitsBetween 1 3 s ∧
      (s.startsWith "0" → s = "0") ∧ natOf s ≤ 255 ∧
      a = BitVec.ofNat 8 (readNat s) := by
  unfold parseNumV4 at h
  dsimp only at h
  split at h
  · rename_i hguard
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hguard
    obtain ⟨⟨hlen, hmax⟩, hcanonical⟩ := hguard
    cases hnat : toNat?' s with
    | none => simp [hnat] at h
    | some n =>
      simp only [hnat] at h
      change (if n ≤ 255 then some (n : BitVec 8) else none) = some a at h
      split at h
      · rename_i hbound
        have hcedar : _root_.IsDigits s :=
          isDigitsOfToNatIsSome (by simp [hnat])
        have hdigits : Triptych.IsDigits s := (digits_iff s).mpr hcedar
        have hread := readNat_eq s hcedar
        rw [hnat] at hread
        have hn : n = readNat s := Option.some.inj hread
        subst n
        have hboundInt : natOf s ≤ 255 := by
          change (readNat s : Int) ≤ 255
          omega
        exact ⟨⟨hdigits.1, hlen, hmax⟩, hcanonical, hboundInt,
          (Option.some.inj h).symm⟩
      · simp at h
  · simp at h

theorem parseNumV4_iff {s : String} {a : BitVec 8} :
    parseNumV4 s = some a ↔ OctetWf s ∧ a = BitVec.ofNat 8 (readNat s) := by
  constructor
  · intro h
    obtain ⟨hwf, hcanonical, hbound, ha⟩ := parseNumV4_sound h
    exact ⟨⟨hwf, hcanonical, hbound⟩, ha⟩
  · rintro ⟨⟨hwf, hcanonical, hbound⟩, rfl⟩
    exact parseNumV4_eq_some hwf hcanonical hbound

theorem parsePrefixNat_eq_some {s : String} {digits size : Nat}
    (hwf : PrefixWf digits size s) :
    parsePrefixNat s digits size = some (Fin.ofNat (size + 1) (readNat s)) := by
  have hdigits : Triptych.IsDigits s := ⟨hwf.1.1, hwf.1.2.1⟩
  have hcedar : _root_.IsDigits s := (digits_iff s).mp hdigits
  have hread := readNat_eq s hcedar
  have hboundNat : readNat s ≤ size := by
    have hbound := hwf.2.2
    change (readNat s : Int) ≤ size at hbound
    omega
  unfold parsePrefixNat
  dsimp only
  split
  · rw [hread]
    simp [hboundNat]
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exfalso
    apply h
    exact ⟨⟨hwf.1.2.1, hwf.1.2.2⟩, hwf.2.1⟩

theorem parsePrefixNat_sound {s : String} {digits size : Nat} {pre : Fin (size + 1)}
    (h : parsePrefixNat s digits size = some pre) :
    PrefixWf digits size s ∧ pre = Fin.ofNat (size + 1) (readNat s) := by
  unfold parsePrefixNat at h
  dsimp only at h
  split at h
  · rename_i hguard
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hguard
    obtain ⟨⟨hlen, hmax⟩, hcanonical⟩ := hguard
    cases hnat : toNat?' s with
    | none => simp [hnat] at h
    | some n =>
      simp only [hnat] at h
      change (if n ≤ size then some (Fin.ofNat (size + 1) n) else none) = some pre at h
      split at h
      · rename_i hbound
        have hcedar : _root_.IsDigits s :=
          isDigitsOfToNatIsSome (by simp [hnat])
        have hdigits : Triptych.IsDigits s := (digits_iff s).mpr hcedar
        have hread := readNat_eq s hcedar
        rw [hnat] at hread
        have hn : n = readNat s := Option.some.inj hread
        subst n
        have hboundInt : natOf s ≤ size := by
          change (readNat s : Int) ≤ size
          omega
        exact ⟨⟨⟨hdigits.1, hlen, hmax⟩, hcanonical, hboundInt⟩,
          (Option.some.inj h).symm⟩
      · simp at h
  · simp at h

private theorem noDotOfOctetWf {s : String} (h : OctetWf s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = '.')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq
  subst c
  have hdigit := h.1.1 '.' hc
  simp [TokClass.mem] at hdigit

theorem parseSegsV4_eq_some {o₁ o₂ o₃ o₄ : String}
    (h₁ : OctetWf o₁) (h₂ : OctetWf o₂) (h₃ : OctetWf o₃) (h₄ : OctetWf o₄) :
    parseSegsV4 (o₁ ++ "." ++ o₂ ++ "." ++ o₃ ++ "." ++ o₄) =
      some (Cedar.Spec.Ext.IPAddr.IPv4Addr.mk
        (BitVec.ofNat 8 (readNat o₁)) (BitVec.ofNat 8 (readNat o₂))
        (BitVec.ofNat 8 (readNat o₃)) (BitVec.ofNat 8 (readNat o₄))) := by
  have hsplit :
      (o₁ ++ "." ++ o₂ ++ "." ++ o₃ ++ "." ++ o₄).splitToList (· = '.') =
        [o₁, o₂, o₃, o₄] := by
    simpa [String.append_assoc] using
      (splitToListEq4 o₁ o₂ o₃ o₄ (fun x : Char => decide (x = '.')) '.'
        (by simp) (noDotOfOctetWf h₁) (noDotOfOctetWf h₂)
        (noDotOfOctetWf h₃) (noDotOfOctetWf h₄))
  unfold parseSegsV4
  rw [hsplit]
  simp only [parseNumV4_eq_some h₁.1 h₁.2.1 h₁.2.2,
    parseNumV4_eq_some h₂.1 h₂.2.1 h₂.2.2,
    parseNumV4_eq_some h₃.1 h₃.2.1 h₃.2.2,
    parseNumV4_eq_some h₄.1 h₄.2.1 h₄.2.2]
  rfl

private theorem joinDotSplit4 {s o₁ o₂ o₃ o₄ : String}
    (h : s.splitToList (· = '.') = [o₁, o₂, o₃, o₄]) :
    s = o₁ ++ "." ++ o₂ ++ "." ++ o₃ ++ "." ++ o₄ := by
  rw [String.splitToList_of_valid] at h
  have hp : (fun x : Char => decide (x = '.')) = (fun x => x == '.') := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, beq_iff_eq]
  have hsplits : List.splitOn '.' s.toList = [o₁.toList, o₂.toList, o₃.toList, o₄.toList] := by
    rw [List.splitOn_eq_splitOnP]
    have h' := congrArg (List.map String.toList) h
    simpa [Function.comp_def, hp] using h'
  have hi := congrArg (List.intercalate ['.']) hsplits
  rw [List.intercalate_splitOn] at hi
  rw [← String.toList_inj]
  simpa [List.intercalate, String.toList_append, List.append_assoc] using hi

private theorem joinSlashSplit1 {s addr : String}
    (h : s.splitToList (· = '/') = [addr]) :
    s = addr := by
  rw [String.splitToList_of_valid] at h
  have hp : (fun x : Char => decide (x = '/')) = (fun x => x == '/') := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, beq_iff_eq]
  have hsplits : List.splitOn '/' s.toList = [addr.toList] := by
    rw [List.splitOn_eq_splitOnP]
    have h' := congrArg (List.map String.toList) h
    simpa [Function.comp_def, hp] using h'
  have hi := congrArg (List.intercalate ['/']) hsplits
  rw [List.intercalate_splitOn] at hi
  rw [← String.toList_inj]
  simpa using hi

private theorem joinSlashSplit2 {s addr pre : String}
    (h : s.splitToList (· = '/') = [addr, pre]) :
    s = addr ++ "/" ++ pre := by
  rw [String.splitToList_of_valid] at h
  have hp : (fun x : Char => decide (x = '/')) = (fun x => x == '/') := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, beq_iff_eq]
  have hsplits : List.splitOn '/' s.toList = [addr.toList, pre.toList] := by
    rw [List.splitOn_eq_splitOnP]
    have h' := congrArg (List.map String.toList) h
    simpa [Function.comp_def, hp] using h'
  have hi := congrArg (List.intercalate ['/']) hsplits
  rw [List.intercalate_splitOn] at hi
  rw [← String.toList_inj]
  simpa [List.intercalate, String.toList_append, List.append_assoc] using hi

theorem parseSegsV4_sound {s : String} {addr : Cedar.Spec.Ext.IPAddr.IPv4Addr}
    (h : parseSegsV4 s = some addr) :
    ∃ o₁ o₂ o₃ o₄,
      s = o₁ ++ "." ++ o₂ ++ "." ++ o₃ ++ "." ++ o₄ ∧
      OctetWf o₁ ∧ OctetWf o₂ ∧ OctetWf o₃ ∧ OctetWf o₄ ∧
      addr = Cedar.Spec.Ext.IPAddr.IPv4Addr.mk
        (BitVec.ofNat 8 (readNat o₁)) (BitVec.ofNat 8 (readNat o₂))
        (BitVec.ofNat 8 (readNat o₃)) (BitVec.ofNat 8 (readNat o₄)) := by
  unfold parseSegsV4 at h
  generalize hsplits : s.splitToList (· = '.') = parts at h
  rcases parts with _ | ⟨o₁, parts⟩
  · simp at h
  rcases parts with _ | ⟨o₂, parts⟩
  · simp at h
  rcases parts with _ | ⟨o₃, parts⟩
  · simp at h
  rcases parts with _ | ⟨o₄, parts⟩
  · simp at h
  rcases parts with _ | ⟨extra, parts⟩
  · cases h₁ : parseNumV4 o₁ with
    | none => simp [h₁] at h
    | some a₁ =>
      cases h₂ : parseNumV4 o₂ with
      | none => simp [h₁, h₂] at h
      | some a₂ =>
        cases h₃ : parseNumV4 o₃ with
        | none => simp [h₁, h₂, h₃] at h
        | some a₃ =>
          cases h₄ : parseNumV4 o₄ with
          | none => simp [h₁, h₂, h₃, h₄] at h
          | some a₄ =>
            obtain ⟨hwf₁, ha₁⟩ := parseNumV4_iff.mp h₁
            obtain ⟨hwf₂, ha₂⟩ := parseNumV4_iff.mp h₂
            obtain ⟨hwf₃, ha₃⟩ := parseNumV4_iff.mp h₃
            obtain ⟨hwf₄, ha₄⟩ := parseNumV4_iff.mp h₄
            have hs := joinDotSplit4 hsplits
            simp [h₁, h₂, h₃, h₄] at h
            subst addr
            subst a₁
            subst a₂
            subst a₃
            subst a₄
            exact ⟨o₁, o₂, o₃, o₄, hs, hwf₁, hwf₂, hwf₃, hwf₄, rfl⟩
  · simp at h

private theorem noSlashOfOctetWf {s : String} (h : OctetWf s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = '/')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq
  subst c
  have hdigit := h.1.1 '/' hc
  simp [TokClass.mem] at hdigit

private theorem noSlashAppend {s₁ s₂ : String}
    (h₁ : ∀ c ∈ s₁.toList, (fun x : Char => decide (x = '/')) c = false)
    (h₂ : ∀ c ∈ s₂.toList, (fun x : Char => decide (x = '/')) c = false) :
    ∀ c ∈ (s₁ ++ s₂).toList, (fun x : Char => decide (x = '/')) c = false := by
  intro c hc
  rw [String.toList_append] at hc
  rcases List.mem_append.mp hc with h | h
  · exact h₁ c h
  · exact h₂ c h

private theorem noSlashDot :
    ∀ c ∈ ".".toList, (fun x : Char => decide (x = '/')) c = false := by
  simp

private theorem noSlashOfV4Addr {o₁ o₂ o₃ o₄ : String}
    (h₁ : OctetWf o₁) (h₂ : OctetWf o₂) (h₃ : OctetWf o₃) (h₄ : OctetWf o₄) :
    ∀ c ∈ (o₁ ++ "." ++ o₂ ++ "." ++ o₃ ++ "." ++ o₄).toList,
      (fun x : Char => decide (x = '/')) c = false := by
  simpa [String.append_assoc] using
    noSlashAppend (noSlashOfOctetWf h₁)
      (noSlashAppend noSlashDot
        (noSlashAppend (noSlashOfOctetWf h₂)
          (noSlashAppend noSlashDot
            (noSlashAppend (noSlashOfOctetWf h₃)
              (noSlashAppend noSlashDot (noSlashOfOctetWf h₄))))))

private theorem noSlashOfPrefixWf {s : String} (h : PrefixWf 2 32 s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = '/')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq
  subst c
  have hdigit := h.1.1 '/' hc
  simp [TokClass.mem] at hdigit

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
  · rintro ⟨⟨hgrammar, hconstraints⟩, _⟩
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
    exact ⟨⟨surface_wf_of_parts hs h₁.1 h₂.1 h₃.1 h₄.1 hsyntaxPre,
      hconstraints⟩, trivial⟩

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

theorem parseIPv4Net_eq_some {o₁ o₂ o₃ o₄ : String} {pre : Option String}
    (h₁ : OctetWf o₁) (h₂ : OctetWf o₂) (h₃ : OctetWf o₃) (h₄ : OctetWf o₄)
    (hp : OptionalPrefixWf pre) :
    parseIPv4Net (renderV4 o₁ o₂ o₃ o₄ pre) =
      some (CedarExamples.IPv4.toIPNet o₁ o₂ o₃ o₄ (pre.getD "")) := by
  let addr := o₁ ++ "." ++ o₂ ++ "." ++ o₃ ++ "." ++ o₄
  have haddr : ∀ c ∈ addr.toList, (fun x : Char => decide (x = '/')) c = false := by
    exact noSlashOfV4Addr h₁ h₂ h₃ h₄
  cases pre with
  | none =>
    have hsplit : (renderV4 o₁ o₂ o₃ o₄ none).splitToList (· = '/') = [addr] := by
      simpa [renderV4, addr, String.append_assoc] using
        splitToListNoSep addr (fun x : Char => decide (x = '/')) haddr
    unfold parseIPv4Net
    rw [hsplit]
    simp only
    rw [parseSegsV4_eq_some h₁ h₂ h₃ h₄]
    rfl
  | some pre =>
    have hsplit :
        (renderV4 o₁ o₂ o₃ o₄ (some pre)).splitToList (· = '/') =
          [addr, pre] := by
      simpa [renderV4, addr, String.append_assoc] using
        splitToListEq addr pre (fun x : Char => decide (x = '/')) '/'
          (by simp) haddr (noSlashOfPrefixWf hp)
    unfold parseIPv4Net
    rw [hsplit]
    simp only
    rw [show Cedar.Spec.Ext.IPAddr.ADDR_SIZE Cedar.Spec.Ext.IPAddr.V4_WIDTH = 32 by rfl]
    rw [parsePrefixNat_eq_some hp]
    rw [parseSegsV4_eq_some h₁ h₂ h₃ h₄]
    unfold CedarExamples.IPv4.toIPNet CedarExamples.IPv4.toIPv4Net
    have hbound : readNat pre < 33 := by
      have h := hp.2.2
      change (readNat pre : Int) ≤ 32 at h
      omega
    have hne : pre ≠ "" := by
      intro heq
      subst pre
      have hlen := hp.1.2.1
      simp at hlen
    simp [hne, Fin.val_ofNat, Nat.mod_eq_of_lt hbound]

theorem parseIPv4Net_sound {s : String} {net : Cedar.Spec.Ext.IPAddr.IPNet}
    (h : parseIPv4Net s = some net) :
    ∃ o₁ o₂ o₃ o₄ pre,
      s = renderV4 o₁ o₂ o₃ o₄ pre ∧
      OctetWf o₁ ∧ OctetWf o₂ ∧ OctetWf o₃ ∧ OctetWf o₄ ∧
      OptionalPrefixWf pre ∧
      net = CedarExamples.IPv4.toIPNet o₁ o₂ o₃ o₄ (pre.getD "") := by
  have hparse := h
  unfold parseIPv4Net at h
  generalize hsplits : s.splitToList (· = '/') = parts at h
  rcases parts with _ | ⟨addr, rest⟩
  · simp at h
  rcases rest with _ | ⟨pre, rest⟩
  · cases haddr : parseSegsV4 addr with
    | none => simp [haddr] at h
    | some parsedAddr =>
      obtain ⟨o₁, o₂, o₃, o₄, hrender, hwf₁, hwf₂, hwf₃, hwf₄, _⟩ :=
        parseSegsV4_sound haddr
      have hs : s = renderV4 o₁ o₂ o₃ o₄ none := by
        rw [joinSlashSplit1 hsplits, hrender]
        simp [renderV4]
      have hvalue := parseIPv4Net_eq_some hwf₁ hwf₂ hwf₃ hwf₄ (pre := none) trivial
      rw [← hs, hparse] at hvalue
      exact ⟨o₁, o₂, o₃, o₄, none, hs, hwf₁, hwf₂, hwf₃, hwf₄, trivial,
        Option.some.inj hvalue⟩
  rcases rest with _ | ⟨extra, rest⟩
  · cases hpre : parsePrefixNat pre 2 32 with
    | none =>
      rw [show Cedar.Spec.Ext.IPAddr.ADDR_SIZE Cedar.Spec.Ext.IPAddr.V4_WIDTH = 32 by rfl] at h
      simp [hpre] at h
    | some parsedPre =>
      rw [show Cedar.Spec.Ext.IPAddr.ADDR_SIZE Cedar.Spec.Ext.IPAddr.V4_WIDTH = 32 by rfl] at h
      cases haddr : parseSegsV4 addr with
      | none => simp [hpre, haddr] at h
      | some parsedAddr =>
        obtain ⟨hp, _⟩ := parsePrefixNat_sound hpre
        obtain ⟨o₁, o₂, o₃, o₄, hrender, hwf₁, hwf₂, hwf₃, hwf₄, _⟩ :=
          parseSegsV4_sound haddr
        have hs : s = renderV4 o₁ o₂ o₃ o₄ (some pre) := by
          rw [joinSlashSplit2 hsplits, hrender]
          simp [renderV4, String.append_assoc]
        have hvalue :=
          parseIPv4Net_eq_some hwf₁ hwf₂ hwf₃ hwf₄ (pre := some pre) hp
        rw [← hs, hparse] at hvalue
        exact ⟨o₁, o₂, o₃, o₄, some pre, hs, hwf₁, hwf₂, hwf₃, hwf₄, hp,
          Option.some.inj hvalue⟩
  · simp at h

theorem parseIPv4Net_filter_isV4 (s : String) :
    (parseIPv4Net s).filter (·.isV4) = parseIPv4Net s := by
  unfold parseIPv4Net
  generalize hsplits : s.splitToList (· = '/') = parts
  rcases parts with _ | ⟨addr, rest⟩
  · rfl
  rcases rest with _ | ⟨pre, rest⟩
  · cases haddr : parseSegsV4 addr <;>
      simp [haddr, Cedar.Spec.Ext.IPAddr.IPNet.isV4]
  rcases rest with _ | ⟨extra, rest⟩
  · cases hpre : parsePrefixNat pre 2
        (Cedar.Spec.Ext.IPAddr.ADDR_SIZE Cedar.Spec.Ext.IPAddr.V4_WIDTH) <;>
      simp [hpre]
    rename_i parsedPre
    cases haddr : parseSegsV4 addr <;>
      simp [Cedar.Spec.Ext.IPAddr.IPNet.isV4]
  · rfl

theorem parseIPv6Net_filter_isV4 (s : String) :
    (parseIPv6Net s).filter (·.isV4) = none := by
  unfold parseIPv6Net
  generalize hsplits : s.splitToList (· = '/') = parts
  rcases parts with _ | ⟨addr, rest⟩
  · rfl
  rcases rest with _ | ⟨pre, rest⟩
  · cases haddr : parseSegsV6 addr <;>
      simp [haddr, Cedar.Spec.Ext.IPAddr.IPNet.isV4]
  rcases rest with _ | ⟨extra, rest⟩
  · cases hpre : parsePrefixNat pre 3
        (Cedar.Spec.Ext.IPAddr.ADDR_SIZE Cedar.Spec.Ext.IPAddr.V6_WIDTH) <;>
      simp [hpre]
    rename_i parsedPre
    cases haddr : parseSegsV6 addr <;>
      simp [Cedar.Spec.Ext.IPAddr.IPNet.isV4]
  · rfl

private def v4Payload : Cedar.Spec.Ext.IPAddr.IPNet → CedarExamples.IPv4.IPv4Net
  | .V4 cidr => cidr
  | .V6 _ => ⟨0, none⟩

theorem ipv4Only_eq_parseIPv4Net (s : String) :
    CedarExamples.IPv4.ipv4Only s = (parseIPv4Net s).map v4Payload := by
  unfold CedarExamples.IPv4.ipv4Only
  rw [ip_eq_parse]
  unfold CedarSupport.IPAddrInternals.parse
  cases h : parseIPv4Net s with
  | none =>
    simp only [Option.isSome_none, if_false, Option.map_none]
    cases h6 : parseIPv6Net s with
    | none => rfl
    | some net =>
      cases net with
      | V4 cidr =>
        have hfilter := parseIPv6Net_filter_isV4 s
        rw [h6] at hfilter
        simp [Cedar.Spec.Ext.IPAddr.IPNet.isV4] at hfilter
      | V6 cidr => rfl
  | some net =>
    cases net with
    | V4 cidr =>
      simp [v4Payload]
    | V6 cidr =>
      have hfilter := parseIPv4Net_filter_isV4 s
      rw [h] at hfilter
      simp [Cedar.Spec.Ext.IPAddr.IPNet.isV4] at hfilter

theorem parser_agrees (s : String) (net : CedarExamples.IPv4.IPv4Net) :
    CedarExamples.IPv4.ipv4Only s = some net ↔
      IPv4.IsValid s ∧ IPv4.computeValue s = some net := by
  rw [ipv4Only_eq_parseIPv4Net]
  constructor
  · intro hparse
    cases htagged : parseIPv4Net s with
    | none => simp [htagged] at hparse
    | some tagged =>
      cases tagged with
      | V4 cidr =>
        simp [htagged, v4Payload] at hparse
        subst net
        obtain ⟨o₁, o₂, o₃, o₄, pre, hs, h₁, h₂, h₃, h₄, hp, hnet⟩ :=
          parseIPv4Net_sound htagged
        simp only [CedarExamples.IPv4.toIPNet] at hnet
        injection hnet with hcidr
        subst cidr
        let v : View := ⟨o₁, o₂, o₃, o₄, pre⟩
        have hrender : v.render = s := by simpa [v, View.render] using hs.symm
        have hvalid : v.Valid := ⟨h₁, h₂, h₃, h₄, hp⟩
        exact ⟨(isValid_iff_view s).mpr ⟨v, hrender, hvalid⟩,
          computeValue_eq_of_view v hrender hvalid⟩
      | V6 cidr =>
        have hfilter := parseIPv4Net_filter_isV4 s
        rw [htagged] at hfilter
        simp [Cedar.Spec.Ext.IPAddr.IPNet.isV4] at hfilter
  · rintro ⟨hvalid, hvalue⟩
    obtain ⟨v, hs, hv⟩ := (isValid_iff_view s).mp hvalid
    have hformat := computeValue_eq_of_view v hs hv
    rw [hvalue] at hformat
    have hnet : net = v.denotation := Option.some.inj hformat
    subst net
    rw [← hs]
    unfold View.render
    rw [parseIPv4Net_eq_some hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2]
    simp [View.denotation, v4Payload, CedarExamples.IPv4.toIPNet]

theorem parser_rejects_iff (s : String) :
    CedarExamples.IPv4.ipv4Only s = none ↔ ¬IPv4.IsValid s := by
  constructor
  · intro hnone hvalid
    obtain ⟨o₁, o₂, o₃, o₄, pre, hs, h₁, h₂, h₃, h₄, hp⟩ :=
      (isValid_iff_parts s).mp hvalid
    have hvalue := computeValue_eq_of_parts hs h₁ h₂ h₃ h₄ hp
    have hsome := (parser_agrees s _).mpr ⟨hvalid, hvalue⟩
    rw [hnone] at hsome
    simp at hsome
  · intro hinvalid
    cases hparse : CedarExamples.IPv4.ipv4Only s with
    | none => rfl
    | some net =>
      exact (hinvalid ((parser_agrees s net).mp hparse).1).elim

end IPv4.CedarBridge
