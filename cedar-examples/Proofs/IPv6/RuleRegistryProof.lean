import Outputs.IPv6.parser
import CedarSupport.IPAddrInternals
import CedarSupport.ParserRules
import CedarSupport.StringInternals
import Triptych.Automation.ExternalParser

/-!
# IPv6 external-parser proof via the Triptych rule registry

This module derives successful-path summaries directly from Cedar's executable IP parser.
The summaries are independent of Cedar's unfinished `Cedar.Thm.Ext.IPAddr` theorem layer.
-/

open Cedar.Spec.Ext
open Cedar.Spec.Ext.IPAddr
open CedarSupport.IPAddrInternals
open CedarSupport.ParserRules
open CedarSupport.StringInternals
open Triptych

namespace IPv6.RuleRegistryProof

/-- Parser-independent syntax of one IPv6 hextet. -/
def HexValid (s : String) : Prop :=
  IsHexDigitsBetween 1 4 s

private theorem isDigit_eq_true_iff (c : Char) :
    c.isDigit = true ↔ '0' ≤ c ∧ c ≤ '9' := by
  rw [Char.isDigit_iff_toNat]
  simp only [Char.le_def, UInt32.le_iff_toNat_le, Char.toNat]

private theorem isHexDigit_eq_true_iff (c : Char) :
    isHexDigit c = true ↔ TokClass.hexDigit.mem c := by
  simp only [isHexDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rw [isDigit_eq_true_iff]
  simp only [TokClass.mem]
  constructor
  · rintro ((hd | hl) | hu)
    · exact Or.inl hd
    · exact Or.inr (Or.inl hl)
    · exact Or.inr (Or.inr hu)
  · rintro (hd | hl | hu)
    · exact Or.inl (Or.inl hd)
    · exact Or.inl (Or.inr hl)
    · exact Or.inr hu

private theorem all_isHexDigit_iff (s : String) :
    s.all isHexDigit = true ↔ TokClass.hexDigit.all s := by
  rw [String.all_bool_eq]
  simp only [List.all_eq_true]
  unfold TokClass.all
  constructor
  · intro h c hc
    exact (isHexDigit_eq_true_iff c).mp (h c hc)
  · intro h c hc
    exact (isHexDigit_eq_true_iff c).mpr (h c hc)

private def hexDigitNat (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

private theorem toHexNat_eq_hexDigitNat {c : Char}
    (h : TokClass.hexDigit.mem c) :
    toHexNat c = hexDigitNat c := by
  unfold toHexNat hexDigitNat
  split <;> rename_i hd
  · rfl
  split <;> rename_i hl
  · rfl
  split <;> rename_i hu
  · rfl
  change
    ('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'f') ∨
      ('A' ≤ c ∧ c ≤ 'F') at h
  have hnotDigit : ¬('0' ≤ c ∧ c ≤ '9') := by
    intro hbounds
    exact hd ((isDigit_eq_true_iff c).mpr hbounds)
  have hnotLower : ¬('a' ≤ c ∧ c ≤ 'f') := by
    intro hbounds
    exact hl (by simp [hbounds])
  have hnotUpper : ¬('A' ≤ c ∧ c ≤ 'F') := by
    intro hbounds
    exact hu (by simp [hbounds])
  rcases h with h | h | h
  · exact (hnotDigit h).elim
  · exact (hnotLower h).elim
  · exact (hnotUpper h).elim

private theorem hexDigitNat_le {c : Char}
    (_h : TokClass.hexDigit.mem c) :
    hexDigitNat c ≤ 15 := by
  unfold hexDigitNat
  split <;> rename_i hd
  · have hb := Char.isDigit_iff_toNat.mp hd
    have hs := Nat.sub_le_sub_right hb.2 '0'.toNat
    have hc : '9'.toNat - '0'.toNat = 9 := by decide
    omega
  split <;> rename_i hl
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
    have hhi : c.toNat ≤ 'f'.toNat := by
      simpa only [Char.le_def, UInt32.le_iff_toNat_le, Char.toNat] using hl.2
    have hs := Nat.sub_le_sub_right hhi 'a'.toNat
    have hc : 'f'.toNat - 'a'.toNat = 5 := by decide
    omega
  split <;> rename_i hu
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hu
    have hhi : c.toNat ≤ 'F'.toNat := by
      simpa only [Char.le_def, UInt32.le_iff_toNat_le, Char.toNat] using hu.2
    have hs := Nat.sub_le_sub_right hhi 'A'.toNat
    have hc : 'F'.toNat - 'A'.toNat = 5 := by decide
    omega
  · simp

private theorem foldHex_eq (l : List Char)
    (h : ∀ c ∈ l, TokClass.hexDigit.mem c) (acc : Nat) :
    l.foldl (fun n c => n * 16 + toHexNat c) acc =
      l.foldl (fun n c => n * 16 + hexDigitNat c) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.foldl_cons]
      rw [toHexNat_eq_hexDigitNat (h c (by simp))]
      apply ih
      intro x hx
      exact h x (by simp [hx])

private theorem foldHex_lt (l : List Char) (acc : Nat)
    (h : ∀ c ∈ l, TokClass.hexDigit.mem c) :
    l.foldl (fun n c => n * 16 + hexDigitNat c) acc <
      (acc + 1) * 16 ^ l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons c cs ih =>
      simp only [List.foldl_cons, List.length_cons, Nat.pow_succ]
      have hdigit : hexDigitNat c ≤ 15 := hexDigitNat_le (h c (by simp))
      have hacc : acc * 16 + hexDigitNat c + 1 ≤ (acc + 1) * 16 := by omega
      have htail := ih (acc * 16 + hexDigitNat c) (by
        intro x hx
        exact h x (by simp [hx]))
      apply Nat.lt_of_lt_of_le htail
      apply Nat.le_trans (Nat.mul_le_mul_right _ hacc)
      simp only [Nat.mul_assoc, Nat.mul_comm]
      exact Nat.le_refl _

private theorem parserFold_eq_readHex {s : String} (h : HexValid s) :
    s.foldl (fun n c => n * 16 + toHexNat c) 0 =
      CedarExamples.IPv6.readHex s := by
  unfold CedarExamples.IPv6.readHex
  rw [String.foldl_eq_foldl_toList, String.foldl_eq_foldl_toList]
  exact foldHex_eq s.toList h.1 0

private theorem readHex_le {s : String} (h : HexValid s) :
    CedarExamples.IPv6.readHex s ≤ 0xffff := by
  unfold CedarExamples.IPv6.readHex
  rw [String.foldl_eq_foldl_toList]
  change s.toList.foldl (fun n c => n * 16 + hexDigitNat c) 0 ≤ 0xffff
  have hlt := foldHex_lt s.toList 0 h.1
  simp only [Nat.zero_add, Nat.one_mul, String.length_toList] at hlt
  have hpow : 16 ^ s.length ≤ 16 ^ 4 :=
    Nat.pow_le_pow_right (by omega) h.2.2
  omega

/-- Cedar's hextet parser accepts exactly 1-4 hex digits and returns their value. -/
@[triptych_parser, triptych_parser_search =]
theorem parseNumV6_eq_some_iff {s : String} {a : BitVec 16} :
    parseNumV6 s = some a ↔
      HexValid s ∧ a = BitVec.ofNat 16 (CedarExamples.IPv6.readHex s) := by
  constructor
  · intro h
    triptych_sound [parseNumV6] at h
    obtain ⟨hpos, hmax, hall, _hbound, hvalue⟩ := h
    have hvalid : HexValid s :=
      ⟨(all_isHexDigit_iff s).mp hall, hpos, hmax⟩
    refine ⟨hvalid, ?_⟩
    rw [← parserFold_eq_readHex hvalid]
    simpa using hvalue.symm
  · rintro ⟨hvalid, rfl⟩
    unfold parseNumV6
    have hsyntax :
        (0 < s.length && s.length ≤ 4 && s.all isHexDigit) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hvalid.2.1, hvalid.2.2⟩, (all_isHexDigit_iff s).mpr hvalid.1⟩
    rw [if_pos hsyntax]
    have hfold := parserFold_eq_readHex hvalid
    have hbound :
        s.foldl (fun n c => n * 16 + toHexNat c) 0 ≤ 0xffff := by
      rw [hfold]
      exact readHex_le hvalid
    rw [if_pos hbound, hfold]
    rfl

/-- Concrete rendering of a list of IPv6 hextets. -/
def renderGroups (parts : List String) : String :=
  String.intercalate ":" parts

/-- Pointwise numeric denotation of IPv6 hextets. -/
def groupValues (parts : List String) : List (BitVec 16) :=
  parts.map (fun part => BitVec.ofNat 16 (CedarExamples.IPv6.readHex part))

private theorem renderGroups_cons_toList (part : String) (parts : List String) :
    (renderGroups (part :: parts)).toList =
      part.toList ++
        match parts with
        | [] => []
        | _ => ':' :: (renderGroups parts).toList := by
  cases parts <;> simp [renderGroups, String.toList_append]

private theorem noColonOfHexValid {s : String} (h : HexValid s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = ':')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq
  subst c
  have hm := h.1 ':' hc
  simp [TokClass.mem] at hm

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
                (renderGroups (next :: tail)).toList ++ suffix = ':' :: rest → False := by
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

private theorem mapM_parseNumV6_eq_some_iff
    {parts : List String} {values : List (BitVec 16)} :
    parts.mapM parseNumV6 = some values ↔
      (∀ part ∈ parts, HexValid part) ∧ values = groupValues parts := by
  rw [Triptych.Automation.list_mapM_option_eq_some_iff]
  constructor
  · intro h
    induction h with
    | nil =>
        exact ⟨by simp, rfl⟩
    | cons hhead _ ih =>
        have hv := parseNumV6_eq_some_iff.mp hhead
        refine ⟨?_, ?_⟩
        · intro item hitem
          simp only [List.mem_cons] at hitem
          rcases hitem with rfl | hitem
          · exact hv.1
          · exact ih.1 item hitem
        · simp [groupValues, hv.2, ih.2]
  · rintro ⟨hall, rfl⟩
    induction parts with
    | nil =>
        exact .nil
    | cons part parts ih =>
        apply List.Forall₂.cons
        · apply parseNumV6_eq_some_iff.mpr
          exact ⟨hall part (by simp), rfl⟩
        · apply ih
          intro item hitem
          exact hall item (by simp [hitem])

/-- Cedar's hextet-list parser implements delimiter-separated valid groups, including the
    empty list used on either side of `::`. -/
@[triptych_parser, triptych_parser_search =]
theorem parseNumSegsV6_eq_some_iff {s : String} {values : List (BitVec 16)} :
    parseNumSegsV6 s = some values ↔
      ∃ parts,
        s = renderGroups parts ∧
        (∀ part ∈ parts, HexValid part) ∧
        values = groupValues parts := by
  constructor
  · intro h
    unfold parseNumSegsV6 at h
    split at h <;> rename_i hempty
    · have hs : s = "" := String.isEmpty_iff.mp hempty
      simp only [Option.some.injEq] at h
      subst s
      subst values
      exact ⟨[], by simp [renderGroups], by simp, rfl⟩
    · generalize hparts : s.splitToList (· = ':') = parts at h
      obtain ⟨hall, hvalues⟩ := mapM_parseNumV6_eq_some_iff.mp h
      refine ⟨parts, ?_, hall, hvalues⟩
      simpa [renderGroups] using
        (Triptych.eq_intercalate_of_splitToList_eq ':' hparts)
  · rintro ⟨parts, rfl, hall, rfl⟩
    cases parts with
    | nil =>
        simp [parseNumSegsV6, renderGroups, groupValues]
    | cons part parts =>
        have hsplit :
            (renderGroups (part :: parts)).splitToList (· = ':') =
              part :: parts := by
          simpa [renderGroups] using
            (Triptych.splitToList_intercalate (part :: parts) (by simp)
              (fun x : Char => decide (x = ':')) ':' (by simp) (by
                intro item hitem c hc
                exact noColonOfHexValid (hall item hitem) c hc))
        have hpartNonempty : part ≠ "" := by
          intro heq
          have hlen := (hall part (by simp)).2.1
          simp [heq] at hlen
        have hnonempty : renderGroups (part :: parts) ≠ "" := by
          cases parts <;> simp [renderGroups, hpartNonempty]
        unfold parseNumSegsV6
        rw [if_neg (by simpa [String.isEmpty_iff] using hnonempty), hsplit]
        exact mapM_parseNumV6_eq_some_iff.mpr ⟨hall, rfl⟩

/-- Proof-facing syntax selected by Cedar's IPv6 compression parser. -/
inductive AddrComponents where
  | full (parts : List String)
  | compressed (left right : List String)

namespace AddrComponents

def render : AddrComponents → String
  | .full parts => renderGroups parts
  | .compressed left right => renderGroups left ++ "::" ++ renderGroups right

def Valid : AddrComponents → Prop
  | .full parts =>
      parts.length = 8 ∧ ∀ part ∈ parts, HexValid part
  | .compressed left right =>
      left.length + right.length < 8 ∧
        (∀ part ∈ left, HexValid part) ∧
        ∀ part ∈ right, HexValid part

def values : AddrComponents → List (BitVec 16)
  | .full parts => groupValues parts
  | .compressed left right =>
      groupValues left ++
        List.replicate (8 - (left.length + right.length)) 0 ++
        groupValues right

def addrOfValues (groups : List (BitVec 16)) : IPv6Addr :=
  IPv6Addr.mk
    (groups.getD 0 0) (groups.getD 1 0) (groups.getD 2 0) (groups.getD 3 0)
    (groups.getD 4 0) (groups.getD 5 0) (groups.getD 6 0) (groups.getD 7 0)

def denotation (c : AddrComponents) : IPv6Addr :=
  addrOfValues c.values

theorem denotation_full (parts : List String) :
    denotation (.full parts) = addrOfValues (groupValues parts) :=
  rfl

theorem denotation_compressed (left right : List String) :
    denotation (.compressed left right) =
      addrOfValues
        (groupValues left ++
          List.replicate (8 - (left.length + right.length)) 0 ++
          groupValues right) :=
  rfl

end AddrComponents

private def finishV6 (groups : List (BitVec 16)) : Option IPv6Addr :=
  match groups with
  | [a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇] =>
      some (IPv6Addr.mk a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇)
  | _ => none

private theorem finishV6_eq_some_iff {groups : List (BitVec 16)} {addr : IPv6Addr} :
    finishV6 groups = some addr ↔
      groups.length = 8 ∧ addr = AddrComponents.addrOfValues groups := by
  unfold finishV6
  rcases groups with _ | ⟨a₀, groups⟩
  · simp
  rcases groups with _ | ⟨a₁, groups⟩
  · simp
  rcases groups with _ | ⟨a₂, groups⟩
  · simp
  rcases groups with _ | ⟨a₃, groups⟩
  · simp
  rcases groups with _ | ⟨a₄, groups⟩
  · simp
  rcases groups with _ | ⟨a₅, groups⟩
  · simp
  rcases groups with _ | ⟨a₆, groups⟩
  · simp
  rcases groups with _ | ⟨a₇, groups⟩
  · simp
  rcases groups with _ | ⟨extra, groups⟩
  · simp [AddrComponents.addrOfValues, eq_comm]
  · simp [AddrComponents.addrOfValues]

private theorem parseSegsV6_full_sound {s left : String} {addr : IPv6Addr}
    (hsplits : s.splitOn "::" = [left])
    (h : (parseNumSegsV6 left >>= finishV6) = some addr) :
    ∃ c : AddrComponents, s = c.render ∧ c.Valid ∧ addr = c.denotation := by
  cases hparse : parseNumSegsV6 left with
  | none =>
      rw [hparse] at h
      simp at h
  | some values =>
      rw [hparse] at h
      change finishV6 values = some addr at h
      obtain ⟨parts, hleft, hvalid, hvalues⟩ :=
        parseNumSegsV6_eq_some_iff.mp hparse
      obtain ⟨hlen, haddr⟩ := finishV6_eq_some_iff.mp h
      rw [hvalues] at hlen haddr
      refine ⟨.full parts, ?_, ?_, ?_⟩
      · have hs := eqIntercalateOfSplitOnEq (s := s) (sep := "::") (by decide) hsplits
        simpa [AddrComponents.render, hleft] using hs
      · exact ⟨by simpa only [groupValues, List.length_map] using hlen, hvalid⟩
      · rw [AddrComponents.denotation_full]
        exact haddr

set_option maxHeartbeats 500000 in
private theorem parseSegsV6_compressed_sound {s left right : String}
    {addr : IPv6Addr}
    (hsplits : s.splitOn "::" = [left, right])
    (h :
      (do
        let leftValues ← parseNumSegsV6 left
        let rightValues ← parseNumSegsV6 right
        if leftValues.length + rightValues.length < 8 then
          finishV6
            (leftValues ++
              List.replicate (8 - (leftValues.length + rightValues.length)) 0 ++
              rightValues)
        else none) = some addr) :
    ∃ c : AddrComponents, s = c.render ∧ c.Valid ∧ addr = c.denotation := by
  cases hleftParse : parseNumSegsV6 left with
  | none =>
      rw [hleftParse] at h
      simp at h
  | some leftValues =>
      cases hrightParse : parseNumSegsV6 right with
      | none =>
          rw [hleftParse, hrightParse] at h
          simp at h
      | some rightValues =>
          rw [hleftParse, hrightParse] at h
          change
            (if leftValues.length + rightValues.length < 8 then
              finishV6
                (leftValues ++
                  List.replicate (8 - (leftValues.length + rightValues.length)) 0 ++
                  rightValues)
            else none) = some addr at h
          split at h <;> rename_i hcount
          · obtain ⟨leftParts, hleft, hleftValid, hleftValues⟩ :=
              parseNumSegsV6_eq_some_iff.mp hleftParse
            obtain ⟨rightParts, hright, hrightValid, hrightValues⟩ :=
              parseNumSegsV6_eq_some_iff.mp hrightParse
            obtain ⟨hlen, haddr⟩ := finishV6_eq_some_iff.mp h
            have hvalues :
                leftValues ++
                    List.replicate (8 - (leftValues.length + rightValues.length)) 0 ++
                    rightValues =
                  groupValues leftParts ++
                    List.replicate (8 - (leftParts.length + rightParts.length)) 0 ++
                    groupValues rightParts := by
              rw [hleftValues, hrightValues]
              simp only [groupValues, List.length_map]
            rw [hleftValues, hrightValues] at hcount
            refine ⟨.compressed leftParts rightParts, ?_, ?_, ?_⟩
            · have hs :=
                eqIntercalateOfSplitOnEq (s := s) (sep := "::") (by decide) hsplits
              simpa [AddrComponents.render, hleft, hright, String.append_assoc] using hs
            · refine ⟨?_, hleftValid, hrightValid⟩
              simpa only [groupValues, List.length_map] using hcount
            · calc
                addr =
                    AddrComponents.addrOfValues
                      (leftValues ++
                        List.replicate
                          (8 - (leftValues.length + rightValues.length)) 0 ++
                        rightValues) := haddr
                _ = AddrComponents.addrOfValues
                      (groupValues leftParts ++
                        List.replicate
                          (8 - (leftParts.length + rightParts.length)) 0 ++
                        groupValues rightParts) :=
                    congrArg AddrComponents.addrOfValues hvalues
                _ = AddrComponents.denotation (.compressed leftParts rightParts) :=
                    (AddrComponents.denotation_compressed leftParts rightParts).symm
          · simp at h

/- Every successful Cedar IPv6-address parse exposes a full or compressed component view. -/
theorem parseSegsV6_sound {s : String} {addr : IPv6Addr}
    (h : parseSegsV6 s = some addr) :
    ∃ c : AddrComponents, s = c.render ∧ c.Valid ∧ addr = c.denotation := by
  unfold parseSegsV6 at h
  rw [← splitOnDoubleColon_eq_cedar] at h
  generalize hsplits : s.splitOn "::" = splits at h
  rcases splits with _ | ⟨left, rest⟩
  · simp at h
  rcases rest with _ | ⟨right, rest⟩
  · exact parseSegsV6_full_sound hsplits h
  rcases rest with _ | ⟨extra, rest⟩
  · exact parseSegsV6_compressed_sound hsplits h
  · simp at h

private theorem parseSegsV6_complete (c : AddrComponents) (hvalid : c.Valid) :
    parseSegsV6 c.render = some c.denotation := by
  cases c with
  | full parts =>
      obtain ⟨hlen, hall⟩ := hvalid
      have hsplit :
          (AddrComponents.render (.full parts)).splitOn "::" = [renderGroups parts] := by
        simpa [AddrComponents.render] using splitOn_renderGroups_eq_singleton parts hall
      have hparse :
          parseNumSegsV6 (renderGroups parts) = some (groupValues parts) :=
        parseNumSegsV6_eq_some_iff.mpr ⟨parts, rfl, hall, rfl⟩
      unfold parseSegsV6
      rw [← splitOnDoubleColon_eq_cedar]
      rw [hsplit]
      simp only
      rw [hparse]
      change finishV6 (groupValues parts) = some (AddrComponents.denotation (.full parts))
      apply finishV6_eq_some_iff.mpr
      exact ⟨by simpa [groupValues] using hlen, rfl⟩
  | compressed left right =>
      obtain ⟨hcount, hleft, hright⟩ := hvalid
      have hsplit :
          (AddrComponents.render (.compressed left right)).splitOn "::" =
            [renderGroups left, renderGroups right] := by
        simpa [AddrComponents.render] using
          splitOn_renderGroups_doubleColon_renderGroups left right hleft hright
      have hleftParse :
          parseNumSegsV6 (renderGroups left) = some (groupValues left) :=
        parseNumSegsV6_eq_some_iff.mpr ⟨left, rfl, hleft, rfl⟩
      have hrightParse :
          parseNumSegsV6 (renderGroups right) = some (groupValues right) :=
        parseNumSegsV6_eq_some_iff.mpr ⟨right, rfl, hright, rfl⟩
      have hvalueCount : (groupValues left).length + (groupValues right).length < 8 := by
        simpa [groupValues] using hcount
      unfold parseSegsV6
      rw [← splitOnDoubleColon_eq_cedar]
      rw [hsplit]
      simp only
      rw [hleftParse, hrightParse]
      change
        (if (groupValues left).length + (groupValues right).length < 8 then
          finishV6
            (groupValues left ++
                List.replicate
                  (8 - ((groupValues left).length + (groupValues right).length)) 0 ++
                groupValues right)
        else none) =
          some (AddrComponents.denotation (.compressed left right))
      rw [if_pos hvalueCount]
      apply finishV6_eq_some_iff.mpr
      constructor
      · simp only [List.length_append, List.length_replicate, groupValues,
          List.length_map]
        omega
      · apply Eq.trans (AddrComponents.denotation_compressed left right)
        apply congrArg AddrComponents.addrOfValues
        simp only [groupValues, List.length_map]

/-- Cedar's IPv6-address parser accepts exactly the valid component views and their value. -/
@[triptych_parser, triptych_parser_search =]
theorem parseSegsV6_eq_some_iff {s : String} {addr : IPv6Addr} :
    parseSegsV6 s = some addr ↔
      ∃ c : AddrComponents, s = c.render ∧ c.Valid ∧ addr = c.denotation := by
  constructor
  · exact parseSegsV6_sound
  · rintro ⟨c, rfl, hvalid, rfl⟩
    exact parseSegsV6_complete c hvalid

def OptionalPrefixValid : Option String → Prop
  | none => True
  | some pre => PrefixValid 3 128 pre

def renderNet (c : AddrComponents) (pre : Option String) : String :=
  c.render ++
    match pre with
    | none => ""
    | some p => "/" ++ p

def prefixValue : Option String → IPv6Prefix
  | none => ADDR_SIZE V6_WIDTH
  | some pre => Fin.ofNat (ADDR_SIZE V6_WIDTH + 1) (readNat pre)

def cidrValue (c : AddrComponents) (pre : Option String) : CedarExamples.IPv6.IPv6Net :=
  { addr := c.denotation, pre := prefixValue pre }

def netValue (c : AddrComponents) (pre : Option String) : IPNet :=
  .V6 (cidrValue c pre)

private theorem noSlashAppend {s₁ s₂ : String}
    (h₁ : ∀ c ∈ s₁.toList, (fun x : Char => decide (x = '/')) c = false)
    (h₂ : ∀ c ∈ s₂.toList, (fun x : Char => decide (x = '/')) c = false) :
    ∀ c ∈ (s₁ ++ s₂).toList, (fun x : Char => decide (x = '/')) c = false := by
  intro c hc
  rw [String.toList_append] at hc
  rcases List.mem_append.mp hc with h | h
  · exact h₁ c h
  · exact h₂ c h

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

private theorem noSlashAddrComponents (c : AddrComponents) (hvalid : c.Valid) :
    ∀ x ∈ c.render.toList, (fun y : Char => decide (y = '/')) x = false := by
  cases c with
  | full parts =>
      exact noSlashRenderGroups hvalid.2
  | compressed left right =>
      simpa [AddrComponents.render, String.append_assoc] using
        noSlashAppend (noSlashRenderGroups hvalid.2.1)
          (noSlashAppend noSlashDoubleColon (noSlashRenderGroups hvalid.2.2))

private theorem noSlashPrefix {s : String} (h : PrefixValid 3 128 s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = '/')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq
  subst c
  have hdigit := h.1.1 '/' hc
  simp [TokClass.mem] at hdigit

private theorem noDotOfHexValid {s : String} (h : HexValid s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = '.')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq
  subst c
  have hm := h.1 '.' hc
  simp [TokClass.mem] at hm

private theorem noDotColon :
    ∀ c ∈ ":".toList, (fun x : Char => decide (x = '.')) c = false := by
  simp

private theorem noDotDoubleColon :
    ∀ c ∈ "::".toList, (fun x : Char => decide (x = '.')) c = false := by
  simp

private theorem noDotAppend {s₁ s₂ : String}
    (h₁ : ∀ c ∈ s₁.toList, (fun x : Char => decide (x = '.')) c = false)
    (h₂ : ∀ c ∈ s₂.toList, (fun x : Char => decide (x = '.')) c = false) :
    ∀ c ∈ (s₁ ++ s₂).toList, (fun x : Char => decide (x = '.')) c = false := by
  intro c hc
  rw [String.toList_append] at hc
  rcases List.mem_append.mp hc with h | h
  · exact h₁ c h
  · exact h₂ c h

private theorem noDotRenderGroups {parts : List String}
    (hall : ∀ part ∈ parts, HexValid part) :
    ∀ c ∈ (renderGroups parts).toList,
      (fun x : Char => decide (x = '.')) c = false := by
  induction parts with
  | nil => simp [renderGroups]
  | cons part parts ih =>
      cases parts with
      | nil =>
          simpa [renderGroups] using noDotOfHexValid (hall part (by simp))
      | cons next tail =>
          have hpart := noDotOfHexValid (hall part (by simp))
          have htail := ih (fun item hitem => hall item (by simp [hitem]))
          simpa [renderGroups, String.append_assoc] using
            noDotAppend hpart (noDotAppend noDotColon htail)

private theorem noDotAddrComponents (c : AddrComponents) (hvalid : c.Valid) :
    ∀ x ∈ c.render.toList, (fun y : Char => decide (y = '.')) x = false := by
  cases c with
  | full parts =>
      exact noDotRenderGroups hvalid.2
  | compressed left right =>
      simpa [AddrComponents.render, String.append_assoc] using
        noDotAppend (noDotRenderGroups hvalid.2.1)
          (noDotAppend noDotDoubleColon (noDotRenderGroups hvalid.2.2))

/-- Complete successful-result specification for Cedar's IPv6/CIDR parser primitive. -/
@[triptych_parser, triptych_parser_search =]
theorem parseIPv6Net_eq_some_iff {s : String} {net : IPNet} :
    parseIPv6Net s = some net ↔
      ∃ c pre,
        s = renderNet c pre ∧ c.Valid ∧ OptionalPrefixValid pre ∧
        net = netValue c pre := by
  constructor
  · intro h
    unfold parseIPv6Net at h
    generalize hsplits : s.splitToList (· = '/') = parts at h
    rcases parts with _ | ⟨addr, rest⟩
    · simp at h
    rcases rest with _ | ⟨pre, rest⟩
    · triptych_sound at h
      obtain ⟨a, ⟨c, haddr, hvalid, ha⟩, hnet⟩ := h
      subst a
      have hs := Triptych.eq_intercalate_of_splitToList_eq '/' hsplits
      rw [String.intercalate_singleton] at hs
      exact ⟨c, none, by simpa [renderNet] using hs.trans haddr, hvalid, trivial,
        by simpa [netValue, cidrValue, prefixValue] using hnet.symm⟩
    rcases rest with _ | ⟨extra, rest⟩
    · triptych_sound at h
      obtain ⟨hp, parsedPrefix, hprefix, parsedAddr,
        ⟨c, haddr, hvalid, ha⟩, hnet⟩ := h
      simp only [Option.pure_def, Option.some.injEq] at hprefix
      subst parsedPrefix
      subst parsedAddr
      have hs := Triptych.eq_intercalate_of_splitToList_eq '/' hsplits
      rw [String.intercalate_cons_cons, String.intercalate_singleton] at hs
      exact ⟨c, some pre, by simpa [renderNet, haddr, String.append_assoc] using hs,
        hvalid, hp, by
          simpa [netValue, cidrValue, prefixValue, Fin.val_ofNat] using hnet.symm⟩
    · simp at h
  · rintro ⟨c, pre, rfl, hvalid, hp, rfl⟩
    unfold parseIPv6Net
    cases pre with
    | none =>
        have hsplit :
            (renderNet c none).splitToList (· = '/') = [c.render] := by
          simpa [renderNet] using
            (splitToListNoSep c.render (fun x : Char => decide (x = '/'))
              (noSlashAddrComponents c hvalid))
        rw [hsplit]
        simp only
        rw [parseSegsV6_complete c hvalid]
        simp [netValue, cidrValue, prefixValue]
    | some pre =>
        have hsplit :
            (renderNet c (some pre)).splitToList (· = '/') = [c.render, pre] := by
          simpa [renderNet, String.append_assoc] using
            (splitToListEq c.render pre (fun x : Char => decide (x = '/')) '/'
              (by simp) (noSlashAddrComponents c hvalid) (noSlashPrefix hp))
        have hpre :
            parsePrefixNat pre 3 (ADDR_SIZE V6_WIDTH) =
              some (Fin.ofNat (ADDR_SIZE V6_WIDTH + 1) (readNat pre)) :=
          parsePrefixNat_eq_some_iff.mpr ⟨hp, rfl⟩
        rw [hsplit]
        simp only
        rw [hpre, parseSegsV6_complete c hvalid]
        simp [netValue, cidrValue, prefixValue]

/-- The dotted-quad parser cannot accept a valid IPv6 address rendering. -/
private theorem parseSegsV4_renderAddr_none (c : AddrComponents) (hvalid : c.Valid) :
    parseSegsV4 c.render = none := by
  have hsplit :
      c.render.splitToList (· = '.') = [c.render] :=
    splitToListNoSep c.render (fun x : Char => decide (x = '.'))
      (noDotAddrComponents c hvalid)
  unfold parseSegsV4
  rw [hsplit]

private theorem parseIPv4Net_renderNet_none
    (c : AddrComponents) (pre : Option String)
    (hvalid : c.Valid) (hp : OptionalPrefixValid pre) :
    parseIPv4Net (renderNet c pre) = none := by
  unfold parseIPv4Net
  cases pre with
  | none =>
      have hsplit :
          (renderNet c none).splitToList (· = '/') = [c.render] := by
        simpa [renderNet] using
          (splitToListNoSep c.render (fun x : Char => decide (x = '/'))
            (noSlashAddrComponents c hvalid))
      rw [hsplit]
      simp only
      rw [parseSegsV4_renderAddr_none c hvalid]
      rfl
  | some pre =>
      have hsplit :
          (renderNet c (some pre)).splitToList (· = '/') = [c.render, pre] := by
        simpa [renderNet, String.append_assoc] using
          (splitToListEq c.render pre (fun x : Char => decide (x = '/')) '/'
            (by simp) (noSlashAddrComponents c hvalid) (noSlashPrefix hp))
      rw [hsplit]
      simp only
      cases parsePrefixNat pre 2 (ADDR_SIZE V4_WIDTH)
      · rfl
      · rw [parseSegsV4_renderAddr_none c hvalid]
        rfl

private theorem parseIPv4Net_isV4 {s : String} {net : IPNet}
    (h : parseIPv4Net s = some net) :
    ∃ cidr, net = IPNet.V4 cidr := by
  unfold parseIPv4Net at h
  generalize hsplits : s.splitToList (· = '/') = parts at h
  rcases parts with _ | ⟨addr, rest⟩
  · simp at h
  rcases rest with _ | ⟨pre, rest⟩
  · triptych_sound at h
    obtain ⟨a, _, hnet⟩ := h
    exact ⟨_, hnet.symm⟩
  rcases rest with _ | ⟨extra, rest⟩
  · triptych_sound at h
    obtain ⟨_, parsedPrefix, hprefix, parsedAddr, _, hnet⟩ := h
    simp only [Option.pure_def, Option.some.injEq] at hprefix
    subst parsedPrefix
    exact ⟨_, hnet.symm⟩
  · simp at h

private theorem parseIPv6Net_isV6 {s : String} {net : IPNet}
    (h : parseIPv6Net s = some net) :
    ∃ cidr, net = IPNet.V6 cidr := by
  obtain ⟨c, pre, _, _, _, hnet⟩ := parseIPv6Net_eq_some_iff.mp h
  exact ⟨_, by simpa [netValue] using hnet⟩

private theorem ipv6Only_eq_some_iff_dispatch
    {s : String} {cidr : CedarExamples.IPv6.IPv6Net} :
    CedarExamples.IPv6.ipv6Only s = some cidr ↔
      parseIPv4Net s = none ∧ parseIPv6Net s = some (.V6 cidr) := by
  unfold CedarExamples.IPv6.ipv6Only
  rw [ip_eq_parse]
  unfold CedarSupport.IPAddrInternals.parse
  cases h4 : parseIPv4Net s with
  | none =>
      simp only [Option.isSome_none]
      cases h6 : parseIPv6Net s with
      | none => simp
      | some parsed =>
          obtain ⟨cidr, rfl⟩ := parseIPv6Net_isV6 h6
          simp
  | some parsed =>
      obtain ⟨cidr, rfl⟩ := parseIPv4Net_isV4 h4
      simp

/-- Complete successful-result specification for Cedar's public IPv6-only parser. -/
theorem ipv6Only_eq_some_iff {s : String} {cidr : CedarExamples.IPv6.IPv6Net} :
    CedarExamples.IPv6.ipv6Only s = some cidr ↔
      ∃ c pre,
        s = renderNet c pre ∧ c.Valid ∧ OptionalPrefixValid pre ∧
        cidr = cidrValue c pre := by
  rw [ipv6Only_eq_some_iff_dispatch]
  constructor
  · rintro ⟨_, hparse⟩
    obtain ⟨c, pre, hs, hvalid, hp, hnet⟩ :=
      parseIPv6Net_eq_some_iff.mp hparse
    exact ⟨c, pre, hs, hvalid, hp, by simpa [netValue] using hnet⟩
  · rintro ⟨c, pre, rfl, hvalid, hp, hcidr⟩
    exact ⟨parseIPv4Net_renderNet_none c pre hvalid hp,
      parseIPv6Net_eq_some_iff.mpr
        ⟨c, pre, rfl, hvalid, hp, by simpa [netValue] using congrArg IPNet.V6 hcidr⟩⟩

end IPv6.RuleRegistryProof
