import Proofs.IPv6.RuleRegistryProof
import Proofs.IPv6.GrammarView

/-!
# End-to-end IPv6 soundness via registered parser summaries

The executable side comes entirely from `RuleRegistryProof`; `GrammarView` contributes only
facts about Triptych's generated grammar, captures, constraints, and denotation. The proof does
not use Cedar's unfinished `Cedar.Thm.Ext.IPAddr` theorem layer.
-/

open Cedar.Spec.Ext.IPAddr
open CedarSupport.ParserRules
open Triptych

namespace IPv6.RuleRegistrySoundness

open IPv6.RuleRegistryProof

def toGrammarAddr : AddrComponents → IPv6.GrammarView.Addr
  | .full parts => .full parts
  | .compressed left right => .compressed left right

def ofGrammarAddr : IPv6.GrammarView.Addr → AddrComponents
  | .full parts => .full parts
  | .compressed left right => .compressed left right

def toGrammarView (c : AddrComponents) (pre : Option String) :
    IPv6.GrammarView.View :=
  ⟨toGrammarAddr c, pre⟩

@[simp] theorem toGrammarAddr_ofGrammarAddr (addr : IPv6.GrammarView.Addr) :
    toGrammarAddr (ofGrammarAddr addr) = addr := by
  cases addr <;> rfl

@[simp] theorem toGrammarAddr_render (c : AddrComponents) :
    (toGrammarAddr c).render = c.render := by
  cases c <;> rfl

@[simp] theorem toGrammarView_render (c : AddrComponents) (pre : Option String) :
    (toGrammarView c pre).render = renderNet c pre := by
  cases c <;> cases pre <;> rfl

private theorem prefixValid_iff {s : String} :
    PrefixValid 3 128 s ↔
      IPv6.GrammarView.OptionalPrefixValid (some s) := by
  unfold PrefixValid IPv6.GrammarView.OptionalPrefixValid
    IPv6.GrammarView.OptionalPrefixSyntax
    IPv6.GrammarView.OptionalPrefixConstraints
    IPv6.GrammarView.PrefixConstraints
  constructor
  · rintro ⟨hsyntax, hcanonical, hbound⟩
    refine ⟨hsyntax, hcanonical, ?_⟩
    change (readNat s : Int) ≤ 128
    omega
  · rintro ⟨hsyntax, hcanonical, hbound⟩
    refine ⟨hsyntax, hcanonical, ?_⟩
    change (readNat s : Int) ≤ 128 at hbound
    omega

private theorem optionalPrefixValid_iff (pre : Option String) :
    OptionalPrefixValid pre ↔ IPv6.GrammarView.OptionalPrefixValid pre := by
  cases pre with
  | none =>
      simp [OptionalPrefixValid, IPv6.GrammarView.OptionalPrefixValid,
        IPv6.GrammarView.OptionalPrefixSyntax,
        IPv6.GrammarView.OptionalPrefixConstraints]
  | some pre =>
      simpa [OptionalPrefixValid] using (prefixValid_iff (s := pre))

private theorem addrValid_iff (c : AddrComponents) :
    c.Valid ↔ (toGrammarAddr c).Valid := by
  cases c with
  | full parts =>
      simp [AddrComponents.Valid, toGrammarAddr, IPv6.GrammarView.Addr.Valid,
        IPv6.GrammarView.Addr.SyntaxValid, IPv6.GrammarView.Addr.Constraints,
        HexValid, IPv6.GrammarView.HexValid]
  | compressed left right =>
      constructor
      · rintro ⟨hcount, hleft, hright⟩
        exact ⟨⟨by omega, by omega, hleft, hright⟩, hcount⟩
      · rintro ⟨⟨_, _, hleft, hright⟩, hcount⟩
        exact ⟨hcount, hleft, hright⟩

theorem viewValid_iff (c : AddrComponents) (pre : Option String) :
    c.Valid ∧ OptionalPrefixValid pre ↔ (toGrammarView c pre).Valid := by
  rw [addrValid_iff, optionalPrefixValid_iff]
  unfold toGrammarView IPv6.GrammarView.View.Valid
    IPv6.GrammarView.Addr.Valid IPv6.GrammarView.OptionalPrefixValid
  constructor
  · rintro ⟨⟨hsyntax, hconstraints⟩, hpreSyntax, hpreConstraints⟩
    exact ⟨⟨hsyntax, hpreSyntax⟩, hconstraints, hpreConstraints⟩
  · rintro ⟨⟨hsyntax, hpreSyntax⟩, hconstraints, hpreConstraints⟩
    exact ⟨⟨hsyntax, hconstraints⟩, hpreSyntax, hpreConstraints⟩

@[simp] private theorem optionMap_readHex_getD (part : Option String) :
    (part.map (fun s => BitVec.ofNat 16 (CedarExamples.IPv6.readHex s))).getD 0 =
      BitVec.ofNat 16 (CedarExamples.IPv6.readHex (part.getD "")) := by
  cases part <;> simp [CedarExamples.IPv6.readHex]

private theorem addrOfValues_groupValues (parts : List String) :
    AddrComponents.addrOfValues (groupValues parts) =
      CedarExamples.IPv6.toV6Addr parts := by
  unfold AddrComponents.addrOfValues groupValues CedarExamples.IPv6.toV6Addr
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  repeat rw [optionMap_readHex_getD]

private theorem addrDenotation_eq (c : AddrComponents) :
    c.denotation = (toGrammarAddr c).denotation := by
  cases c with
  | full parts =>
      exact addrOfValues_groupValues parts
  | compressed left right =>
      rw [AddrComponents.denotation_compressed]
      change
        AddrComponents.addrOfValues
            (groupValues left ++
              List.replicate (8 - (left.length + right.length)) 0 ++
              groupValues right) =
          CedarExamples.IPv6.toV6Addr
            (left ++ List.replicate (8 - (left.length + right.length)) "" ++ right)
      rw [← addrOfValues_groupValues
        (left ++ List.replicate (8 - (left.length + right.length)) "" ++ right)]
      apply congrArg AddrComponents.addrOfValues
      simp [groupValues, CedarExamples.IPv6.readHex]

private theorem prefixValue_eq (pre : Option String)
    (h : OptionalPrefixValid pre) :
    prefixValue pre =
      if pre.getD "" == "" then
        (ADDR_SIZE V6_WIDTH : IPv6Prefix)
      else
        (readNat (pre.getD "") : IPv6Prefix) := by
  cases pre with
  | none => rfl
  | some pre =>
      change PrefixValid 3 128 pre at h
      have hne : pre ≠ "" := by
        intro hempty
        have hlength := h.1.2.1
        simp [hempty] at hlength
      simp [prefixValue, hne]
      have hbound : readNat pre ≤ 128 := h.2.2
      have hlt : readNat pre < ADDR_SIZE V6_WIDTH + 1 := by
        change readNat pre < 129
        omega
      rw [Nat.mod_eq_of_lt hlt]

theorem cidrValue_eq_viewDenotation (c : AddrComponents) (pre : Option String)
    (hc : c.Valid) (hp : OptionalPrefixValid pre) :
    cidrValue c pre = (toGrammarView c pre).denotation := by
  rw [show cidrValue c pre =
      { addr := c.denotation, pre := prefixValue pre } by rfl]
  rw [addrDenotation_eq, prefixValue_eq pre hp]
  cases c with
  | full parts =>
      have hne : parts ≠ [] := by
        intro hempty
        have hlength := hc.1
        simp [hempty] at hlength
      simp [toGrammarView, toGrammarAddr, IPv6.GrammarView.View.denotation,
        IPv6.GrammarView.Addr.denotation, CedarExamples.IPv6.toIPv6Net, hne]
  | compressed left right =>
      simp [toGrammarView, toGrammarAddr, IPv6.GrammarView.View.denotation,
        IPv6.GrammarView.Addr.denotation, CedarExamples.IPv6.toIPv6Net]

private def oldHexDigitValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

private theorem hexDigitValueInt_eq_old {c : Char} (h : TokClass.hexDigit.mem c) :
    hexDigitValueInt c = oldHexDigitValue c := by
  simp only [TokClass.mem] at h
  unfold hexDigitValueInt oldHexDigitValue
  rcases h with h | h | h
  · have hb' : '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat := by
      simpa only [Char.le_def, UInt32.le_iff_toNat_le, Char.toNat] using h
    have hb : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
      have h0 : '0'.toNat = 48 := by decide
      have h9 : '9'.toNat = 57 := by decide
      omega
    have hbInt : (48 : Int) ≤ c.toNat ∧ (c.toNat : Int) ≤ 57 := by omega
    have hd : c.isDigit := Char.isDigit_iff_toNat.mpr hb
    have hcast : ((c.toNat - 48 : Nat) : Int) = (c.toNat : Int) - 48 := by omega
    simp [hd, hbInt, hcast]
  · have hb' : 'a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'f'.toNat := by
      simpa only [Char.le_def, UInt32.le_iff_toNat_le, Char.toNat] using h
    have hb : 97 ≤ c.toNat ∧ c.toNat ≤ 102 := by
      have ha : 'a'.toNat = 97 := by decide
      have hf : 'f'.toNat = 102 := by decide
      omega
    have hbInt : (97 : Int) ≤ c.toNat ∧ (c.toNat : Int) ≤ 102 := by omega
    have hn : ¬c.isDigit := by
      intro hd
      have hd' := Char.isDigit_iff_toNat.mp hd
      have h0 : '0'.toNat = 48 := by decide
      have h9 : '9'.toNat = 57 := by decide
      omega
    have hl : ('a' ≤ c && c ≤ 'f') = true := by simp [h]
    have hcast : ((c.toNat - 97 : Nat) : Int) = (c.toNat : Int) - 97 := by omega
    have hnotDigitInt : ¬((48 : Int) ≤ c.toNat ∧ (c.toNat : Int) ≤ 57) := by omega
    simp [hn, hnotDigitInt, hbInt, hl, hcast]
  · have hb' : 'A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'F'.toNat := by
      simpa only [Char.le_def, UInt32.le_iff_toNat_le, Char.toNat] using h
    have hb : 65 ≤ c.toNat ∧ c.toNat ≤ 70 := by
      have hA : 'A'.toNat = 65 := by decide
      have hF : 'F'.toNat = 70 := by decide
      omega
    have hbInt : (65 : Int) ≤ c.toNat ∧ (c.toNat : Int) ≤ 70 := by omega
    have hn : ¬c.isDigit := by
      intro hd
      have hd' := Char.isDigit_iff_toNat.mp hd
      have h0 : '0'.toNat = 48 := by decide
      have h9 : '9'.toNat = 57 := by decide
      omega
    have hl : ('a' ≤ c && c ≤ 'f') = false := by
      apply Bool.eq_false_iff.mpr
      intro hl
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
      have hlraw : 'a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'f'.toNat := by
        simpa only [Char.le_def, UInt32.le_iff_toNat_le, Char.toNat] using hl
      have ha : 'a'.toNat = 97 := by decide
      have hf : 'f'.toNat = 102 := by decide
      omega
    have hu : ('A' ≤ c && c ≤ 'F') = true := by simp [h]
    have hcast : ((c.toNat - 65 : Nat) : Int) = (c.toNat : Int) - 65 := by omega
    have hnotDigitInt : ¬((48 : Int) ≤ c.toNat ∧ (c.toNat : Int) ≤ 57) := by omega
    have hnotLowerInt : ¬((97 : Int) ≤ c.toNat ∧ (c.toNat : Int) ≤ 102) := by omega
    simp [hn, hnotDigitInt, hnotLowerInt, hbInt, hl, hu, hcast]

private theorem hexFold_eq (characters : List Char)
    (h : ∀ c ∈ characters, TokClass.hexDigit.mem c) (accumulator : Nat) :
    characters.foldl (fun acc c => acc * 16 + hexDigitValueInt c) accumulator =
      (characters.foldl (fun acc c => acc * 16 + oldHexDigitValue c) accumulator : Nat) := by
  induction characters generalizing accumulator with
  | nil => simp
  | cons character rest ih =>
      simp only [List.foldl_cons]
      rw [hexDigitValueInt_eq_old (h character (by simp))]
      norm_cast
      apply ih
      intro c hc
      exact h c (by simp [hc])

private theorem hexOf_eq_readHex {s : String} (h : HexValid s) :
    hexOf s = CedarExamples.IPv6.readHex s := by
  unfold hexOf hexOfChars CedarExamples.IPv6.readHex
  simpa [oldHexDigitValue] using hexFold_eq s.toList h.1 0

private def encodedGroupsValue (parts : List String) (accumulator : Int := 0) : Int :=
  parts.foldl (fun acc part => acc * 65536 + hexOf part) accumulator

private theorem hexChar_ne_colon {c : Char} (h : TokClass.hexDigit.mem c) :
    c ≠ ':' := by
  intro heq
  subst c
  simp [TokClass.mem] at h

private theorem hexSeqOfChars_append_hex
    (characters tail : List Char)
    (h : ∀ c ∈ characters, TokClass.hexDigit.mem c)
    (accumulator current : Int) :
    hexSeqOfChars (characters ++ tail) accumulator current =
      hexSeqOfChars tail accumulator
        (characters.foldl (fun acc c => acc * 16 + hexDigitValueInt c) current) := by
  induction characters generalizing current with
  | nil => rfl
  | cons character rest ih =>
      simp only [List.cons_append, hexSeqOfChars, List.foldl_cons]
      rw [if_neg (hexChar_ne_colon (h character (by simp)))]
      apply ih
      intro c hc
      exact h c (by simp [hc])

private theorem hexSeqOfChars_group_end
    (group : String) (h : ∀ c ∈ group.toList, TokClass.hexDigit.mem c)
    (accumulator : Int) :
    hexSeqOfChars group.toList accumulator 0 =
      accumulator * 65536 + hexOf group := by
  have happend := hexSeqOfChars_append_hex group.toList [] h accumulator 0
  simp only [List.append_nil] at happend
  simpa [hexSeqOfChars, hexOf, hexOfChars] using happend

private theorem hexSeqOfChars_group_cons
    (group : String) (tail : List Char)
    (h : ∀ c ∈ group.toList, TokClass.hexDigit.mem c)
    (accumulator : Int) :
    hexSeqOfChars (group.toList ++ ':' :: tail) accumulator 0 =
      hexSeqOfChars tail (accumulator * 65536 + hexOf group) 0 := by
  rw [hexSeqOfChars_append_hex group.toList (':' :: tail) h accumulator 0]
  simp [hexSeqOfChars, hexOf, hexOfChars]

private theorem hexSeq_renderGroups_nonempty (parts : List String) (hne : parts ≠ [])
    (h : ∀ part ∈ parts, HexValid part) (accumulator : Int) :
    hexSeqOfChars (IPv6.GrammarView.renderGroups parts).toList accumulator 0 =
      encodedGroupsValue parts accumulator := by
  induction parts generalizing accumulator with
  | nil => contradiction
  | cons part rest ih =>
      cases rest with
      | nil =>
          simpa [IPv6.GrammarView.renderGroups, encodedGroupsValue] using
            hexSeqOfChars_group_end part (h part (by simp)).1 accumulator
      | cons next tail =>
          rw [show IPv6.GrammarView.renderGroups (part :: next :: tail) =
              part ++ ":" ++ IPv6.GrammarView.renderGroups (next :: tail) by
            unfold IPv6.GrammarView.renderGroups
            rw [String.intercalate_cons_cons]]
          rw [String.toList_append, String.toList_append]
          have hcolon : ":".toList = [':'] := by decide
          rw [hcolon, List.append_assoc]
          change
            hexSeqOfChars
                (part.toList ++
                  ':' :: (IPv6.GrammarView.renderGroups (next :: tail)).toList)
                accumulator 0 =
              encodedGroupsValue (part :: next :: tail) accumulator
          rw [hexSeqOfChars_group_cons part
            (IPv6.GrammarView.renderGroups (next :: tail)).toList
            (h part (by simp)).1 accumulator]
          rw [ih (by simp) (by
            intro candidate hc
            exact h candidate (by simp [hc]))]
          rfl

private theorem hexSeq_renderGroups (parts : List String)
    (h : ∀ part ∈ parts, HexValid part) :
    hexSeqOf (IPv6.GrammarView.renderGroups parts) = encodedGroupsValue parts := by
  cases parts with
  | nil => rfl
  | cons part rest =>
      unfold hexSeqOf
      simpa using
        hexSeq_renderGroups_nonempty (part :: rest) (by simp) h 0

private theorem ipv6Addr_toNat_mk
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : BitVec 16) :
    (IPv6Addr.mk a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇).toNat =
      (((((((a₀.toNat * 65536 + a₁.toNat) * 65536 + a₂.toNat) * 65536 +
          a₃.toNat) * 65536 + a₄.toNat) * 65536 + a₅.toNat) * 65536 +
          a₆.toNat) * 65536 + a₇.toNat) := by
  unfold IPv6Addr.mk
  simp only [BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₇)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₆)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₅)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₄)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₃)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₂)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₁)]
  simp [Nat.shiftLeft_eq]

private theorem hexOf_eq_readHex_or_empty {part : String}
    (h : HexValid part ∨ part = "") :
    hexOf part = CedarExamples.IPv6.readHex part := by
  rcases h with h | rfl
  · exact hexOf_eq_readHex h
  · simp [hexOf, hexOfChars, CedarExamples.IPv6.readHex]

private theorem readHex_lt_or_empty {part : String}
    (h : HexValid part ∨ part = "") :
    CedarExamples.IPv6.readHex part < 65536 := by
  rcases h with h | rfl
  · exact Nat.lt_of_le_of_lt (readHex_le h) (by decide)
  · simp [CedarExamples.IPv6.readHex]

private theorem encodedGroupsValue_eq_toV6Addr {parts : List String}
    (hlength : parts.length = 8)
    (hvalid : ∀ part ∈ parts, HexValid part ∨ part = "") :
    encodedGroupsValue parts = (CedarExamples.IPv6.toV6Addr parts).toNat := by
  rcases parts with _ | ⟨p₀, parts⟩
  · simp at hlength
  rcases parts with _ | ⟨p₁, parts⟩
  · simp at hlength
  rcases parts with _ | ⟨p₂, parts⟩
  · simp at hlength
  rcases parts with _ | ⟨p₃, parts⟩
  · simp at hlength
  rcases parts with _ | ⟨p₄, parts⟩
  · simp at hlength
  rcases parts with _ | ⟨p₅, parts⟩
  · simp at hlength
  rcases parts with _ | ⟨p₆, parts⟩
  · simp at hlength
  rcases parts with _ | ⟨p₇, parts⟩
  · simp at hlength
  cases parts with
  | nil =>
      have h₀ := hvalid p₀ (by simp)
      have h₁ := hvalid p₁ (by simp)
      have h₂ := hvalid p₂ (by simp)
      have h₃ := hvalid p₃ (by simp)
      have h₄ := hvalid p₄ (by simp)
      have h₅ := hvalid p₅ (by simp)
      have h₆ := hvalid p₆ (by simp)
      have h₇ := hvalid p₇ (by simp)
      simp [encodedGroupsValue, CedarExamples.IPv6.toV6Addr, ipv6Addr_toNat_mk,
        hexOf_eq_readHex_or_empty h₀, hexOf_eq_readHex_or_empty h₁,
        hexOf_eq_readHex_or_empty h₂, hexOf_eq_readHex_or_empty h₃,
        hexOf_eq_readHex_or_empty h₄, hexOf_eq_readHex_or_empty h₅,
        hexOf_eq_readHex_or_empty h₆, hexOf_eq_readHex_or_empty h₇,
        Nat.mod_eq_of_lt (readHex_lt_or_empty h₀),
        Nat.mod_eq_of_lt (readHex_lt_or_empty h₁),
        Nat.mod_eq_of_lt (readHex_lt_or_empty h₂),
        Nat.mod_eq_of_lt (readHex_lt_or_empty h₃),
        Nat.mod_eq_of_lt (readHex_lt_or_empty h₄),
        Nat.mod_eq_of_lt (readHex_lt_or_empty h₅),
        Nat.mod_eq_of_lt (readHex_lt_or_empty h₆),
        Nat.mod_eq_of_lt (readHex_lt_or_empty h₇)]
  | cons p₈ rest =>
      simp at hlength

private theorem encodedGroupsFold_accumulator (parts : List String) (accumulator : Int) :
    parts.foldl (fun acc part => acc * 65536 + hexOf part) accumulator =
      accumulator * 65536 ^ parts.length +
        parts.foldl (fun acc part => acc * 65536 + hexOf part) 0 := by
  induction parts generalizing accumulator with
  | nil => simp
  | cons part rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih (accumulator * 65536 + hexOf part)]
      have hzero : (0 : Int) * 65536 + hexOf part = hexOf part := by simp
      rw [hzero, ih (hexOf part)]
      rw [Int.pow_succ', Int.add_mul, Int.mul_assoc]
      ac_rfl

private theorem encodedGroupsValue_accumulator (parts : List String) (accumulator : Int) :
    encodedGroupsValue parts accumulator =
      accumulator * 65536 ^ parts.length + encodedGroupsValue parts :=
  encodedGroupsFold_accumulator parts accumulator

private theorem encodedGroupsValue_append (left right : List String) :
    encodedGroupsValue (left ++ right) =
      encodedGroupsValue left * 65536 ^ right.length + encodedGroupsValue right := by
  unfold encodedGroupsValue
  rw [List.foldl_append]
  exact encodedGroupsValue_accumulator right
    (left.foldl (fun acc part => acc * 65536 + hexOf part) 0)

private theorem encodedGroupsValue_replicate_empty (repetitions : Nat) :
    encodedGroupsValue (List.replicate repetitions "") = 0 := by
  induction repetitions with
  | zero => rfl
  | succ repetitions ih =>
      rw [List.replicate_succ]
      change encodedGroupsValue (List.replicate repetitions "") 0 = 0
      exact ih

private theorem fullAddressCode_eq (parts : List String)
    (hlength : parts.length = 8)
    (hvalid : ∀ part ∈ parts, HexValid part) :
    ((CedarExamples.IPv6.toV6Addr parts).toNat : Int) =
      hexSeqOf (IPv6.GrammarView.renderGroups parts) := by
  rw [hexSeq_renderGroups parts hvalid]
  exact (encodedGroupsValue_eq_toV6Addr hlength
    (fun part hpart => Or.inl (hvalid part hpart))).symm

private theorem compressedAddressCode_eq (left right : List String)
    (hcount : left.length + right.length < 8)
    (hleft : ∀ part ∈ left, HexValid part)
    (hright : ∀ part ∈ right, HexValid part) :
    ((CedarExamples.IPv6.toV6Addr
      (left ++ List.replicate (8 - (left.length + right.length)) "" ++ right)).toNat : Int) =
        hexSeqOf (IPv6.GrammarView.renderGroups left) *
            65536 ^ (8 - segmentsOf (IPv6.GrammarView.renderGroups left)).toNat +
          hexSeqOf (IPv6.GrammarView.renderGroups right) := by
  have hleftSegments :=
    IPv6.GrammarView.segments_renderGroups_all left hleft
  have hrightSegments :=
    IPv6.GrammarView.segments_renderGroups_all right hright
  have hlength :
      (left ++ List.replicate (8 - (left.length + right.length)) "" ++ right).length =
        8 := by
    simp
    omega
  have hall :
      ∀ part ∈ left ++ List.replicate (8 - (left.length + right.length)) "" ++ right,
        HexValid part ∨ part = "" := by
    intro part hpart
    rcases List.mem_append.mp hpart with hfront | hrightMem
    · rcases List.mem_append.mp hfront with hleftMem | hempty
      · exact Or.inl (hleft part hleftMem)
      · exact Or.inr (List.eq_of_mem_replicate hempty)
    · exact Or.inl (hright part hrightMem)
  rw [← encodedGroupsValue_eq_toV6Addr hlength hall]
  rw [encodedGroupsValue_append, encodedGroupsValue_append,
    encodedGroupsValue_replicate_empty]
  rw [hexSeq_renderGroups left hleft, hexSeq_renderGroups right hright]
  rw [hleftSegments]
  simp only [List.length_append, List.length_replicate]
  have hsub : ((8 : Int) - left.length).toNat = 8 - left.length := by
    omega
  rw [hsub]
  have hexponent :
      8 - (left.length + right.length) + right.length = 8 - left.length := by
    omega
  simp
  rw [Int.mul_assoc, ← Int.pow_add, hexponent]

private theorem addressCode_eq (c : AddrComponents) (hc : c.Valid) :
    (c.denotation.toNat : Int) =
      match c with
      | .full parts =>
          hexSeqOf (IPv6.GrammarView.renderGroups parts)
      | .compressed left right =>
          hexSeqOf (IPv6.GrammarView.renderGroups left) *
              65536 ^ (8 - segmentsOf (IPv6.GrammarView.renderGroups left)).toNat +
            hexSeqOf (IPv6.GrammarView.renderGroups right) := by
  rw [addrDenotation_eq c]
  cases c with
  | full parts =>
      exact fullAddressCode_eq parts hc.1 hc.2
  | compressed left right =>
      exact compressedAddressCode_eq left right hc.1 hc.2.1 hc.2.2

private theorem prefix_toNat_of_le (n : Nat) (h : n ≤ 128) :
    (n : IPv6Prefix).toNat = n := by
  have hall : ∀ i : Fin 129, (i.val : IPv6Prefix).toNat = i.val := by
    decide
  exact hall ⟨n, by omega⟩

private theorem prefixValue_toNat (pre : Option String) (h : OptionalPrefixValid pre) :
    (prefixValue pre).toNat =
      if pre.getD "" = "" then 128 else readNat (pre.getD "") := by
  cases pre with
  | none => rfl
  | some pre =>
      change PrefixValid 3 128 pre at h
      have hne : pre ≠ "" := by
        intro hempty
        have hlength := h.1.2.1
        simp [hempty] at hlength
      simp only [Option.getD_some, if_neg hne]
      unfold prefixValue
      have hle : readNat pre ≤ 128 := h.2.2
      have hbound : readNat pre < 129 := by omega
      change ((Fin.ofNat 129 (readNat pre)).val : IPv6Prefix).toNat = readNat pre
      rw [Fin.val_ofNat, Nat.mod_eq_of_lt hbound]
      exact prefix_toNat_of_le (readNat pre) hle

private theorem prefix_toNat_le (pre : IPv6Prefix) : pre.toNat ≤ 128 := by
  cases pre with
  | none => decide
  | some pre =>
      have hbound := BitVec.isLt pre
      change pre.toNat < 2 ^ 7 at hbound
      change pre.toNat ≤ 128
      omega

private theorem prefix_of_toNat (pre : IPv6Prefix) :
    (pre.toNat : IPv6Prefix) = pre := by
  cases pre with
  | none => rfl
  | some pre =>
      have hbound := BitVec.isLt pre
      change pre.toNat < 2 ^ 7 at hbound
      change (if pre.toNat < 128 then some (BitVec.ofNat 7 pre.toNat) else none) = some pre
      rw [if_pos hbound]
      congr
      apply BitVec.eq_of_toNat_eq
      simp

theorem ipv6CodeToNet_netToCode (net : CedarExamples.IPv6.IPv6Net) :
    CedarExamples.IPv6.ipv6CodeToNet (CedarExamples.IPv6.ipv6NetToCode net) = net := by
  rcases net with ⟨addr, pre⟩
  have hp : pre.toNat < 129 := by
    have := prefix_toNat_le pre
    omega
  have hnonneg :
      (0 : Int) ≤ (addr.toNat : Int) * 129 + pre.toNat := by
    omega
  have htoNat :
      ((addr.toNat : Int) * 129 + pre.toNat).toNat =
        addr.toNat * 129 + pre.toNat := by
    apply Int.ofNat_inj.mp
    rw [Int.toNat_of_nonneg hnonneg]
    simp
  unfold CedarExamples.IPv6.ipv6CodeToNet CedarExamples.IPv6.ipv6NetToCode
  rw [htoNat, CIDR.mk.injEq]
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    have hdiv : (addr.toNat * 129 + pre.toNat) / 129 = addr.toNat := by
      omega
    rw [hdiv]
    exact Nat.mod_eq_of_lt (BitVec.isLt addr)
  · have hmod : (addr.toNat * 129 + pre.toNat) % 129 = pre.toNat := by
      omega
    rw [hmod]
    exact prefix_of_toNat pre

private theorem cidrValue_code (c : AddrComponents) (pre : Option String)
    (hc : c.Valid) (hp : OptionalPrefixValid pre) :
    CedarExamples.IPv6.ipv6NetToCode (cidrValue c pre) =
      (toGrammarView c pre).encodedDenotation := by
  unfold CedarExamples.IPv6.ipv6NetToCode cidrValue
  rw [addressCode_eq c hc, prefixValue_toNat pre hp]
  cases c with
  | full parts =>
      have hsegments :=
        IPv6.GrammarView.segments_renderGroups_all parts hc.2
      have hne : IPv6.GrammarView.renderGroups parts ≠ "" := by
        intro hempty
        rw [hempty] at hsegments
        simp [segmentsOf] at hsegments
        have hlength : parts.length = 8 := hc.1
        omega
      by_cases hpre : pre.getD "" = "" <;>
        simp [toGrammarView, toGrammarAddr, IPv6.GrammarView.View.encodedDenotation,
          IPv6.value, Triptych.natOf, hne, hpre]
  | compressed left right =>
      by_cases hpre : pre.getD "" = "" <;>
        simp [toGrammarView, toGrammarAddr, IPv6.GrammarView.View.encodedDenotation,
          IPv6.value, Triptych.natOf, hpre]

theorem view_encodedDenotation (v : IPv6.GrammarView.View) (h : v.Valid) :
    CedarExamples.IPv6.ipv6NetToCode v.denotation = v.encodedDenotation := by
  let c := ofGrammarAddr v.addr
  have hround : toGrammarView c v.«prefix» = v := by
    cases v with
    | mk addr pre =>
        cases addr <;> rfl
  have hext : c.Valid ∧ OptionalPrefixValid v.«prefix» :=
    (viewValid_iff c v.«prefix»).mpr (by simpa [hround] using h)
  have hdenotation : cidrValue c v.«prefix» = v.denotation := by
    simpa [hround] using
      cidrValue_eq_viewDenotation c v.«prefix» hext.1 hext.2
  calc
    CedarExamples.IPv6.ipv6NetToCode v.denotation =
        CedarExamples.IPv6.ipv6NetToCode (cidrValue c v.«prefix») :=
      congrArg CedarExamples.IPv6.ipv6NetToCode hdenotation.symm
    _ = (toGrammarView c v.«prefix»).encodedDenotation :=
      cidrValue_code c v.«prefix» hext.1 hext.2
    _ = v.encodedDenotation :=
      congrArg IPv6.GrammarView.View.encodedDenotation hround

/-- The external parser returns exactly the values accepted and denoted by the Triptych spec. -/
theorem parser_agrees (s : String) (net : CedarExamples.IPv6.IPv6Net) :
    CedarExamples.IPv6.ipv6Only s = some net ↔
      IPv6.IsValid s ∧
        IPv6.computeValue s = some (CedarExamples.IPv6.ipv6NetToCode net) := by
  rw [ipv6Only_eq_some_iff]
  constructor
  · rintro ⟨c, pre, hs, hc, hp, rfl⟩
    have hview : (toGrammarView c pre).Valid :=
      (viewValid_iff c pre).mp ⟨hc, hp⟩
    have hrender : (toGrammarView c pre).render = s := by
      rw [toGrammarView_render, ← hs]
    have hvalid : IPv6.IsValid s :=
      (IPv6.GrammarView.isValid_iff_view s).mpr
        ⟨toGrammarView c pre, hrender, hview⟩
    have hcompute :=
      IPv6.GrammarView.computeValue_eq_of_view (toGrammarView c pre) hview.1
    refine ⟨hvalid, ?_⟩
    calc
      IPv6.computeValue s =
          some (toGrammarView c pre).encodedDenotation := by simpa [hrender] using hcompute
      _ = some (CedarExamples.IPv6.ipv6NetToCode (cidrValue c pre)) :=
        congrArg some (cidrValue_code c pre hc hp).symm
  · rintro ⟨hvalid, hcompute⟩
    obtain ⟨v, hrender, hview⟩ :=
      (IPv6.GrammarView.isValid_iff_view s).mp hvalid
    let c := ofGrammarAddr v.addr
    have hround : toGrammarView c v.«prefix» = v := by
      cases v with
      | mk addr pre =>
          cases addr <;> rfl
    have hext : c.Valid ∧ OptionalPrefixValid v.«prefix» :=
      (viewValid_iff c v.«prefix»).mpr (by simpa [hround] using hview)
    have hviewCompute :
        IPv6.computeValue s = some v.encodedDenotation := by
      simpa [hrender] using
        IPv6.GrammarView.computeValue_eq_of_view v hview.1
    have hcode :
        CedarExamples.IPv6.ipv6NetToCode net =
          CedarExamples.IPv6.ipv6NetToCode (cidrValue c v.«prefix») := by
      have hparsed := Option.some.inj (hcompute.symm.trans hviewCompute)
      exact hparsed.trans (by
        simpa [hround] using (cidrValue_code c v.«prefix» hext.1 hext.2).symm)
    refine ⟨c, v.«prefix», ?_, hext.1, hext.2, ?_⟩
    · calc
        s = v.render := hrender.symm
        _ = (toGrammarView c v.«prefix»).render :=
          congrArg IPv6.GrammarView.View.render hround.symm
        _ = renderNet c v.«prefix» := toGrammarView_render c v.«prefix»
    · have hnet := congrArg CedarExamples.IPv6.ipv6CodeToNet hcode
      rw [ipv6CodeToNet_netToCode, ipv6CodeToNet_netToCode] at hnet
      exact hnet

private def hex16 (n : Nat) : String :=
  hexDigitRepr ((n % 0x10000) / 0x1000) ++
    hexDigitRepr ((n % 0x1000) / 0x100) ++
    hexDigitRepr ((n % 0x100) / 0x10) ++
    hexDigitRepr ((n % 0x10) / 0x1)

private theorem digitChar_hex {n : Nat} (h : n < 16) :
    TokClass.hexDigit.mem n.digitChar := by
  have hn :
      n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
      n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by
    omega
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem hex16_valid (n : Nat) : HexValid (hex16 n) := by
  have h₀ : (n % 0x10000) / 0x1000 < 16 := by omega
  have h₁ : (n % 0x1000) / 0x100 < 16 := by omega
  have h₂ : (n % 0x100) / 0x10 < 16 := by omega
  have h₃ : (n % 0x10) / 0x1 < 16 := by omega
  unfold HexValid IsHexDigitsBetween TokClass.all hex16 hexDigitRepr
  constructor
  · intro c hc
    simp only [String.toList_append, String.toList_singleton, List.mem_append,
      List.mem_singleton] at hc
    rcases hc with ((rfl | rfl) | rfl) | rfl
    · exact digitChar_hex h₀
    · exact digitChar_hex h₁
    · exact digitChar_hex h₂
    · exact digitChar_hex h₃
  · simp

private theorem readHex_digitChar {n : Nat} (h : n < 16) :
    (if n.digitChar.isDigit then n.digitChar.toNat - '0'.toNat
     else if 'a' ≤ n.digitChar && n.digitChar ≤ 'f' then
       n.digitChar.toNat - 'a'.toNat + 10
     else if 'A' ≤ n.digitChar && n.digitChar ≤ 'F' then
       n.digitChar.toNat - 'A'.toNat + 10
     else 0) = n := by
  have hn :
      n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
      n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by
    omega
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem readHex_hex16 (n : Nat) :
    CedarExamples.IPv6.readHex (hex16 n) = n % 0x10000 := by
  have h₀ : (n % 0x10000) / 0x1000 < 16 := by omega
  have h₁ : (n % 0x1000) / 0x100 < 16 := by omega
  have h₂ : (n % 0x100) / 0x10 < 16 := by omega
  have h₃ : (n % 0x10) / 0x1 < 16 := by omega
  unfold CedarExamples.IPv6.readHex hex16 hexDigitRepr
  simp only [String.foldl_eq_foldl_toList, String.toList_append,
    String.toList_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [readHex_digitChar h₀, readHex_digitChar h₁, readHex_digitChar h₂,
    readHex_digitChar h₃]
  omega

private theorem addrValue_of_addr (addr : IPv6Addr) :
    let v := addr.toNat
    AddrComponents.addrOfValues
        (groupValues
          [hex16 ((v >>> 112) &&& 0xffff), hex16 ((v >>> 96) &&& 0xffff),
            hex16 ((v >>> 80) &&& 0xffff), hex16 ((v >>> 64) &&& 0xffff),
            hex16 ((v >>> 48) &&& 0xffff), hex16 ((v >>> 32) &&& 0xffff),
            hex16 ((v >>> 16) &&& 0xffff), hex16 (v &&& 0xffff)]) =
      addr := by
  dsimp only
  unfold AddrComponents.addrOfValues groupValues
  simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
  have hchunk (start : Nat) :
      BitVec.ofNat 16
          (CedarExamples.IPv6.readHex
            (hex16 ((addr.toNat >>> start) &&& 0xffff))) =
        addr.extractLsb' start 16 := by
    rw [readHex_hex16]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat]
    have hmask : (0xffff : Nat) = 2 ^ 16 - 1 := by decide
    rw [hmask, Nat.and_two_pow_sub_one_eq_mod]
    simp
  rw [hchunk 112, hchunk 96, hchunk 80, hchunk 64, hchunk 48, hchunk 32, hchunk 16]
  rw [show BitVec.ofNat 16
      (CedarExamples.IPv6.readHex (hex16 (addr.toNat &&& 0xffff))) =
        addr.extractLsb' 0 16 by simpa using hchunk 0]
  unfold IPv6Addr.mk
  repeat rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)]
  exact BitVec.extractLsb'_eq_self

private theorem digitsBetween_toString {n width : Nat} (hbound : n < 10 ^ width)
    (hwidth : 0 < width) :
    IsDigitsBetween 1 width (toString n) := by
  have hdigits :=
    (CedarSupport.String.digits_iff (toString n)).mpr
      (CedarSupport.String.digits_toString n)
  refine ⟨hdigits.1, hdigits.2, ?_⟩
  rw [Nat.toString_eq_repr]
  exact (Nat.length_repr_le_iff hwidth).mpr hbound

private theorem prefixValid_toString (pre : IPv6Prefix) :
    PrefixValid 3 128 (toString pre.toNat) := by
  have hbound : pre.toNat ≤ 128 := by
    cases pre with
    | none =>
        change 128 ≤ 128
        omega
    | some pre =>
        have := BitVec.isLt pre
        change pre.toNat < 2 ^ 7 at this
        change pre.toNat ≤ 128
        omega
  refine ⟨digitsBetween_toString (by omega) (by omega),
    CedarSupport.String.canonical_toString pre.toNat, ?_⟩
  rw [CedarSupport.String.readNat_toString]
  exact hbound

/-- Cedar's canonical IPv6 serializer is accepted and reconstructs the original CIDR. -/
theorem parser_ipNetToStr (i : CedarExamples.IPv6.IPv6Net) :
    CedarExamples.IPv6.ipv6Only (CedarExamples.IPv6.ipNetToStr i) = some i := by
  rcases i with ⟨addr, pre⟩
  let v := addr.toNat
  let h₀ := hex16 ((v >>> 112) &&& 0xffff)
  let h₁ := hex16 ((v >>> 96) &&& 0xffff)
  let h₂ := hex16 ((v >>> 80) &&& 0xffff)
  let h₃ := hex16 ((v >>> 64) &&& 0xffff)
  let h₄ := hex16 ((v >>> 48) &&& 0xffff)
  let h₅ := hex16 ((v >>> 32) &&& 0xffff)
  let h₆ := hex16 ((v >>> 16) &&& 0xffff)
  let h₇ := hex16 (v &&& 0xffff)
  let p := toString pre.toNat
  apply ipv6Only_eq_some_iff.mpr
  refine ⟨.full [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇], some p, ?_, ?_, ?_, ?_⟩
  · have hrender :
        CedarExamples.IPv6.ipNetToStr { addr := addr, pre := pre } =
          s!"{hex16 ((addr.toNat >>> 112) &&& 0xffff)}:\
            {hex16 ((addr.toNat >>> 96) &&& 0xffff)}:\
            {hex16 ((addr.toNat >>> 80) &&& 0xffff)}:\
            {hex16 ((addr.toNat >>> 64) &&& 0xffff)}:\
            {hex16 ((addr.toNat >>> 48) &&& 0xffff)}:\
            {hex16 ((addr.toNat >>> 32) &&& 0xffff)}:\
            {hex16 ((addr.toNat >>> 16) &&& 0xffff)}:\
            {hex16 (addr.toNat &&& 0xffff)}/{pre.toNat}" := by
      rfl
    have stringToString (s : String) : toString s = s := rfl
    simp only [stringToString] at hrender
    simpa [renderNet, AddrComponents.render, renderGroups, v, h₀, h₁, h₂, h₃, h₄, h₅,
      h₆, h₇, p, String.append_assoc] using hrender
  · constructor
    · simp
    · intro part hpart
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpart
      rcases hpart with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hex16_valid _
  · simpa [OptionalPrefixValid, p] using prefixValid_toString pre
  · unfold cidrValue
    rw [CIDR.mk.injEq]
    constructor
    · simpa [AddrComponents.denotation_full, h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇,
        v] using (addrValue_of_addr addr).symm
    · have hp : pre.toNat < 129 := by
        have := (prefixValid_toString pre).2.2
        rw [CedarSupport.String.readNat_toString] at this
        omega
      have hread : readNat p = pre.toNat :=
        CedarSupport.String.readNat_toString pre.toNat
      change pre = ((Fin.ofNat 129 (readNat p)).val : IPv6Prefix)
      rw [hread]
      change pre = ((Fin.ofNat 129 pre.toNat).val : IPv6Prefix)
      rw [Fin.val_ofNat, Nat.mod_eq_of_lt hp]
      exact (prefix_of_toNat pre).symm

theorem parser_rejects_iff (s : String) :
    CedarExamples.IPv6.ipv6Only s = none ↔ ¬IPv6.IsValid s := by
  constructor
  · intro hnone hvalid
    obtain ⟨v, hrender, hview⟩ :=
      (IPv6.GrammarView.isValid_iff_view s).mp hvalid
    have hcompute : IPv6.computeValue s = some v.encodedDenotation := by
      simpa [hrender] using
        IPv6.GrammarView.computeValue_eq_of_view v hview.1
    have hcode := view_encodedDenotation v hview
    have hsome := (parser_agrees s v.denotation).mpr
      ⟨hvalid, by simpa [hcode] using hcompute⟩
    rw [hnone] at hsome
    simp at hsome
  · intro hinvalid
    cases hparse : CedarExamples.IPv6.ipv6Only s with
    | none => rfl
    | some net => exact (hinvalid ((parser_agrees s net).mp hparse).1).elim

end IPv6.RuleRegistrySoundness
