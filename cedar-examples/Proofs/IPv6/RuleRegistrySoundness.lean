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

/-- The external parser returns exactly the values accepted and denoted by the Triptych spec. -/
theorem parser_agrees (s : String) (net : CedarExamples.IPv6.IPv6Net) :
    CedarExamples.IPv6.ipv6Only s = some net ↔
      IPv6.IsValid s ∧ IPv6.computeValue s = some net := by
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
          some (toGrammarView c pre).denotation := by simpa [hrender] using hcompute
      _ = some (cidrValue c pre) :=
        congrArg some (cidrValue_eq_viewDenotation c pre hc hp).symm
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
        IPv6.computeValue s = some v.denotation := by
      simpa [hrender] using
        IPv6.GrammarView.computeValue_eq_of_view v hview.1
    have hdenotation : v.denotation = net :=
      Option.some.inj (hviewCompute.symm.trans hcompute)
    have hcidrValue : cidrValue c v.«prefix» = v.denotation := by
      simpa [hround] using
        cidrValue_eq_viewDenotation c v.«prefix» hext.1 hext.2
    refine ⟨c, v.«prefix», ?_, hext.1, hext.2, ?_⟩
    · calc
        s = v.render := hrender.symm
        _ = (toGrammarView c v.«prefix»).render :=
          congrArg IPv6.GrammarView.View.render hround.symm
        _ = renderNet c v.«prefix» := toGrammarView_render c v.«prefix»
    · exact hdenotation.symm.trans hcidrValue.symm

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
    have hcompute : IPv6.computeValue s = some v.denotation := by
      simpa [hrender] using
        IPv6.GrammarView.computeValue_eq_of_view v hview.1
    have hsome := (parser_agrees s v.denotation).mpr ⟨hvalid, hcompute⟩
    rw [hnone] at hsome
    simp at hsome
  · intro hinvalid
    cases hparse : CedarExamples.IPv6.ipv6Only s with
    | none => rfl
    | some net => exact (hinvalid ((parser_agrees s net).mp hparse).1).elim

end IPv6.RuleRegistrySoundness
