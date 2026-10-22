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

/-! ## Digit and group readers -/

theorem hexDigitValueInt_eq (c : Char) :
    hexDigitValueInt c = (hexDigitValue c : Int) := by
  unfold hexDigitValueInt hexDigitValue
  repeat' split
  all_goals (simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega)

private theorem foldHexInt_cast (cs : List Char) (acc : Nat) :
    cs.foldl (fun a c => a * 16 + (hexDigitValue c : Int)) (acc : Int) =
      ((cs.foldl (fun a c => a * 16 + hexDigitValue c) acc : Nat) : Int) := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.foldl_cons]
      have e : (acc : Int) * 16 + (hexDigitValue c : Int) =
          ((acc * 16 + hexDigitValue c : Nat) : Int) := by omega
      rw [e]
      exact ih _

theorem hexOfChars_eq (cs : List Char) (acc : Nat) :
    hexOfChars cs (acc : Int) =
      ((cs.foldl (fun a c => a * 16 + hexDigitValue c) acc : Nat) : Int) := by
  unfold hexOfChars
  have hfun : (fun a c => a * 16 + hexDigitValueInt c) =
      (fun (a : Int) c => a * 16 + (hexDigitValue c : Int)) := by
    funext a c
    rw [hexDigitValueInt_eq]
  rw [hfun]
  exact foldHexInt_cast cs acc

theorem hexOf_eq_readHex (s : String) : hexOf s = (readHex s : Int) := by
  unfold hexOf readHex readHexChars
  simpa using hexOfChars_eq s.toList 0

/-! ## Colon-separated sequences -/

/-- Base-65536 fold of a list of digit values. -/
def groupFold (values : List Int) (acc : Int) : Int :=
  values.foldl (fun a v => a * 65536 + v) acc

theorem groupFold_acc (values : List Int) (acc : Int) :
    groupFold values acc = acc * 65536 ^ values.length + groupFold values 0 := by
  unfold groupFold
  induction values generalizing acc with
  | nil => simp
  | cons v vs ih =>
      simp only [List.foldl_cons, List.length_cons, Int.zero_mul, Int.zero_add]
      rw [ih (acc * 65536 + v), ih v, Int.pow_succ]
      simp only [Int.add_mul, Int.mul_assoc, Int.add_assoc]
      rw [Int.mul_comm 65536 (65536 ^ vs.length)]

theorem groupFold_append (xs ys : List Int) :
    groupFold (xs ++ ys) 0 = groupFold xs 0 * 65536 ^ ys.length + groupFold ys 0 := by
  unfold groupFold
  rw [List.foldl_append]
  exact groupFold_acc ys _

theorem groupFold_replicate_zero (k : Nat) : groupFold (List.replicate k 0) 0 = 0 := by
  unfold groupFold
  induction k with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ] using ih

private theorem hexSeqOfChars_part (part rest : List Char) (acc cur : Int)
    (h : ∀ c ∈ part, c ≠ ':') :
    hexSeqOfChars (part ++ rest) acc cur =
      hexSeqOfChars rest acc (hexOfChars part cur) := by
  induction part generalizing cur with
  | nil => rfl
  | cons c cs ih =>
      have hc : c ≠ ':' := h c (by simp)
      simp only [List.cons_append, hexSeqOfChars, if_neg hc]
      rw [ih _ (fun x hx => h x (by simp [hx]))]
      rfl

private theorem hexSeqOfChars_intercalate (parts : List (List Char)) (acc : Int)
    (hne : parts ≠ []) (h : ∀ part ∈ parts, ∀ c ∈ part, c ≠ ':') :
    hexSeqOfChars ([':'].intercalate parts) acc 0 =
      groupFold (parts.map (fun part => hexOfChars part 0)) acc := by
  induction parts generalizing acc with
  | nil => exact (hne rfl).elim
  | cons part rest ih =>
      cases rest with
      | nil =>
          simp only [List.intercalate_singleton, List.map_cons, List.map_nil]
          have := hexSeqOfChars_part part [] acc 0 (h part (by simp))
          simp only [List.append_nil] at this
          rw [this]
          rfl
      | cons next tail =>
          rw [List.intercalate_cons_cons]
          rw [List.append_assoc, hexSeqOfChars_part part _ acc 0 (h part (by simp))]
          simp only [List.singleton_append, hexSeqOfChars, if_pos rfl]
          rw [ih _ (by simp) (fun p hp => h p (by simp [hp]))]
          rfl

theorem hexSeqOf_renderGroups (parts : List String)
    (h : ∀ part ∈ parts, ∀ c ∈ part.toList, c ≠ ':') :
    hexSeqOf (IPv6.RuleRegistryProof.renderGroups parts) =
      groupFold (parts.map (fun part => (readHex part : Int))) 0 := by
  cases parts with
  | nil => rfl
  | cons part rest =>
      unfold hexSeqOf IPv6.RuleRegistryProof.renderGroups
      rw [String.toList_intercalate, show ":".toList = [':'] from rfl]
      rw [hexSeqOfChars_intercalate _ 0 (by simp)
        (by
          intro p hp
          simp only [List.mem_map] at hp
          obtain ⟨q, hq, rfl⟩ := hp
          exact h q hq)]
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro q _
      simp only [Function.comp_apply]
      rw [← hexOf_eq_readHex]
      rfl

/-! ## Group counting -/

private def colonCount (cs : List Char) (k : Int) : Int :=
  cs.foldl (fun current c => if c = ':' then current + 1 else current) k

private theorem colonCount_part (part rest : List Char) (k : Int)
    (h : ∀ c ∈ part, c ≠ ':') :
    colonCount (part ++ rest) k = colonCount rest k := by
  unfold colonCount
  rw [List.foldl_append]
  congr 1
  induction part generalizing k with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.foldl_cons, if_neg (h c (by simp))]
      exact ih k (fun x hx => h x (by simp [hx]))

private theorem colonCount_intercalate (parts : List (List Char)) (k : Int)
    (hne : parts ≠ []) (h : ∀ part ∈ parts, ∀ c ∈ part, c ≠ ':') :
    colonCount ([':'].intercalate parts) k = k + (parts.length - 1 : Nat) := by
  induction parts generalizing k with
  | nil => exact (hne rfl).elim
  | cons part rest ih =>
      cases rest with
      | nil =>
          simp only [List.intercalate_singleton, List.length_singleton]
          have := colonCount_part part [] k (h part (by simp))
          simp only [List.append_nil] at this
          rw [this]
          simp [colonCount]
      | cons next tail =>
          rw [List.intercalate_cons_cons, List.append_assoc,
            colonCount_part part _ k (h part (by simp))]
          simp only [List.singleton_append]
          unfold colonCount
          simp only [List.foldl_cons, ↓reduceIte]
          have := ih (k + 1) (by simp) (fun p hp => h p (by simp [hp]))
          unfold colonCount at this
          rw [this]
          simp only [List.length_cons]
          omega

theorem segmentsOf_renderGroups (parts : List String)
    (h : ∀ part ∈ parts, HexValid part) :
    segmentsOf (IPv6.RuleRegistryProof.renderGroups parts) = parts.length := by
  have hcolon : ∀ part ∈ parts, ∀ c ∈ part.toList, c ≠ ':' := by
    intro part hpart c hc heq
    subst c
    have := (h part hpart).1 ':' hc
    simp [TokClass.mem] at this
  cases parts with
  | nil => rfl
  | cons part rest =>
      have hpartNe : part.toList ≠ [] := by
        intro hempty
        have hlen := (h part (by simp)).2.1
        rw [← String.length_toList, hempty] at hlen
        simp at hlen
      unfold segmentsOf IPv6.RuleRegistryProof.renderGroups
      rw [String.toList_intercalate, show ":".toList = [':'] from rfl]
      have hne : ([':'].intercalate ((part :: rest).map String.toList)).isEmpty = false := by
        cases rest with
        | nil =>
            simpa [List.isEmpty_iff] using hpartNe
        | cons next tail =>
            rw [List.map_cons, List.map_cons, List.intercalate_cons_cons]
            simp
      rw [if_neg (by simp only [hne]; decide)]
      have := colonCount_intercalate ((part :: rest).map String.toList) 1 (by simp)
        (by
          intro p hp
          simp only [List.mem_map] at hp
          obtain ⟨q, hq, rfl⟩ := hp
          exact hcolon q hq)
      unfold colonCount at this
      rw [this]
      simp only [List.length_map, List.length_cons]
      omega

/-! ## Cedar's 128-bit address -/

theorem toNat_ipv6mk (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : BitVec 16) :
    ((IPv6Addr.mk a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇).toNat : Int) =
      groupFold [a₀.toNat, a₁.toNat, a₂.toNat, a₃.toNat, a₄.toNat, a₅.toNat, a₆.toNat,
        a₇.toNat] 0 := by
  unfold IPv6Addr.mk
  simp only [BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₇)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₆)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₅)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₄)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₃)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₂)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₁)]
  simp only [Nat.shiftLeft_eq, groupFold, List.foldl_cons, List.foldl_nil]
  omega

theorem addrOfValues_toNat (groups : List (BitVec 16)) (h : groups.length = 8) :
    ((AddrComponents.addrOfValues groups).toNat : Int) =
      groupFold (groups.map fun g => (g.toNat : Int)) 0 := by
  match groups, h with
  | [a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇], _ =>
      unfold AddrComponents.addrOfValues
      simp only [List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]
      exact toNat_ipv6mk a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇

theorem groupValues_toNat (parts : List String) (h : ∀ part ∈ parts, HexValid part) :
    (groupValues parts).map (fun g => (g.toNat : Int)) =
      parts.map (fun part => (readHex part : Int)) := by
  unfold groupValues
  rw [List.map_map]
  apply List.map_congr_left
  intro part hpart
  simp only [Function.comp_apply, BitVec.toNat_ofNat]
  have := readHex_le (h part hpart)
  rw [Nat.mod_eq_of_lt (by omega)]

/-! ## Prefix -/

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

private theorem prefix_toNat_le (pre : IPv6Prefix) : pre.toNat ≤ 128 := by
  cases pre with
  | none => exact Nat.le_refl 128
  | some pre =>
      have := BitVec.isLt pre
      change pre.toNat < 2 ^ 7 at this
      change pre.toNat ≤ 128
      omega

private theorem toNat_ofNat_prefix {n : Nat} (h : n ≤ 128) :
    (n : IPv6Prefix).toNat = n := by
  change (if n < 128 then some (BitVec.ofNat 7 n) else none : IPv6Prefix).toNat = n
  by_cases hlt : n < 128
  · rw [if_pos hlt]
    change (BitVec.ofNat 7 n).toNat = n
    simp only [BitVec.toNat_ofNat]
    omega
  · rw [if_neg hlt]
    change 128 = n
    omega

theorem prefixValue_toNat (pre : Option String) (hp : OptionalPrefixValid pre) :
    ((prefixValue pre).toNat : Int) =
      if pre.getD "" = "" then 128 else natOf (pre.getD "") := by
  cases pre with
  | none => rfl
  | some p =>
      change PrefixValid 3 128 p at hp
      have hbound : readNat p ≤ 128 := hp.2.2
      have hne : p ≠ "" := by
        intro hempty
        have hlength := hp.1.2.1
        simp [hempty] at hlength
      simp only [Option.getD_some, if_neg hne]
      change (((readNat p % 129 : Nat) : IPv6Prefix).toNat : Int) = _
      rw [Nat.mod_eq_of_lt (by omega), toNat_ofNat_prefix hbound]
      rfl

/-! ## Address and CIDR codes -/

private theorem colonFree {parts : List String} (h : ∀ part ∈ parts, HexValid part) :
    ∀ part ∈ parts, ∀ c ∈ part.toList, c ≠ ':' := by
  intro part hpart c hc heq
  subst c
  have := (h part hpart).1 ':' hc
  simp [TokClass.mem] at this

theorem fullDenotation_toNat {parts : List String}
    (hc : (AddrComponents.full parts).Valid) :
    (((AddrComponents.full parts).denotation).toNat : Int) =
      hexSeqOf (IPv6.RuleRegistryProof.renderGroups parts) := by
  obtain ⟨hlen, hparts⟩ := hc
  rw [AddrComponents.denotation_full,
    addrOfValues_toNat _ (by simpa [groupValues] using hlen),
    groupValues_toNat parts hparts, hexSeqOf_renderGroups parts (colonFree hparts)]

theorem compressedDenotation_toNat {left right : List String}
    (hc : (AddrComponents.compressed left right).Valid) :
    (((AddrComponents.compressed left right).denotation).toNat : Int) =
      hexSeqOf (IPv6.RuleRegistryProof.renderGroups left) *
          65536 ^ ((8 : Int) - segmentsOf (IPv6.RuleRegistryProof.renderGroups left)).toNat +
        hexSeqOf (IPv6.RuleRegistryProof.renderGroups right) := by
  obtain ⟨hcount, hleft, hright⟩ := hc
  rw [AddrComponents.denotation_compressed,
    addrOfValues_toNat _ (by simp [groupValues]; omega)]
  have hzero : ((0 : BitVec 16).toNat : Int) = 0 := rfl
  simp only [List.map_append, List.map_replicate, hzero]
  rw [groupFold_append, groupFold_append, groupFold_replicate_zero,
    groupValues_toNat left hleft, groupValues_toNat right hright,
    ← hexSeqOf_renderGroups left (colonFree hleft),
    ← hexSeqOf_renderGroups right (colonFree hright),
    segmentsOf_renderGroups left hleft]
  simp only [List.length_replicate, List.length_map]
  have hexp : ((8 : Int) - (left.length : Int)).toNat =
      (8 - (left.length + right.length)) + right.length := by omega
  rw [hexp, Int.pow_add, Int.add_zero, Int.mul_assoc]

theorem ipv6CodeToNet_ipv6NetToCode (c : CIDR V6_WIDTH) :
    CedarExamples.IPv6.ipv6CodeToNet (CedarExamples.IPv6.ipv6NetToCode c) = c := by
  rcases c with ⟨addr, pre⟩
  have hpre := prefix_toNat_le pre
  unfold CedarExamples.IPv6.ipv6CodeToNet CedarExamples.IPv6.ipv6NetToCode
  have hcode :
      ((addr.toNat : Int) * 129 + (pre.toNat : Int)).toNat = addr.toNat * 129 + pre.toNat := by
    omega
  simp only [hcode]
  rw [CIDR.mk.injEq]
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    have hlt := BitVec.isLt addr
    rw [show (addr.toNat * 129 + pre.toNat) / 129 = addr.toNat by omega]
    exact Nat.mod_eq_of_lt hlt
  · rw [show (addr.toNat * 129 + pre.toNat) % 129 = pre.toNat by omega]
    exact prefix_of_toNat pre

theorem ipv6NetToCode_bounds (c : CIDR V6_WIDTH) :
    0 ≤ CedarExamples.IPv6.ipv6NetToCode c ∧
      CedarExamples.IPv6.ipv6NetToCode c ≤ (2 : Int) ^ ((128 : Int)).toNat * 129 - 1 := by
  have hpre := prefix_toNat_le c.pre
  have haddr := BitVec.isLt c.addr
  unfold CedarExamples.IPv6.ipv6NetToCode
  have hpow : (2 : Int) ^ ((128 : Int)).toNat = ((2 ^ 128 : Nat) : Int) := by
    simp
  rw [hpow]
  change c.addr.toNat < 2 ^ 128 at haddr
  omega

/-! ## Validity and value bridge -/

private theorem valueConstraints_iff (v : IPv6.GrammarView.View) :
    v.ValueConstraints ↔
      0 ≤ v.denotation ∧ v.denotation ≤ (2 : Int) ^ ((128 : Int)).toNat * 129 - 1 := by
  cases v with
  | mk addr pre => cases addr <;> rfl

/-- The DSL value of a valid IPv6 view is the integer code of the CIDR Cedar's parser
    returns. -/
theorem code_cidrValue (c : AddrComponents) (pre : Option String)
    (hc : c.Valid) (hp : OptionalPrefixValid pre) :
    CedarExamples.IPv6.ipv6NetToCode (cidrValue c pre) = (toGrammarView c pre).denotation := by
  unfold CedarExamples.IPv6.ipv6NetToCode
  rw [show (cidrValue c pre).pre = prefixValue pre from rfl, prefixValue_toNat pre hp]
  cases c with
  | full parts =>
      rw [show (cidrValue (.full parts) pre).addr = (AddrComponents.full parts).denotation
          from rfl, fullDenotation_toNat hc]
      have hne : IPv6.RuleRegistryProof.renderGroups parts ≠ "" := by
        intro hempty
        have hcount := segmentsOf_renderGroups parts hc.2
        rw [hempty, hc.1] at hcount
        simp [segmentsOf] at hcount
      simp only [toGrammarView, toGrammarAddr, IPv6.GrammarView.View.denotation, IPv6.value]
      rw [if_neg (show IPv6.GrammarView.renderGroups parts ≠ "" from hne)]
      rfl
  | compressed left right =>
      rw [show (cidrValue (.compressed left right) pre).addr =
          (AddrComponents.compressed left right).denotation from rfl,
        compressedDenotation_toNat hc]
      simp only [toGrammarView, toGrammarAddr, IPv6.GrammarView.View.denotation, IPv6.value]
      rfl

private theorem prefixConstraints_iff (pre : Option String) :
    IPv6.GrammarView.OptionalPrefixConstraints pre ↔
      ((pre.getD "").startsWith "0" → pre.getD "" = "0") ∧
        0 ≤ natOf (pre.getD "") ∧ natOf (pre.getD "") ≤ 128 := by
  cases pre with
  | none =>
      simp [IPv6.GrammarView.OptionalPrefixConstraints, natOf]
  | some p =>
      simp only [IPv6.GrammarView.OptionalPrefixConstraints,
        IPv6.GrammarView.PrefixConstraints, Option.getD_some]
      constructor
      · rintro ⟨hcanonical, hbound⟩
        exact ⟨hcanonical, by simp [natOf], hbound⟩
      · rintro ⟨hcanonical, _, hbound⟩
        exact ⟨hcanonical, hbound⟩

theorem viewValid_iff (c : AddrComponents) (pre : Option String) :
    c.Valid ∧ OptionalPrefixValid pre ↔ (toGrammarView c pre).Valid := by
  constructor
  · rintro ⟨hc, hp⟩
    have haddr := (addrValid_iff c).mp hc
    have hpre := (optionalPrefixValid_iff pre).mp hp
    refine ⟨⟨haddr.1, hpre.1⟩, ?_, ?_⟩
    · have hprefix := (prefixConstraints_iff pre).mp hpre.2
      cases c with
      | full parts =>
          exact ⟨⟨by simp [segmentsOf], hprefix.1⟩, hprefix.2⟩
      | compressed left right =>
          obtain ⟨hcount, hleft, hright⟩ := hc
          refine ⟨⟨?_, hprefix.1⟩, hprefix.2⟩
          change segmentsOf (IPv6.RuleRegistryProof.renderGroups left) +
            segmentsOf (IPv6.RuleRegistryProof.renderGroups right) < 8
          rw [segmentsOf_renderGroups left hleft, segmentsOf_renderGroups right hright]
          omega
    · rw [valueConstraints_iff, ← code_cidrValue c pre hc hp]
      exact ipv6NetToCode_bounds (cidrValue c pre)
  · rintro ⟨⟨haddrSyntax, hpreSyntax⟩, hconstraints, _⟩
    have hprefix : IPv6.GrammarView.OptionalPrefixConstraints pre := by
      apply (prefixConstraints_iff pre).mpr
      cases c <;> exact ⟨hconstraints.1.2, hconstraints.2⟩
    refine ⟨(addrValid_iff c).mpr ⟨haddrSyntax, ?_⟩,
      (optionalPrefixValid_iff pre).mpr ⟨hpreSyntax, hprefix⟩⟩
    cases c with
    | full parts => trivial
    | compressed left right =>
        obtain ⟨_, _, hleft, hright⟩ := haddrSyntax
        have hcount := hconstraints.1.1
        change segmentsOf (IPv6.RuleRegistryProof.renderGroups left) +
          segmentsOf (IPv6.RuleRegistryProof.renderGroups right) < 8 at hcount
        rw [segmentsOf_renderGroups left hleft, segmentsOf_renderGroups right hright]
          at hcount
        change left.length + right.length < 8
        omega

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
          some (toGrammarView c pre).denotation := by simpa [hrender] using hcompute
      _ = some (CedarExamples.IPv6.ipv6NetToCode (cidrValue c pre)) :=
        congrArg some (code_cidrValue c pre hc hp).symm
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
    have hdenotation : v.denotation = CedarExamples.IPv6.ipv6NetToCode net :=
      Option.some.inj (hviewCompute.symm.trans hcompute)
    have hcode :
        CedarExamples.IPv6.ipv6NetToCode (cidrValue c v.«prefix») = v.denotation := by
      simpa [hround] using code_cidrValue c v.«prefix» hext.1 hext.2
    have hcidrValue : cidrValue c v.«prefix» = net := by
      simpa only [ipv6CodeToNet_ipv6NetToCode] using
        congrArg CedarExamples.IPv6.ipv6CodeToNet (hcode.trans hdenotation)
    refine ⟨c, v.«prefix», ?_, hext.1, hext.2, ?_⟩
    · calc
        s = v.render := hrender.symm
        _ = (toGrammarView c v.«prefix»).render :=
          congrArg IPv6.GrammarView.View.render hround.symm
        _ = renderNet c v.«prefix» := toGrammarView_render c v.«prefix»
    · exact hcidrValue.symm

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
    Triptych.hexDigitValue n.digitChar = n := by
  have hn :
      n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
      n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by
    omega
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem readHex_hex16 (n : Nat) :
    Triptych.readHex (hex16 n) = n % 0x10000 := by
  have h₀ : (n % 0x10000) / 0x1000 < 16 := by omega
  have h₁ : (n % 0x1000) / 0x100 < 16 := by omega
  have h₂ : (n % 0x100) / 0x10 < 16 := by omega
  have h₃ : (n % 0x10) / 0x1 < 16 := by omega
  unfold Triptych.readHex Triptych.readHexChars hex16 hexDigitRepr
  simp only [String.toList_append, String.toList_singleton, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
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
          (Triptych.readHex
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
      (Triptych.readHex (hex16 (addr.toNat &&& 0xffff))) =
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
    have hcompute : IPv6.computeValue s = some v.denotation := by
      simpa [hrender] using
        IPv6.GrammarView.computeValue_eq_of_view v hview.1
    let c := ofGrammarAddr v.addr
    have hround : toGrammarView c v.«prefix» = v := by
      cases v with
      | mk addr pre => cases addr <;> rfl
    have hext : c.Valid ∧ OptionalPrefixValid v.«prefix» :=
      (viewValid_iff c v.«prefix»).mpr (by simpa [hround] using hview)
    have hcode :
        CedarExamples.IPv6.ipv6NetToCode (cidrValue c v.«prefix») = v.denotation := by
      simpa [hround] using code_cidrValue c v.«prefix» hext.1 hext.2
    rw [← hcode] at hcompute
    have hsome := (parser_agrees s _).mpr ⟨hvalid, hcompute⟩
    rw [hnone] at hsome
    simp at hsome
  · intro hinvalid
    cases hparse : CedarExamples.IPv6.ipv6Only s with
    | none => rfl
    | some net => exact (hinvalid ((parser_agrees s net).mp hparse).1).elim

end IPv6.RuleRegistrySoundness
