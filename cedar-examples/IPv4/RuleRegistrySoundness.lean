import IPv4.RuleRegistryProof
import IPv4.CedarBridge

/-!
# End-to-end IPv4 soundness via registered parser summaries

The executable side comes entirely from `RuleRegistryProof`. This file uses only the
grammar-side component facts from `CedarBridge`; it does not use that module's parser agreement
or rejection theorems, nor Cedar's unfinished `Cedar.Thm.Ext.IPAddr` theorem layer.
-/

open Cedar.Spec.Ext.IPAddr
open Triptych

namespace IPv4.RuleRegistrySoundness

open IPv4.RuleRegistryProof

private theorem octetValid_iff {s : String} :
    OctetValid s ↔ IPv4.CedarBridge.OctetWf s := by
  unfold OctetValid IPv4.CedarBridge.OctetWf IPv4.CedarBridge.OctetConstraints
  constructor
  · rintro ⟨hsyntax, hcanonical, hbound⟩
    refine ⟨hsyntax, hcanonical, ?_⟩
    change (readNat s : Int) ≤ 255
    omega
  · rintro ⟨hsyntax, hcanonical, hbound⟩
    refine ⟨hsyntax, hcanonical, ?_⟩
    change (readNat s : Int) ≤ 255 at hbound
    omega

private theorem prefixValid_iff {s : String} :
    PrefixValid 2 32 s ↔ IPv4.CedarBridge.PrefixWf 2 32 s := by
  unfold PrefixValid IPv4.CedarBridge.PrefixWf IPv4.CedarBridge.PrefixConstraints
  constructor
  · rintro ⟨hsyntax, hcanonical, hbound⟩
    refine ⟨hsyntax, hcanonical, ?_⟩
    change (readNat s : Int) ≤ 32
    omega
  · rintro ⟨hsyntax, hcanonical, hbound⟩
    refine ⟨hsyntax, hcanonical, ?_⟩
    change (readNat s : Int) ≤ 32 at hbound
    omega

private theorem optionalPrefixValid_iff (pre : Option String) :
    OptionalPrefixValid pre ↔ IPv4.CedarBridge.OptionalPrefixWf pre := by
  cases pre with
  | none => simp [OptionalPrefixValid, IPv4.CedarBridge.OptionalPrefixWf]
  | some pre =>
      simpa [OptionalPrefixValid, IPv4.CedarBridge.OptionalPrefixWf] using
        (prefixValid_iff (s := pre))

private theorem renderNet_eq_renderV4 (o₁ o₂ o₃ o₄ : String) (pre : Option String) :
    renderNet o₁ o₂ o₃ o₄ pre = IPv4.CedarBridge.renderV4 o₁ o₂ o₃ o₄ pre := by
  rfl

private theorem toNat_mk (a₀ a₁ a₂ a₃ : BitVec 8) :
    (IPv4Addr.mk a₀ a₁ a₂ a₃).toNat =
      ((a₀.toNat * 256 + a₁.toNat) * 256 + a₂.toNat) * 256 + a₃.toNat := by
  unfold IPv4Addr.mk
  simp only [BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₃)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₂)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₁)]
  simp [Nat.shiftLeft_eq]

private theorem addrValue_of_addr (addr : IPv4Addr) :
    let v := addr.toNat
    addrValue
        (toString ((v >>> 24) &&& 0xff))
        (toString ((v >>> 16) &&& 0xff))
        (toString ((v >>> 8) &&& 0xff))
        (toString (v &&& 0xff)) =
      addr := by
  dsimp only
  unfold addrValue
  repeat rw [CedarSupport.String.readNat_toString]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_mk]
  simp only [BitVec.toNat_ofNat]
  have hmask : (0xff : Nat) = 2 ^ 8 - 1 := by decide
  simp only [hmask, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have hbound := BitVec.isLt addr
  change addr.toNat < 2 ^ 32 at hbound
  omega

private theorem digitsBetween_toString {n width : Nat} (hbound : n < 10 ^ width)
    (hwidth : 0 < width) :
    IsDigitsBetween 1 width (toString n) := by
  have hdigits :=
    (CedarSupport.String.digits_iff (toString n)).mpr
      (CedarSupport.String.digits_toString n)
  refine ⟨hdigits.1, hdigits.2, ?_⟩
  rw [Nat.toString_eq_repr]
  exact (Nat.length_repr_le_iff hwidth).mpr hbound

private theorem octetValid_toString {n : Nat} (hbound : n ≤ 255) :
    OctetValid (toString n) := by
  refine ⟨digitsBetween_toString (by omega) (by omega),
    CedarSupport.String.canonical_toString n, ?_⟩
  rw [CedarSupport.String.readNat_toString]
  exact hbound

private theorem prefixValid_toString (pre : IPv4Prefix) :
    PrefixValid 2 32 (toString pre.toNat) := by
  have hbound : pre.toNat ≤ 32 := by
    cases pre with
    | none =>
        change 32 ≤ 32
        omega
    | some pre =>
        have := BitVec.isLt pre
        change pre.toNat < 2 ^ 5 at this
        change pre.toNat ≤ 32
        omega
  refine ⟨digitsBetween_toString (by omega) (by omega),
    CedarSupport.String.canonical_toString pre.toNat, ?_⟩
  rw [CedarSupport.String.readNat_toString]
  exact hbound

private theorem prefix_of_toNat (pre : IPv4Prefix) :
    (pre.toNat : IPv4Prefix) = pre := by
  cases pre with
  | none => rfl
  | some pre =>
      have hbound := BitVec.isLt pre
      change pre.toNat < 2 ^ 5 at hbound
      change (if pre.toNat < 32 then some (BitVec.ofNat 5 pre.toNat) else none) = some pre
      rw [if_pos (by omega)]
      congr
      apply BitVec.eq_of_toNat_eq
      simp

private theorem mask255_le (n : Nat) : n &&& 0xff ≤ 255 := by
  have h := Nat.and_lt_two_pow n (n := 8) (y := 0xff) (by decide)
  omega

/-- The external parser returns exactly the values accepted and denoted by the Triptych spec. -/
theorem parser_agrees (s : String) (cidr : CIDR V4_WIDTH) :
    CedarExamples.IPv4.ipv4Only s = some cidr ↔
      IPv4.IsValid s ∧ IPv4.computeValue s = some cidr := by
  rw [ipv4Only_eq_some_iff]
  constructor
  · rintro ⟨o₁, o₂, o₃, o₄, pre, hs, h₁, h₂, h₃, h₄, hp, hcidr⟩
    have hb₁ := octetValid_iff.mp h₁
    have hb₂ := octetValid_iff.mp h₂
    have hb₃ := octetValid_iff.mp h₃
    have hb₄ := octetValid_iff.mp h₄
    have hbp := optionalPrefixValid_iff pre |>.mp hp
    have hs' : s = IPv4.CedarBridge.renderV4 o₁ o₂ o₃ o₄ pre := by
      simpa only [renderNet_eq_renderV4] using hs
    have hvalid : IPv4.IsValid s :=
      (IPv4.CedarBridge.isValid_iff_parts s).mpr
        ⟨o₁, o₂, o₃, o₄, pre, hs', hb₁, hb₂, hb₃, hb₄, hbp⟩
    have hvalue :=
      IPv4.CedarBridge.computeValue_eq_of_parts hs' hb₁ hb₂ hb₃ hb₄ hbp
    have hdenote := cidrValue_eq_toIPv4Net (o₁ := o₁) (o₂ := o₂) (o₃ := o₃)
      (o₄ := o₄) hp
    refine ⟨hvalid, ?_⟩
    calc
      IPv4.computeValue s =
          some (CedarExamples.IPv4.toIPv4Net o₁ o₂ o₃ o₄ (pre.getD "")) := hvalue
      _ = some cidr := congrArg some (hdenote.symm.trans hcidr.symm)
  · rintro ⟨hvalid, hvalue⟩
    obtain ⟨o₁, o₂, o₃, o₄, pre, hs, hb₁, hb₂, hb₃, hb₄, hbp⟩ :=
      (IPv4.CedarBridge.isValid_iff_parts s).mp hvalid
    have h₁ := octetValid_iff.mpr hb₁
    have h₂ := octetValid_iff.mpr hb₂
    have h₃ := octetValid_iff.mpr hb₃
    have h₄ := octetValid_iff.mpr hb₄
    have hp := optionalPrefixValid_iff pre |>.mpr hbp
    have hformat :=
      IPv4.CedarBridge.computeValue_eq_of_parts hs hb₁ hb₂ hb₃ hb₄ hbp
    rw [hvalue] at hformat
    have hcidr :
        cidr = CedarExamples.IPv4.toIPv4Net o₁ o₂ o₃ o₄ (pre.getD "") :=
      Option.some.inj hformat
    have hdenote := cidrValue_eq_toIPv4Net (o₁ := o₁) (o₂ := o₂) (o₃ := o₃)
      (o₄ := o₄) hp
    exact ⟨o₁, o₂, o₃, o₄, pre, by simpa only [renderNet_eq_renderV4] using hs,
      h₁, h₂, h₃, h₄, hp, hcidr.trans hdenote.symm⟩

/-- Cedar's canonical IPv4 serializer is accepted and reconstructs the original CIDR. -/
theorem parser_ipNetToStr (i : CIDR V4_WIDTH) :
    CedarExamples.IPv4.ipv4Only (CedarExamples.IPv4.ipNetToStr i) = some i := by
  rcases i with ⟨addr, pre⟩
  let v := addr.toNat
  let o₁ := toString ((v >>> 24) &&& 0xff)
  let o₂ := toString ((v >>> 16) &&& 0xff)
  let o₃ := toString ((v >>> 8) &&& 0xff)
  let o₄ := toString (v &&& 0xff)
  let p := toString pre.toNat
  apply ipv4Only_eq_some_iff.mpr
  refine ⟨o₁, o₂, o₃, o₄, some p, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hrender :
        CedarExamples.IPv4.ipNetToStr { addr := addr, pre := pre } =
          s!"{(addr.toNat >>> 24) &&& 0xff}.{(addr.toNat >>> 16) &&& 0xff}.\
            {(addr.toNat >>> 8) &&& 0xff}.{addr.toNat &&& 0xff}/{pre.toNat}" := by
      rfl
    have hdot : toString "." = "." := rfl
    have hslash : toString "/" = "/" := rfl
    simpa [renderNet, renderAddr, v, o₁, o₂, o₃, o₄, p, hdot, hslash,
      String.append_assoc] using hrender
  · exact octetValid_toString (mask255_le _)
  · exact octetValid_toString (mask255_le _)
  · exact octetValid_toString (mask255_le _)
  · exact octetValid_toString (mask255_le _)
  · simpa [OptionalPrefixValid, p] using prefixValid_toString pre
  · unfold cidrValue
    rw [CIDR.mk.injEq]
    constructor
    · simpa [o₁, o₂, o₃, o₄, v] using (addrValue_of_addr addr).symm
    · have hp : pre.toNat < 33 := by
        have := (prefixValid_toString pre).2.2
        rw [CedarSupport.String.readNat_toString] at this
        omega
      have hread : readNat p = pre.toNat :=
        CedarSupport.String.readNat_toString pre.toNat
      change pre = ((Fin.ofNat 33 (readNat p)).val : IPv4Prefix)
      rw [hread]
      change pre = ((Fin.ofNat 33 pre.toNat).val : IPv4Prefix)
      rw [Fin.val_ofNat, Nat.mod_eq_of_lt hp]
      exact (prefix_of_toNat pre).symm

theorem parser_rejects_iff (s : String) :
    CedarExamples.IPv4.ipv4Only s = none ↔ ¬IPv4.IsValid s := by
  constructor
  · intro hnone hvalid
    obtain ⟨o₁, o₂, o₃, o₄, pre, hs, h₁, h₂, h₃, h₄, hp⟩ :=
      (IPv4.CedarBridge.isValid_iff_parts s).mp hvalid
    have hvalue :=
      IPv4.CedarBridge.computeValue_eq_of_parts hs h₁ h₂ h₃ h₄ hp
    have hsome := (parser_agrees s _).mpr ⟨hvalid, hvalue⟩
    rw [hnone] at hsome
    simp at hsome
  · intro hinvalid
    cases hparse : CedarExamples.IPv4.ipv4Only s with
    | none => rfl
    | some cidr => exact (hinvalid ((parser_agrees s cidr).mp hparse).1).elim

end IPv4.RuleRegistrySoundness
