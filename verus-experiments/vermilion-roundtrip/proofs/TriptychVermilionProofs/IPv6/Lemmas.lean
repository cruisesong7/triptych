import TriptychVermilionGenerated.IPv6
import Proofs.IPv6.GrammarView
import Triptych.Backend.Verus.AstSemantics

namespace Triptych.Vermilion.Proofs.IPv6

open Triptych
open Triptych.Vermilion.String
open Triptych.Vermilion.Generated.IPv6
open IPv6.GrammarView

theorem hexDigits_between_equiv
    (lower upper : Nat) (source : String) :
    IsHexDigitsBetween lower upper source ↔
      ∃ digits : Vermilion.Seq Int,
        encodeString source = digits ∧
          ((Int.ofNat lower ≤ Vermilion.Seq.len digits ∧
              Vermilion.Seq.len digits ≤ Int.ofNat upper) ∧
            ∀ index : Int,
              0 ≤ index ∧ index < Vermilion.Seq.len digits →
                triptych_ipv6_roundtrip.triptych_is_hex_digit
                  (Vermilion.Seq.index digits index)) := by
  simpa [triptych_ipv6_roundtrip.triptych_is_hex_digit,
    triptych_ipv6_roundtrip.triptych_is_digit, IsHexDigitCode,
    IsDigitCode, or_comm, or_left_comm, or_assoc] using
      hexDigitsBetween_iff_encoded lower upper source

theorem digits_between_equiv
    (lower upper : Nat) (source : String) :
    IsDigitsBetween lower upper source ↔
      ∃ digits : Vermilion.Seq Int,
        encodeString source = digits ∧
          ((Int.ofNat lower ≤ Vermilion.Seq.len digits ∧
              Vermilion.Seq.len digits ≤ Int.ofNat upper) ∧
            ∀ index : Int,
              0 ≤ index ∧ index < Vermilion.Seq.len digits →
                triptych_ipv6_roundtrip.triptych_is_digit
                  (Vermilion.Seq.index digits index)) := by
  simpa [triptych_ipv6_roundtrip.triptych_is_digit, IsDigitCode] using
    digitsBetween_iff_encoded lower upper source

theorem h16_equiv (source : String) :
    IPv6.IsWf.H16 source ↔
      triptych_ipv6_roundtrip.ipv6_is_wf_H16 (encodeString source) := by
  simpa [IPv6.IsWf.H16, triptych_ipv6_roundtrip.ipv6_is_wf_H16] using
    hexDigits_between_equiv 1 4 source

theorem h16L_equiv (source : String) :
    IPv6.IsWf.H16L source ↔
      triptych_ipv6_roundtrip.ipv6_is_wf_H16L (encodeString source) := by
  simpa [IPv6.IsWf.H16L, triptych_ipv6_roundtrip.ipv6_is_wf_H16L] using
    hexDigits_between_equiv 1 4 source

theorem h16R_equiv (source : String) :
    IPv6.IsWf.H16R source ↔
      triptych_ipv6_roundtrip.ipv6_is_wf_H16R (encodeString source) := by
  simpa [IPv6.IsWf.H16R, triptych_ipv6_roundtrip.ipv6_is_wf_H16R] using
    hexDigits_between_equiv 1 4 source

theorem prefix_equiv (source : String) :
    IPv6.IsWf.Prefix source ↔
      triptych_ipv6_roundtrip.ipv6_is_wf_Prefix (encodeString source) := by
  simpa [IPv6.IsWf.Prefix, triptych_ipv6_roundtrip.ipv6_is_wf_Prefix] using
    digits_between_equiv 1 3 source

def CodeRepValid
    (itemValid : Vermilion.Seq Int → Prop)
    (lower upper : Int) (input : Vermilion.Seq Int) (already : Int) : Prop :=
  ∃ parts : List (Vermilion.Seq Int),
    parts ≠ [] ∧
      lower ≤ already + Int.ofNat parts.length ∧
      already + Int.ofNat parts.length ≤ upper ∧
      (∀ part ∈ parts, itemValid part) ∧
      input = [58].intercalate parts

def RepStep
    (matcher : Vermilion.Seq Int → Int → Prop)
    (itemValid : Vermilion.Seq Int → Prop)
    (lower upper : Int) (input : Vermilion.Seq Int) (already : Int) : Prop :=
  ∃ split : Int,
    0 ≤ split ∧
      split ≤ input.len ∧
      itemValid (input.subrange 0 split) ∧
      ((lower ≤ already + 1 ∧ already + 1 ≤ upper ∧ split = input.len) ∨
        (already + 1 < upper ∧
          split + 1 ≤ input.len ∧
          input.subrange split (split + 1) = [58] ∧
          matcher (input.subrange (split + 1) input.len) (already + 1)))

theorem guarded_iff_and (condition consequence : Prop)
    [Decidable condition] :
    (if condition then consequence else False) ↔
      condition ∧ consequence := by
  by_cases condition <;> simp_all

theorem guardedDite_iff_and (condition consequence : Prop)
    [Decidable condition] :
    (dite condition (fun _ => consequence) (fun _ => False)) ↔
      condition ∧ consequence := by
  by_cases condition <;> simp_all

theorem repMatcher_iff_codeRep
    (matcher : Vermilion.Seq Int → Int → Prop)
    (itemValid : Vermilion.Seq Int → Prop)
    (lower upper : Int)
    (equation :
      ∀ input already,
        matcher input already ↔
          RepStep matcher itemValid lower upper input already)
    (input : Vermilion.Seq Int) (already : Int) :
    matcher input already ↔
      CodeRepValid itemValid lower upper input already := by
  rw [equation]
  constructor
  · rintro ⟨split, hsplit, hsplitBound, hitem, hstop | hcontinue⟩
    · rcases hstop with ⟨hlower, hupper, hfinish⟩
      have hwhole : input.subrange 0 split = input := by
        rw [hfinish]
        simp [Vermilion.Seq.subrange, Vermilion.Seq.len]
      refine ⟨[input], by simp, ?_, ?_, ?_, by simp⟩
      · simpa using hlower
      · simpa using hupper
      · intro part hpart
        simp only [List.mem_singleton] at hpart
        subst part
        simpa [hwhole] using hitem
    · rcases hcontinue with
        ⟨hbelow, hseparatorBound, hseparator, hrecursive⟩
      have htail :=
        (repMatcher_iff_codeRep matcher itemValid lower upper equation
          (input.subrange (split + 1) input.len) (already + 1)).1
          hrecursive
      rcases htail with
        ⟨parts, hparts, hlower, hupper, hitems, hrender⟩
      let first := input.subrange 0 split
      have hlength :
          Int.ofNat (first :: parts).length =
            Int.ofNat parts.length + 1 := by simp
      refine ⟨first :: parts, by simp, ?_, ?_, ?_, ?_⟩
      · rw [hlength]
        omega
      · rw [hlength]
        omega
      · intro part hpart
        simp only [List.mem_cons] at hpart
        rcases hpart with rfl | hpart
        · exact hitem
        · exact hitems part hpart
      · have hdecompose :=
          subrange_three_way input split hsplit hseparatorBound
        rw [hseparator, hrender] at hdecompose
        rw [intercalate_cons_of_ne_nil [58] first parts hparts]
        exact hdecompose
  · rintro ⟨parts, hparts, hlower, hupper, hitems, hrender⟩
    cases parts with
    | nil => exact absurd rfl hparts
    | cons first rest =>
        by_cases hrest : rest = []
        · subst rest
          norm_num at hlower hupper
          simp only [List.intercalate, List.append_nil] at hrender
          subst input
          refine ⟨Int.ofNat first.length, Int.ofNat_nonneg _, ?_, ?_,
            Or.inl ⟨hlower, hupper, ?_⟩⟩
          · simp [Vermilion.Seq.len]
          · simpa [Vermilion.Seq.subrange, Vermilion.Seq.len] using
              hitems first (by simp)
          · simp [Vermilion.Seq.len]
        · rw [intercalate_cons_of_ne_nil [58] first rest hrest] at hrender
          subst input
          let suffix := [58].intercalate rest
          have htail :
              CodeRepValid itemValid lower upper suffix (already + 1) := by
            refine ⟨rest, hrest, ?_, ?_, ?_, rfl⟩
            · have hlength :
                  Int.ofNat (first :: rest).length =
                    Int.ofNat rest.length + 1 := by simp
              rw [hlength] at hlower
              omega
            · have hlength :
                  Int.ofNat (first :: rest).length =
                    Int.ofNat rest.length + 1 := by simp
              rw [hlength] at hupper
              omega
            · intro part hpart
              exact hitems part (by simp [hpart])
          have hrecursive :=
            (repMatcher_iff_codeRep matcher itemValid lower upper equation
              suffix (already + 1)).2 htail
          refine ⟨Int.ofNat first.length, Int.ofNat_nonneg _, ?_, ?_,
            Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
          · simp [Vermilion.Seq.len, suffix, List.append_assoc]
            omega
          · simpa [Vermilion.Seq.subrange, Vermilion.Seq.len, suffix,
              List.append_assoc] using hitems first (by simp)
          · have hlength :
                Int.ofNat (first :: rest).length =
                  Int.ofNat rest.length + 1 := by simp
            rw [hlength] at hupper
            have hrestLength : 1 ≤ rest.length := by
              cases rest with
              | nil => exact absurd rfl hrest
              | cons _ _ => simp
            have hrestLengthInt : (1 : Int) ≤ Int.ofNat rest.length :=
              (Int.ofNat_le).2 hrestLength
            omega
          · simp [Vermilion.Seq.len, suffix, List.append_assoc]
          · simp [Vermilion.Seq.subrange, Vermilion.Seq.len, suffix,
              List.append_assoc]
          · simpa [Vermilion.Seq.subrange, Vermilion.Seq.len, suffix,
              List.append_assoc] using hrecursive
termination_by input.length
decreasing_by
  all_goals
    first
    | (simp only [Vermilion.Seq.len] at hseparatorBound
       have hdecrease := Vermilion.Seq.len_subrange_suffix_toNat_lt
         input (split + 1) (by omega) hseparatorBound
       simpa [Vermilion.Seq.len] using hdecrease)
    | (rw [hrender, intercalate_cons_of_ne_nil [58] first rest hrest]
       simp
       omega)

theorem rep0_equation (input : Vermilion.Seq Int) (already : Int) :
    triptych_ipv6_roundtrip.ipv6_rep_0_matches input already ↔
      RepStep triptych_ipv6_roundtrip.ipv6_rep_0_matches
        triptych_ipv6_roundtrip.ipv6_is_wf_H16 8 8 input already := by
  rw [triptych_ipv6_roundtrip.ipv6_rep_0_matches]
  rw [dif_pos (Vermilion.Seq.len_nonneg input)]
  unfold RepStep
  apply exists_congr
  intro split
  by_cases hcontinue : already + 1 < 8 <;>
    by_cases hbound : split + 1 ≤ input.len <;>
  by_cases hseparator : input.subrange split (split + 1) = [58] <;>
    simp [hcontinue, hbound, hseparator,
      Vermilion.Seq.push, Vermilion.Seq.empty] <;> tauto

theorem rep1_equation (input : Vermilion.Seq Int) (already : Int) :
    triptych_ipv6_roundtrip.ipv6_rep_1_matches input already ↔
      RepStep triptych_ipv6_roundtrip.ipv6_rep_1_matches
        triptych_ipv6_roundtrip.ipv6_is_wf_H16L 1 7 input already := by
  rw [triptych_ipv6_roundtrip.ipv6_rep_1_matches]
  rw [dif_pos (Vermilion.Seq.len_nonneg input)]
  unfold RepStep
  apply exists_congr
  intro split
  by_cases hcontinue : already + 1 < 7 <;>
    by_cases hbound : split + 1 ≤ input.len <;>
  by_cases hseparator : input.subrange split (split + 1) = [58] <;>
    simp [hcontinue, hbound, hseparator,
      Vermilion.Seq.push, Vermilion.Seq.empty] <;> tauto

theorem rep2_equation (input : Vermilion.Seq Int) (already : Int) :
    triptych_ipv6_roundtrip.ipv6_rep_2_matches input already ↔
      RepStep triptych_ipv6_roundtrip.ipv6_rep_2_matches
        triptych_ipv6_roundtrip.ipv6_is_wf_H16R 1 7 input already := by
  rw [triptych_ipv6_roundtrip.ipv6_rep_2_matches]
  rw [dif_pos (Vermilion.Seq.len_nonneg input)]
  unfold RepStep
  apply exists_congr
  intro split
  by_cases hcontinue : already + 1 < 7 <;>
    by_cases hbound : split + 1 ≤ input.len <;>
  by_cases hseparator : input.subrange split (split + 1) = [58] <;>
    simp [hcontinue, hbound, hseparator,
      Vermilion.Seq.push, Vermilion.Seq.empty] <;> tauto

theorem rep0_code (input : Vermilion.Seq Int) (already : Int) :
    triptych_ipv6_roundtrip.ipv6_rep_0_matches input already ↔
      CodeRepValid triptych_ipv6_roundtrip.ipv6_is_wf_H16
        8 8 input already :=
  repMatcher_iff_codeRep _ _ 8 8 rep0_equation input already

theorem rep1_code (input : Vermilion.Seq Int) (already : Int) :
    triptych_ipv6_roundtrip.ipv6_rep_1_matches input already ↔
      CodeRepValid triptych_ipv6_roundtrip.ipv6_is_wf_H16L
        1 7 input already :=
  repMatcher_iff_codeRep _ _ 1 7 rep1_equation input already

theorem rep2_code (input : Vermilion.Seq Int) (already : Int) :
    triptych_ipv6_roundtrip.ipv6_rep_2_matches input already ↔
      CodeRepValid triptych_ipv6_roundtrip.ipv6_is_wf_H16R
        1 7 input already :=
  repMatcher_iff_codeRep _ _ 1 7 rep2_equation input already

theorem stringRep_codeRep
    (sourceItem : String → Prop)
    (codeItem : Vermilion.Seq Int → Prop)
    (itemEquiv : ∀ source, sourceItem source ↔ codeItem (encodeString source))
    (itemRange : ∀ sequence, codeItem sequence →
      ∀ index : Int,
        0 ≤ index ∧ index < Vermilion.Seq.len sequence →
          Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index))
    (lower upper : Nat) (hlowerPositive : 0 < lower) (source : String) :
    (∃ parts : List String,
        lower ≤ parts.length ∧
          parts.length ≤ upper ∧
          (∀ part ∈ parts, sourceItem part) ∧
          source = String.intercalate ":" parts) ↔
      CodeRepValid codeItem (Int.ofNat lower) (Int.ofNat upper)
        (encodeString source) 0 := by
  constructor
  · rintro ⟨parts, hlower, hupper, hitems, hrender⟩
    refine ⟨parts.map encodeString, ?_, ?_, ?_, ?_, ?_⟩
    · cases parts with
      | nil => simp at hlower; omega
      | cons => simp
    · simp only [List.length_map, Int.zero_add]
      exact (Int.ofNat_le).2 hlower
    · simp only [List.length_map, Int.zero_add]
      exact (Int.ofNat_le).2 hupper
    · intro part hpart
      rw [List.mem_map] at hpart
      rcases hpart with ⟨text, htext, rfl⟩
      exact (itemEquiv text).1 (hitems text htext)
    · rw [hrender, encodeString_intercalate]
      norm_num [encodeString]
  · rintro ⟨parts, hparts, hlower, hupper, hitems, hrender⟩
    let texts := parts.map decodeSequence
    have hencodes :
        texts.map encodeString = parts := by
      apply List.ext_getElem
      · simp [texts]
      · intro index hleft hright
        have hpart := hitems parts[index] (List.getElem_mem hright)
        simpa [texts] using
          encode_decode_sequence parts[index] (itemRange parts[index] hpart)
    refine ⟨texts, ?_, ?_, ?_, ?_⟩
    · simpa [texts] using (Int.ofNat_le).1 (by simpa using hlower)
    · simpa [texts] using (Int.ofNat_le).1 (by simpa using hupper)
    · intro text htext
      rw [List.mem_map] at htext
      rcases htext with ⟨part, hpart, rfl⟩
      apply (itemEquiv (decodeSequence part)).2
      rw [encode_decode_sequence part (itemRange part (hitems part hpart))]
      exact hitems part hpart
    · apply encodeString_injective
      rw [encodeString_intercalate, hencodes]
      simpa [encodeString] using hrender

theorem h16_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv6_roundtrip.ipv6_is_wf_H16 sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  apply hex_witness_sequence_range sequence
    (fun digits =>
      1 ≤ Vermilion.Seq.len digits ∧ Vermilion.Seq.len digits ≤ 4)
  simpa [triptych_ipv6_roundtrip.ipv6_is_wf_H16,
    triptych_ipv6_roundtrip.triptych_is_hex_digit,
    triptych_ipv6_roundtrip.triptych_is_digit, IsHexDigitCode, IsDigitCode,
    or_comm, or_left_comm, or_assoc] using hwf

theorem h16L_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv6_roundtrip.ipv6_is_wf_H16L sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  apply hex_witness_sequence_range sequence
    (fun digits =>
      1 ≤ Vermilion.Seq.len digits ∧ Vermilion.Seq.len digits ≤ 4)
  simpa [triptych_ipv6_roundtrip.ipv6_is_wf_H16L,
    triptych_ipv6_roundtrip.triptych_is_hex_digit,
    triptych_ipv6_roundtrip.triptych_is_digit, IsHexDigitCode, IsDigitCode,
    or_comm, or_left_comm, or_assoc] using hwf

theorem h16R_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv6_roundtrip.ipv6_is_wf_H16R sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  apply hex_witness_sequence_range sequence
    (fun digits =>
      1 ≤ Vermilion.Seq.len digits ∧ Vermilion.Seq.len digits ≤ 4)
  simpa [triptych_ipv6_roundtrip.ipv6_is_wf_H16R,
    triptych_ipv6_roundtrip.triptych_is_hex_digit,
    triptych_ipv6_roundtrip.triptych_is_digit, IsHexDigitCode, IsDigitCode,
    or_comm, or_left_comm, or_assoc] using hwf

theorem full_equiv (source : String) :
    IPv6.IsWf.Full source ↔
      triptych_ipv6_roundtrip.ipv6_is_wf_Full (encodeString source) := by
  unfold IPv6.IsWf.Full triptych_ipv6_roundtrip.ipv6_is_wf_Full
  have hrep := stringRep_codeRep IPv6.IsWf.H16
    triptych_ipv6_roundtrip.ipv6_is_wf_H16 h16_equiv
    h16_sequence_range 8 8 (by omega) source
  constructor
  · intro hwf
    exact ⟨encodeString source, rfl,
      (rep0_code (encodeString source) 0).2 (hrep.1 hwf)⟩
  · rintro ⟨items, hitems, hmatch⟩
    subst items
    exact hrep.2 ((rep0_code (encodeString source) 0).1 hmatch)

theorem left_equiv (source : String) :
    IPv6.IsWf.Left source ↔
      triptych_ipv6_roundtrip.ipv6_is_wf_Left (encodeString source) := by
  unfold IPv6.IsWf.Left triptych_ipv6_roundtrip.ipv6_is_wf_Left
  have hrep := stringRep_codeRep IPv6.IsWf.H16L
    triptych_ipv6_roundtrip.ipv6_is_wf_H16L h16L_equiv
    h16L_sequence_range 1 7 (by omega) source
  constructor
  · intro hwf
    exact ⟨encodeString source, rfl,
      (rep1_code (encodeString source) 0).2 (hrep.1 hwf)⟩
  · rintro ⟨items, hitems, hmatch⟩
    subst items
    exact hrep.2 ((rep1_code (encodeString source) 0).1 hmatch)

theorem right_equiv (source : String) :
    IPv6.IsWf.Right source ↔
      triptych_ipv6_roundtrip.ipv6_is_wf_Right (encodeString source) := by
  unfold IPv6.IsWf.Right triptych_ipv6_roundtrip.ipv6_is_wf_Right
  have hrep := stringRep_codeRep IPv6.IsWf.H16R
    triptych_ipv6_roundtrip.ipv6_is_wf_H16R h16R_equiv
    h16R_sequence_range 1 7 (by omega) source
  constructor
  · intro hwf
    exact ⟨encodeString source, rfl,
      (rep2_code (encodeString source) 0).2 (hrep.1 hwf)⟩
  · rintro ⟨items, hitems, hmatch⟩
    subst items
    exact hrep.2 ((rep2_code (encodeString source) 0).1 hmatch)

theorem mem_intercalate_parts {α : Type}
    (separator : List α) (parts : List (List α)) (element : α)
    (helement : element ∈ separator.intercalate parts) :
    element ∈ separator ∨ ∃ part ∈ parts, element ∈ part := by
  induction parts with
  | nil => simp at helement
  | cons part rest ih =>
      cases rest with
      | nil =>
          exact Or.inr ⟨part, by simp, by simpa using helement⟩
      | cons next tail =>
          rw [List.intercalate_cons_cons] at helement
          have helement' :
              (element ∈ part ∨ element ∈ separator) ∨
                element ∈ separator.intercalate (next :: tail) := by
            simpa only [List.mem_append] using helement
          rcases helement' with (hpart | hseparator) | hrest
          · exact Or.inr ⟨part, by simp, hpart⟩
          · exact Or.inl hseparator
          · rcases ih hrest with hseparator | ⟨found, hfound, hmember⟩
            · exact Or.inl hseparator
            · exact Or.inr ⟨found, by simp [hfound], hmember⟩

theorem codeRep_sequence_range
    (itemValid : Vermilion.Seq Int → Prop)
    (itemRange : ∀ sequence, itemValid sequence →
      ∀ index : Int,
        0 ≤ index ∧ index < Vermilion.Seq.len sequence →
          Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index))
    (lower upper already : Int) (input : Vermilion.Seq Int)
    (hrep : CodeRepValid itemValid lower upper input already) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len input →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index input index) := by
  rintro index hindex
  rcases hrep with ⟨parts, _, _, _, hitems, rfl⟩
  have hbound :
      index.toNat < ([58].intercalate parts).length := by
    simp only [Vermilion.Seq.len] at hindex
    omega
  have hmember :
      ([58].intercalate parts)[index.toNat] ∈ [58].intercalate parts :=
    List.getElem_mem hbound
  rcases mem_intercalate_parts [58] parts _ hmember with
    hseparator | ⟨part, hpart, hpartMember⟩
  · have hcode : ([58].intercalate parts)[index.toNat] = 58 := by
      simpa using hseparator
    simpa [Vermilion.Seq.index, hindex.1,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbound, hcode,
      Vermilion.isUnicodeScalar]
  · rw [List.mem_iff_getElem] at hpartMember
    rcases hpartMember with ⟨partIndex, hpartBound, hcode⟩
    have hscalar := itemRange part (hitems part hpart) (Int.ofNat partIndex)
      ⟨Int.ofNat_nonneg _, by
        simp only [Vermilion.Seq.len]
        exact (Int.ofNat_lt).2 hpartBound⟩
    simpa [Vermilion.Seq.index, hindex.1,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbound,
      List.getElem?_eq_getElem hpartBound, hcode] using hscalar

theorem left_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv6_roundtrip.ipv6_is_wf_Left sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  rcases hwf with ⟨items, hsequence, hmatch⟩
  subst sequence
  exact codeRep_sequence_range _ h16L_sequence_range 1 7 0 items
    ((rep1_code items 0).1 hmatch)

theorem right_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv6_roundtrip.ipv6_is_wf_Right sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  rcases hwf with ⟨items, hsequence, hmatch⟩
  subst sequence
  exact codeRep_sequence_range _ h16R_sequence_range 1 7 0 items
    ((rep2_code items 0).1 hmatch)

theorem decode_left_wf (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv6_roundtrip.ipv6_is_wf_Left sequence) :
    ∃ source : String,
      sequence = encodeString source ∧ IPv6.IsWf.Left source := by
  let source := decodeSequence sequence
  have hencode : encodeString source = sequence :=
    encode_decode_sequence sequence (left_sequence_range sequence hwf)
  exact ⟨source, hencode.symm,
    (left_equiv source).2 (by simpa [hencode] using hwf)⟩

theorem decode_right_wf (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv6_roundtrip.ipv6_is_wf_Right sequence) :
    ∃ source : String,
      sequence = encodeString source ∧ IPv6.IsWf.Right source := by
  let source := decodeSequence sequence
  have hencode : encodeString source = sequence :=
    encode_decode_sequence sequence (right_sequence_range sequence hwf)
  exact ⟨source, hencode.symm,
    (right_equiv source).2 (by simpa [hencode] using hwf)⟩

theorem compressed_iff_parts (source : String) :
    IPv6.IsWf.Compressed source ↔
      ∃ left right : String,
        source = left ++ ("::" ++ right) ∧
          (left = "" ∨ IPv6.IsWf.Left left) ∧
          (right = "" ∨ IPv6.IsWf.Right right) := by
  unfold IPv6.IsWf.Compressed
  constructor
  · rintro (⟨left, rest, hsource, hleft, right, hrest, hright⟩ |
      ⟨right, hsource, hright⟩)
    · exact ⟨left, right, by simp [hsource, hrest, String.append_assoc],
        Or.inr hleft, hright.symm⟩
    · exact ⟨"", right, by simpa using hsource, Or.inl rfl, hright.symm⟩
  · rintro ⟨left, right, hsource, hleft, hright⟩
    rcases hleft with rfl | hleft
    · exact Or.inr ⟨right, by simpa using hsource, hright.symm⟩
    · exact Or.inl ⟨left, "::" ++ right, hsource, hleft,
        right, rfl, hright.symm⟩

theorem compressed_equiv (source : String) :
    IPv6.IsWf.Compressed source ↔
      triptych_ipv6_roundtrip.ipv6_is_wf_Compressed
        (encodeString source) := by
  rw [compressed_iff_parts]
  constructor
  · rintro ⟨left, right, hsource, hleft, hright⟩
    refine ⟨encodeString left, encodeString right, ?_⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa [encodeString_append, encodeString, Vermilion.Seq.add,
        Vermilion.Seq.push, Vermilion.Seq.empty, List.append_assoc] using
          congrArg encodeString hsource
    · rcases hleft with rfl | hleft
      · exact Or.inl (by simp [encodeString, Vermilion.Seq.len])
      · exact Or.inr ((left_equiv left).1 hleft)
    · rcases hright with rfl | hright
      · exact Or.inl (by simp [encodeString, Vermilion.Seq.len])
      · exact Or.inr ((right_equiv right).1 hright)
  · rintro ⟨leftSequence, rightSequence,
      ⟨⟨hsource, hleft⟩, hright⟩⟩
    obtain ⟨left, hleftEncode, hleftWf⟩ :
        ∃ left : String,
          leftSequence = encodeString left ∧
            (left = "" ∨ IPv6.IsWf.Left left) := by
      rcases hleft with hleftEmpty | hleftWf
      · have hleftEmpty' :=
          sequence_eq_empty_of_length_zero leftSequence hleftEmpty
        exact ⟨"", by simpa [encodeString, Vermilion.Seq.empty] using
          hleftEmpty', Or.inl rfl⟩
      · obtain ⟨left, hencode, hwf⟩ :=
          decode_left_wf leftSequence hleftWf
        exact ⟨left, hencode, Or.inr hwf⟩
    obtain ⟨right, hrightEncode, hrightWf⟩ :
        ∃ right : String,
          rightSequence = encodeString right ∧
            (right = "" ∨ IPv6.IsWf.Right right) := by
      rcases hright with hrightEmpty | hrightWf
      · have hrightEmpty' :=
          sequence_eq_empty_of_length_zero rightSequence hrightEmpty
        exact ⟨"", by simpa [encodeString, Vermilion.Seq.empty] using
          hrightEmpty', Or.inl rfl⟩
      · obtain ⟨right, hencode, hwf⟩ :=
          decode_right_wf rightSequence hrightWf
        exact ⟨right, hencode, Or.inr hwf⟩
    refine ⟨left, right, ?_, hleftWf, hrightWf⟩
    apply encodeString_injective
    rw [encodeString_append, encodeString_append, ← hleftEncode,
      ← hrightEncode]
    simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
      Vermilion.Seq.empty, List.append_assoc] using hsource

theorem v6addr_equiv (source : String) :
    IPv6.IsWf.V6Addr source ↔
      triptych_ipv6_roundtrip.ipv6_is_wf_V6Addr
        (encodeString source) := by
  unfold IPv6.IsWf.V6Addr triptych_ipv6_roundtrip.ipv6_is_wf_V6Addr
  constructor
  · rintro (hfull | hcompressed)
    · exact Or.inl ⟨encodeString source, rfl, (full_equiv source).1 hfull⟩
    · exact Or.inr
        ⟨encodeString source, rfl, (compressed_equiv source).1 hcompressed⟩
  · rintro (⟨full, hsource, hfull⟩ |
      ⟨compressed, hsource, hcompressed⟩)
    · subst full
      exact Or.inl ((full_equiv source).2 hfull)
    · subst compressed
      exact Or.inr ((compressed_equiv source).2 hcompressed)

theorem full_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv6_roundtrip.ipv6_is_wf_Full sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  rcases hwf with ⟨items, hsequence, hmatch⟩
  subst sequence
  exact codeRep_sequence_range _ h16_sequence_range 8 8 0 items
    ((rep0_code items 0).1 hmatch)

theorem compressed_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv6_roundtrip.ipv6_is_wf_Compressed sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  rcases hwf with ⟨left, right, ⟨⟨rfl, hleft⟩, hright⟩⟩
  have hleftRange :
      ∀ index : Int,
        0 ≤ index ∧ index < Vermilion.Seq.len left →
          Vermilion.isUnicodeScalar (Vermilion.Seq.index left index) := by
    rcases hleft with hleft | hleft
    · exact empty_sequence_range left hleft
    · exact left_sequence_range left hleft
  have hrightRange :
      ∀ index : Int,
        0 ≤ index ∧ index < Vermilion.Seq.len right →
          Vermilion.isUnicodeScalar (Vermilion.Seq.index right index) := by
    rcases hright with hright | hright
    · exact empty_sequence_range right hright
    · exact right_sequence_range right hright
  have hseparatorRange :
      ∀ index : Int,
        0 ≤ index ∧
            index <
              Vermilion.Seq.len
                (Vermilion.Seq.push
                  (Vermilion.Seq.push Vermilion.Seq.empty 58) 58) →
          Vermilion.isUnicodeScalar
            (Vermilion.Seq.index
              (Vermilion.Seq.push
                (Vermilion.Seq.push Vermilion.Seq.empty 58) 58) index) := by
    intro index hindex
    have hposition : index = 0 ∨ index = 1 := by
      simp [Vermilion.Seq.len, Vermilion.Seq.push,
        Vermilion.Seq.empty] at hindex
      omega
    rcases hposition with rfl | rfl <;>
      norm_num [Vermilion.Seq.index, Vermilion.Seq.push,
        Vermilion.Seq.empty, Vermilion.isUnicodeScalar]
  exact sequence_add_range
    (Vermilion.Seq.add left
      (Vermilion.Seq.push
        (Vermilion.Seq.push Vermilion.Seq.empty 58) 58))
    right
    (sequence_add_range left
      (Vermilion.Seq.push
        (Vermilion.Seq.push Vermilion.Seq.empty 58) 58)
      hleftRange hseparatorRange)
    hrightRange

theorem v6addr_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv6_roundtrip.ipv6_is_wf_V6Addr sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  rcases hwf with ⟨full, hsequence, hfull⟩ |
      ⟨compressed, hsequence, hcompressed⟩
  · subst sequence
    exact full_sequence_range full hfull
  · subst sequence
    exact compressed_sequence_range compressed hcompressed

theorem prefix_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv6_roundtrip.ipv6_is_wf_Prefix sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  rcases hwf with ⟨digits, hsequence, _, hdigits⟩
  subst sequence
  apply digit_sequence_range digits
  intro index hindex
  simpa [triptych_ipv6_roundtrip.triptych_is_digit, IsDigitCode] using
    hdigits index hindex

theorem decode_v6addr_wf (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv6_roundtrip.ipv6_is_wf_V6Addr sequence) :
    ∃ source : String,
      sequence = encodeString source ∧ IPv6.IsWf.V6Addr source := by
  let source := decodeSequence sequence
  have hencode : encodeString source = sequence :=
    encode_decode_sequence sequence (v6addr_sequence_range sequence hwf)
  exact ⟨source, hencode.symm,
    (v6addr_equiv source).2 (by simpa [hencode] using hwf)⟩

theorem decode_prefix_wf (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv6_roundtrip.ipv6_is_wf_Prefix sequence) :
    ∃ source : String,
      sequence = encodeString source ∧ IPv6.IsWf.Prefix source := by
  let source := decodeSequence sequence
  have hencode : encodeString source = sequence :=
    encode_decode_sequence sequence (prefix_sequence_range sequence hwf)
  exact ⟨source, hencode.symm,
    (prefix_equiv source).2 (by simpa [hencode] using hwf)⟩

theorem v6net_equiv (source : String) :
    IPv6.IsWf.V6Net source ↔
      triptych_ipv6_roundtrip.ipv6_is_wf_V6Net
        (encodeString source) := by
  unfold IPv6.IsWf.V6Net IPv6.Production
  constructor
  · rintro (haddr | ⟨addr, pre, ⟨hsource, haddr⟩, hprefix⟩)
    · exact Or.inl ⟨encodeString source, rfl, (v6addr_equiv source).1 haddr⟩
    · refine Or.inr ⟨encodeString addr, encodeString pre, ?_⟩
      refine ⟨⟨?_, (v6addr_equiv addr).1 haddr⟩,
        (prefix_equiv pre).1 hprefix⟩
      simpa [encodeString_append, encodeString, Vermilion.Seq.add,
        Vermilion.Seq.push, Vermilion.Seq.empty, List.append_assoc] using
          congrArg encodeString hsource
  · rintro (⟨addrSequence, hsource, haddr⟩ |
      ⟨addrSequence, prefixSequence, ⟨⟨hsource, haddr⟩, hprefix⟩⟩)
    · subst addrSequence
      exact Or.inl ((v6addr_equiv source).2 haddr)
    · obtain ⟨addr, haddrSequence, haddrWf⟩ :=
        decode_v6addr_wf addrSequence haddr
      obtain ⟨pre, hprefixSequence, hprefixWf⟩ :=
        decode_prefix_wf prefixSequence hprefix
      refine Or.inr ⟨addr, pre, ⟨?_, haddrWf⟩, hprefixWf⟩
      apply encodeString_injective
      rw [encodeString_append, encodeString_append, ← haddrSequence,
        ← hprefixSequence]
      simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
        Vermilion.Seq.empty, List.append_assoc] using hsource

def IPv6AddressParts
    (address full left right : String) : Prop :=
  (full = address ∧ IPv6.IsWf.Full full ∧ left = "" ∧ right = "") ∨
    (full = "" ∧
      address = left ++ ("::" ++ right) ∧
      (left = "" ∨ IPv6.IsWf.Left left) ∧
      (right = "" ∨ IPv6.IsWf.Right right))

def IPv6Parts
    (input full left right pre : String) : Prop :=
  ∃ address : String,
    IPv6AddressParts address full left right ∧
      ((pre = "" ∧ input = address) ∨
        (IPv6.IsWf.Prefix pre ∧ input = address ++ ("/" ++ pre)))

theorem address_parts_exists_equiv (address : String) :
    IPv6.IsWf.V6Addr address ↔
      ∃ full left right : String,
        IPv6AddressParts address full left right := by
  unfold IPv6.IsWf.V6Addr IPv6AddressParts
  constructor
  · rintro (hfull | hcompressed)
    · exact ⟨address, "", "", Or.inl ⟨rfl, hfull, rfl, rfl⟩⟩
    · rcases (compressed_iff_parts address).1 hcompressed with
        ⟨left, right, haddress, hleft, hright⟩
      exact ⟨"", left, right,
        Or.inr ⟨rfl, haddress, hleft, hright⟩⟩
  · rintro ⟨full, left, right,
      (⟨rfl, hfull, rfl, rfl⟩ |
        ⟨rfl, haddress, hleft, hright⟩)⟩
    · exact Or.inl hfull
    · exact Or.inr ((compressed_iff_parts address).2
        ⟨left, right, haddress, hleft, hright⟩)

theorem parts_exists_equiv (input : String) :
    IPv6.IsWf.V6Net input ↔
      ∃ full left right pre : String,
        IPv6Parts input full left right pre := by
  unfold IPv6.IsWf.V6Net IPv6.Production IPv6Parts
  constructor
  · rintro (haddress |
      ⟨address, pre, ⟨hinput, haddress⟩, hprefix⟩)
    · rcases (address_parts_exists_equiv input).1 haddress with
        ⟨full, left, right, hparts⟩
      exact ⟨full, left, right, "", input, hparts,
        Or.inl ⟨rfl, rfl⟩⟩
    · rcases (address_parts_exists_equiv address).1 haddress with
        ⟨full, left, right, hparts⟩
      exact ⟨full, left, right, pre, address, hparts,
        Or.inr ⟨hprefix, by simpa [String.append_assoc] using hinput⟩⟩
  · rintro ⟨full, left, right, pre, address, hparts,
      (⟨rfl, rfl⟩ | ⟨hprefix, hinput⟩)⟩
    · exact Or.inl ((address_parts_exists_equiv input).2
        ⟨full, left, right, hparts⟩)
    · exact Or.inr ⟨address, pre,
        ⟨by simpa [String.append_assoc] using hinput,
          (address_parts_exists_equiv address).2
            ⟨full, left, right, hparts⟩⟩,
        hprefix⟩

theorem matches_full_wf
    (sequence : Vermilion.Seq Int)
    (view : triptych_ipv6_roundtrip.IPv6View) :
    triptych_ipv6_roundtrip.ipv6_matches_Full sequence view ↔
      triptych_ipv6_roundtrip.ipv6_is_wf_Full sequence := by
  rfl

theorem matches_left_wf
    (sequence : Vermilion.Seq Int)
    (view : triptych_ipv6_roundtrip.IPv6View) :
    triptych_ipv6_roundtrip.ipv6_matches_Left sequence view ↔
      triptych_ipv6_roundtrip.ipv6_is_wf_Left sequence := by
  rfl

theorem matches_right_wf
    (sequence : Vermilion.Seq Int)
    (view : triptych_ipv6_roundtrip.IPv6View) :
    triptych_ipv6_roundtrip.ipv6_matches_Right sequence view ↔
      triptych_ipv6_roundtrip.ipv6_is_wf_Right sequence := by
  rfl

theorem matches_prefix_wf
    (sequence : Vermilion.Seq Int)
    (view : triptych_ipv6_roundtrip.IPv6View) :
    triptych_ipv6_roundtrip.ipv6_matches_Prefix sequence view ↔
      triptych_ipv6_roundtrip.ipv6_is_wf_Prefix sequence := by
  rfl

theorem matches_compressed_equiv
    (sequence : Vermilion.Seq Int)
    (input full left right pre : String) :
    triptych_ipv6_roundtrip.ipv6_matches_Compressed sequence
        (.IPv6View (encodeString input) (encodeString full)
          (encodeString left) (encodeString right) (encodeString pre)) ↔
      sequence = encodeString (left ++ ("::" ++ right)) ∧
        (left = "" ∨ IPv6.IsWf.Left left) ∧
        (right = "" ∨ IPv6.IsWf.Right right) := by
  constructor
  · rintro ⟨leftSequence, rightSequence,
      ⟨⟨hsequence, hleft⟩, hright⟩⟩
    obtain ⟨hleftSequence, hleftWf⟩ :
        leftSequence = encodeString left ∧
          (left = "" ∨ IPv6.IsWf.Left left) := by
      rcases hleft with ⟨hlength, hfield⟩ | ⟨hfield, hmatch⟩
      · have hempty :=
          sequence_eq_empty_of_length_zero leftSequence hlength
        have hleftEmpty : left = "" := by
          apply encodeString_injective
          simpa [encodeString, Vermilion.Seq.empty] using hfield
        exact ⟨by simpa [hleftEmpty, encodeString, Vermilion.Seq.empty] using
          hempty, Or.inl hleftEmpty⟩
      · subst leftSequence
        exact ⟨rfl, Or.inr ((left_equiv left).2
          ((matches_left_wf (encodeString left) _).1 hmatch))⟩
    obtain ⟨hrightSequence, hrightWf⟩ :
        rightSequence = encodeString right ∧
          (right = "" ∨ IPv6.IsWf.Right right) := by
      rcases hright with ⟨hlength, hfield⟩ | ⟨hfield, hmatch⟩
      · have hempty :=
          sequence_eq_empty_of_length_zero rightSequence hlength
        have hrightEmpty : right = "" := by
          apply encodeString_injective
          simpa [encodeString, Vermilion.Seq.empty] using hfield
        exact ⟨by simpa [hrightEmpty, encodeString, Vermilion.Seq.empty] using
          hempty, Or.inl hrightEmpty⟩
      · subst rightSequence
        exact ⟨rfl, Or.inr ((right_equiv right).2
          ((matches_right_wf (encodeString right) _).1 hmatch))⟩
    refine ⟨?_, hleftWf, hrightWf⟩
    rw [hleftSequence, hrightSequence] at hsequence
    simpa [encodeString_append, encodeString, Vermilion.Seq.add,
      Vermilion.Seq.push, Vermilion.Seq.empty, List.append_assoc] using
        hsequence
  · rintro ⟨hsequence, hleft, hright⟩
    refine ⟨encodeString left, encodeString right, ?_⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa [encodeString_append, encodeString, Vermilion.Seq.add,
        Vermilion.Seq.push, Vermilion.Seq.empty, List.append_assoc] using
          hsequence
    · rcases hleft with rfl | hleft
      · exact Or.inl ⟨by simp [encodeString, Vermilion.Seq.len],
          by simp [encodeString, Vermilion.Seq.empty]⟩
      · exact Or.inr ⟨rfl, (matches_left_wf (encodeString left) _).2
          ((left_equiv left).1 hleft)⟩
    · rcases hright with rfl | hright
      · exact Or.inl ⟨by simp [encodeString, Vermilion.Seq.len],
          by simp [encodeString, Vermilion.Seq.empty]⟩
      · exact Or.inr ⟨rfl, (matches_right_wf (encodeString right) _).2
          ((right_equiv right).1 hright)⟩

theorem matches_address_equiv
    (sequence : Vermilion.Seq Int)
    (input full left right pre : String) :
    triptych_ipv6_roundtrip.ipv6_matches_V6Addr sequence
        (.IPv6View (encodeString input) (encodeString full)
          (encodeString left) (encodeString right) (encodeString pre)) ↔
      ∃ address : String,
        sequence = encodeString address ∧
          IPv6AddressParts address full left right := by
  constructor
  · rintro (⟨fullSequence,
      ⟨⟨⟨hsequence, hfield, hmatch⟩, hleft⟩, hright⟩⟩ |
      ⟨compressedSequence, ⟨⟨hsequence, hmatch⟩, hfull⟩⟩)
    · have hleftEmpty : left = "" :=
        encodeString_injective (by
          simpa [encodeString, Vermilion.Seq.empty] using hleft)
      have hrightEmpty : right = "" :=
        encodeString_injective (by
          simpa [encodeString, Vermilion.Seq.empty] using hright)
      change encodeString full = fullSequence at hfield
      exact ⟨full, hsequence.trans hfield.symm,
        Or.inl ⟨rfl,
          (full_equiv full).2
            (by
              rw [hfield]
              exact (matches_full_wf fullSequence _).1 hmatch),
          hleftEmpty, hrightEmpty⟩⟩
    · have hfullEmpty : full = "" :=
        encodeString_injective (by
          simpa [encodeString, Vermilion.Seq.empty] using hfull)
      rcases (matches_compressed_equiv compressedSequence
        input full left right pre).1 hmatch with
        ⟨hcompressed, hleft, hright⟩
      exact ⟨left ++ ("::" ++ right),
        hsequence.trans hcompressed,
        Or.inr ⟨hfullEmpty, rfl, hleft, hright⟩⟩
  · rintro ⟨address, hsequence,
      (⟨rfl, hfull, rfl, rfl⟩ |
        ⟨rfl, rfl, hleft, hright⟩)⟩
    · exact Or.inl ⟨encodeString full,
        ⟨⟨⟨hsequence, rfl,
          (matches_full_wf (encodeString full) _).2
            ((full_equiv full).1 hfull)⟩,
          by simp [encodeString, Vermilion.Seq.empty]⟩,
          by simp [encodeString, Vermilion.Seq.empty]⟩⟩
    · exact Or.inr ⟨encodeString (left ++ ("::" ++ right)),
        ⟨⟨hsequence,
          (matches_compressed_equiv _ input "" left right pre).2
            ⟨rfl, hleft, hright⟩⟩,
          by simp [encodeString, Vermilion.Seq.empty]⟩⟩

theorem matches_view_equiv
    (input full left right pre : String) :
    triptych_ipv6_roundtrip.ipv6_matches_view (encodeString input)
        (.IPv6View (encodeString input) (encodeString full)
          (encodeString left) (encodeString right) (encodeString pre)) ↔
      IPv6Parts input full left right pre := by
  constructor
  · rintro ⟨_, hbare | hprefixed⟩
    · rcases hbare with
        ⟨addressSequence, ⟨⟨hinput, haddress⟩, hprefixField⟩⟩
      rcases (matches_address_equiv addressSequence
        input full left right pre).1 haddress with
        ⟨address, haddressSequence, hparts⟩
      have hpre : pre = "" :=
        encodeString_injective (by
          simpa [encodeString, Vermilion.Seq.empty] using hprefixField)
      refine ⟨address, hparts, Or.inl ⟨hpre, ?_⟩⟩
      apply encodeString_injective
      rw [hinput, haddressSequence]
    · rcases hprefixed with
        ⟨addressSequence, prefixSequence,
          ⟨⟨hinput, haddress⟩, ⟨hprefixField, hprefixMatch⟩⟩⟩
      rcases (matches_address_equiv addressSequence
        input full left right pre).1 haddress with
        ⟨address, haddressSequence, hparts⟩
      subst prefixSequence
      have hprefix : IPv6.IsWf.Prefix pre :=
        (prefix_equiv pre).2
          ((matches_prefix_wf (encodeString pre) _).1 hprefixMatch)
      refine ⟨address, hparts, Or.inr ⟨hprefix, ?_⟩⟩
      apply encodeString_injective
      rw [encodeString_append, encodeString_append, hinput,
        haddressSequence]
      simp [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
        Vermilion.Seq.empty, List.append_assoc]
  · rintro ⟨address, hparts,
      (⟨rfl, hinput⟩ | ⟨hprefix, hinput⟩)⟩
    · refine ⟨rfl, Or.inl ⟨encodeString address, ?_⟩⟩
      refine ⟨⟨?_, (matches_address_equiv _ input full left right "").2
        ⟨address, rfl, hparts⟩⟩, ?_⟩
      · simpa [hinput]
      · rfl
    · refine ⟨rfl, Or.inr
        ⟨encodeString address, encodeString pre, ?_⟩⟩
      refine ⟨⟨?_, (matches_address_equiv _ input full left right pre).2
        ⟨address, rfl, hparts⟩⟩, ⟨rfl, ?_⟩⟩
      · simpa [encodeString_append, encodeString, Vermilion.Seq.add,
          Vermilion.Seq.push, Vermilion.Seq.empty,
          List.append_assoc] using congrArg encodeString hinput
      · exact (matches_prefix_wf (encodeString pre) _).2
          ((prefix_equiv pre).1 hprefix)

theorem matching_view_exists_equiv (input : String) :
    IPv6.IsWf.V6Net input ↔
      ∃ full left right pre : String,
        triptych_ipv6_roundtrip.ipv6_matches_view (encodeString input)
          (.IPv6View (encodeString input) (encodeString full)
            (encodeString left) (encodeString right) (encodeString pre)) := by
  rw [parts_exists_equiv]
  apply exists_congr
  intro full
  apply exists_congr
  intro left
  apply exists_congr
  intro right
  apply exists_congr
  intro pre
  exact (matches_view_equiv input full left right pre).symm

def sourceViewFull (view : IPv6.GrammarView.View) : String :=
  match view.addr with
  | .full parts => renderGroups parts
  | .compressed _ _ => ""

def sourceViewLeft (view : IPv6.GrammarView.View) : String :=
  match view.addr with
  | .full _ => ""
  | .compressed left _ => renderGroups left

def sourceViewRight (view : IPv6.GrammarView.View) : String :=
  match view.addr with
  | .full _ => ""
  | .compressed _ right => renderGroups right

def sourceViewPrefix (view : IPv6.GrammarView.View) : String :=
  view.«prefix».getD ""

theorem source_view_constraints (view : IPv6.GrammarView.View) :
    view.Constraints =
      IPv6.WfConstraints (sourceViewLeft view) (sourceViewRight view)
        (sourceViewPrefix view) := by
  cases view with
  | mk address pre =>
      cases address <;> rfl

theorem source_view_value_constraints
    (view : IPv6.GrammarView.View) :
    view.ValueConstraints =
      IPv6.Constraints (sourceViewFull view) (sourceViewLeft view)
        (sourceViewRight view) (sourceViewPrefix view) := by
  cases view with
  | mk address pre =>
      cases address <;> rfl

theorem source_view_parts (view : IPv6.GrammarView.View)
    (hsyntax : view.SyntaxValid) :
    IPv6Parts view.render (sourceViewFull view) (sourceViewLeft view)
      (sourceViewRight view) (sourceViewPrefix view) := by
  cases view with
  | mk address pre =>
      cases address with
      | full parts =>
          change
            (parts.length = 8 ∧ ∀ part ∈ parts, HexValid part) ∧
              OptionalPrefixSyntax pre at hsyntax
          refine ⟨renderGroups parts,
            Or.inl ⟨rfl, ?_, rfl, rfl⟩, ?_⟩
          · exact ⟨parts, by omega, by omega, hsyntax.1.2, rfl⟩
          · cases pre with
            | none =>
                exact Or.inl ⟨rfl, by simp [IPv6.GrammarView.View.render,
                  renderNet, IPv6.GrammarView.Addr.render]⟩
            | some pre =>
                exact Or.inr ⟨hsyntax.2, by
                  simp [sourceViewPrefix, IPv6.GrammarView.View.render,
                    renderNet, IPv6.GrammarView.Addr.render,
                    String.append_assoc]⟩
      | compressed leftParts rightParts =>
          change
            (leftParts.length ≤ 7 ∧ rightParts.length ≤ 7 ∧
                (∀ part ∈ leftParts, HexValid part) ∧
                ∀ part ∈ rightParts, HexValid part) ∧
              OptionalPrefixSyntax pre at hsyntax
          have hleft :
              renderGroups leftParts = "" ∨
                IPv6.IsWf.Left (renderGroups leftParts) := by
            cases leftParts with
            | nil => exact Or.inl (by simp [renderGroups])
            | cons part rest =>
                exact Or.inr ⟨part :: rest, by simp, hsyntax.1.1,
                  hsyntax.1.2.2.1, rfl⟩
          have hright :
              renderGroups rightParts = "" ∨
                IPv6.IsWf.Right (renderGroups rightParts) := by
            cases rightParts with
            | nil => exact Or.inl (by simp [renderGroups])
            | cons part rest =>
                exact Or.inr ⟨part :: rest, by simp, hsyntax.1.2.1,
                  hsyntax.1.2.2.2, rfl⟩
          refine ⟨renderGroups leftParts ++ ("::" ++ renderGroups rightParts),
            Or.inr ⟨rfl, rfl, hleft, hright⟩, ?_⟩
          cases pre with
          | none =>
              exact Or.inl ⟨rfl, by simp [IPv6.GrammarView.View.render,
                renderNet, IPv6.GrammarView.Addr.render,
                String.append_assoc]⟩
          | some pre =>
              exact Or.inr ⟨hsyntax.2, by
                simp [sourceViewPrefix, IPv6.GrammarView.View.render,
                  renderNet, IPv6.GrammarView.Addr.render,
                  String.append_assoc]⟩

theorem source_view_of_parts
    (input full left right pre : String)
    (hparts : IPv6Parts input full left right pre) :
    ∃ view : IPv6.GrammarView.View,
      view.SyntaxValid ∧
        view.render = input ∧
        sourceViewFull view = full ∧
        sourceViewLeft view = left ∧
        sourceViewRight view = right ∧
        sourceViewPrefix view = pre := by
  rcases hparts with ⟨address, haddress, hnet⟩
  rcases haddress with
      ⟨hfullAddress, hfull, hleft, hright⟩ |
      ⟨hfull, haddress, hleft, hright⟩
  · rcases hfull with ⟨parts, hlower, hupper, hitems, hrender⟩
    have hlength : parts.length = 8 := by omega
    have hrender' : renderGroups parts = full := by
      simpa [renderGroups] using hrender.symm
    rcases hnet with ⟨hpre, hinput⟩ | ⟨hprefix, hinput⟩
    · refine ⟨⟨.full parts, none⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ⟨⟨hlength, hitems⟩, trivial⟩
      · simp [IPv6.GrammarView.View.render, renderNet,
          IPv6.GrammarView.Addr.render, hrender', hfullAddress, hinput]
      · simpa [sourceViewFull] using hrender'
      · simpa [sourceViewLeft] using hleft.symm
      · simpa [sourceViewRight] using hright.symm
      · simpa [sourceViewPrefix] using hpre.symm
    · refine ⟨⟨.full parts, some pre⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ⟨⟨hlength, hitems⟩, hprefix⟩
      · simp [IPv6.GrammarView.View.render, renderNet,
          IPv6.GrammarView.Addr.render, hrender', hfullAddress, hinput,
          String.append_assoc]
      · simpa [sourceViewFull] using hrender'
      · simpa [sourceViewLeft] using hleft.symm
      · simpa [sourceViewRight] using hright.symm
      · rfl
  · obtain ⟨leftParts, hleftLength, hleftItems, hleftRender⟩ :
        ∃ parts : List String,
          parts.length ≤ 7 ∧
            (∀ part ∈ parts, HexValid part) ∧
            renderGroups parts = left := by
      rcases hleft with hleft | hleft
      · exact ⟨[], by simp, by simp, by simp [renderGroups, hleft]⟩
      · rcases hleft with ⟨parts, _, hupper, hitems, hrender⟩
        exact ⟨parts, hupper, hitems,
          by simpa [renderGroups] using hrender.symm⟩
    obtain ⟨rightParts, hrightLength, hrightItems, hrightRender⟩ :
        ∃ parts : List String,
          parts.length ≤ 7 ∧
            (∀ part ∈ parts, HexValid part) ∧
            renderGroups parts = right := by
      rcases hright with hright | hright
      · exact ⟨[], by simp, by simp, by simp [renderGroups, hright]⟩
      · rcases hright with ⟨parts, _, hupper, hitems, hrender⟩
        exact ⟨parts, hupper, hitems,
          by simpa [renderGroups] using hrender.symm⟩
    rcases hnet with ⟨hpre, hinput⟩ | ⟨hprefix, hinput⟩
    · refine ⟨⟨.compressed leftParts rightParts, none⟩,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ⟨⟨hleftLength, hrightLength, hleftItems, hrightItems⟩,
          trivial⟩
      · simp [IPv6.GrammarView.View.render, renderNet,
          IPv6.GrammarView.Addr.render, hleftRender, hrightRender,
          haddress, hinput, String.append_assoc]
      · simpa [sourceViewFull] using hfull.symm
      · exact hleftRender
      · exact hrightRender
      · simpa [sourceViewPrefix] using hpre.symm
    · refine ⟨⟨.compressed leftParts rightParts, some pre⟩,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ⟨⟨hleftLength, hrightLength, hleftItems, hrightItems⟩,
          hprefix⟩
      · simp [IPv6.GrammarView.View.render, renderNet,
          IPv6.GrammarView.Addr.render, hleftRender, hrightRender,
          haddress, hinput, String.append_assoc]
      · simpa [sourceViewFull] using hfull.symm
      · exact hleftRender
      · exact hrightRender
      · rfl

theorem source_satisfies_wf_constraints_parts (input : String)
    (hwf : IPv6.IsWf.V6Net input) :
    IPv6.SatisfiesWfConstraints input ↔
      ∃ full left right pre : String,
        IPv6Parts input full left right pre ∧
          IPv6.WfConstraints left right pre := by
  have hengine : Triptych.IsWf IPv6.grammar input :=
    (IPv6.IsWfGrammar_equiv input).mpr hwf
  have hsome : (decode IPv6.grammar input).isSome = true :=
    (decodeSome_iff_IsWf IPv6.grammar (by decide) input).mpr hengine
  obtain ⟨captures, hdecodeInput⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨view, hcaptures, hrender, hsyntax⟩ :=
    decode_ipv6_sound hdecodeInput
  have hdecode :
      decode IPv6.grammar view.render = some view.captures := by
    rw [← hrender, ← hcaptures]
    exact hdecodeInput
  constructor
  · intro hconstraints
    have hparts :
        IPv6Parts input (sourceViewFull view) (sourceViewLeft view)
          (sourceViewRight view) (sourceViewPrefix view) := by
      rw [hrender]
      exact source_view_parts view hsyntax
    have hviewConstraints : view.Constraints :=
      (IPv6.GrammarView.constraints_of_decode view hdecode).1
        (by simpa [hrender] using hconstraints)
    refine ⟨sourceViewFull view, sourceViewLeft view,
      sourceViewRight view, sourceViewPrefix view, hparts, ?_⟩
    rw [← source_view_constraints]
    exact hviewConstraints
  · rintro ⟨full, left, right, pre, hparts, hconstraints⟩
    obtain ⟨view, hsyntax, hrender, hfull, hleft, hright, hpre⟩ :=
      source_view_of_parts input full left right pre hparts
    have hviewConstraints : view.Constraints := by
      rw [source_view_constraints, hleft, hright, hpre]
      exact hconstraints
    have hsurface :=
      (IPv6.GrammarView.constraints_of_decode view
        (decode_eq_of_view view hsyntax)).2 hviewConstraints
    simpa [hrender] using hsurface

theorem source_satisfies_constraints_parts (input : String)
    (hwf : IPv6.IsWf.V6Net input) :
    IPv6.SatisfiesConstraints input ↔
      ∃ full left right pre : String,
        IPv6Parts input full left right pre ∧
          IPv6.Constraints full left right pre := by
  have hengine : Triptych.IsWf IPv6.grammar input :=
    (IPv6.IsWfGrammar_equiv input).mpr hwf
  have hsome : (decode IPv6.grammar input).isSome = true :=
    (decodeSome_iff_IsWf IPv6.grammar (by decide) input).mpr hengine
  obtain ⟨captures, hdecodeInput⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨view, hcaptures, hrender, hsyntax⟩ :=
    decode_ipv6_sound hdecodeInput
  have hdecode :
      decode IPv6.grammar view.render = some view.captures := by
    rw [← hrender, ← hcaptures]
    exact hdecodeInput
  constructor
  · intro hconstraints
    have hparts :
        IPv6Parts input (sourceViewFull view) (sourceViewLeft view)
          (sourceViewRight view) (sourceViewPrefix view) := by
      rw [hrender]
      exact source_view_parts view hsyntax
    have hviewConstraints : view.ValueConstraints :=
      (IPv6.GrammarView.valueConstraints_of_decode view hdecode).1
        (by simpa [hrender] using hconstraints)
    refine ⟨sourceViewFull view, sourceViewLeft view,
      sourceViewRight view, sourceViewPrefix view, hparts, ?_⟩
    rw [← source_view_value_constraints]
    exact hviewConstraints
  · rintro ⟨full, left, right, pre, hparts, hconstraints⟩
    obtain ⟨view, hsyntax, hrender, hfull, hleft, hright, hpre⟩ :=
      source_view_of_parts input full left right pre hparts
    have hviewConstraints : view.ValueConstraints := by
      rw [source_view_value_constraints, hfull, hleft, hright, hpre]
      exact hconstraints
    have hsurface :=
      (IPv6.GrammarView.valueConstraints_of_decode view
        (decode_eq_of_view view hsyntax)).2 hviewConstraints
    simpa [hrender] using hsurface

theorem matched_compressed_fields
    (sequence : Vermilion.Seq Int)
    (view : triptych_ipv6_roundtrip.IPv6View)
    (hmatch :
      triptych_ipv6_roundtrip.ipv6_matches_Compressed sequence view) :
    ((view.get_IPv6View_left = Vermilion.Seq.empty) ∨
        triptych_ipv6_roundtrip.ipv6_is_wf_Left
          view.get_IPv6View_left) ∧
      ((view.get_IPv6View_right = Vermilion.Seq.empty) ∨
        triptych_ipv6_roundtrip.ipv6_is_wf_Right
          view.get_IPv6View_right) := by
  rcases hmatch with ⟨left, right, ⟨⟨_, hleft⟩, hright⟩⟩
  constructor
  · rcases hleft with ⟨_, hfield⟩ | ⟨hfield, hmatch⟩
    · exact Or.inl hfield
    · exact Or.inr (by
        rw [hfield]
        exact (matches_left_wf left view).1 hmatch)
  · rcases hright with ⟨_, hfield⟩ | ⟨hfield, hmatch⟩
    · exact Or.inl hfield
    · exact Or.inr (by
        rw [hfield]
        exact (matches_right_wf right view).1 hmatch)

theorem matched_address_fields
    (sequence : Vermilion.Seq Int)
    (view : triptych_ipv6_roundtrip.IPv6View)
    (hmatch :
      triptych_ipv6_roundtrip.ipv6_matches_V6Addr sequence view) :
    ((view.get_IPv6View_full = Vermilion.Seq.empty) ∨
        triptych_ipv6_roundtrip.ipv6_is_wf_Full
          view.get_IPv6View_full) ∧
      ((view.get_IPv6View_left = Vermilion.Seq.empty) ∨
        triptych_ipv6_roundtrip.ipv6_is_wf_Left
          view.get_IPv6View_left) ∧
      ((view.get_IPv6View_right = Vermilion.Seq.empty) ∨
        triptych_ipv6_roundtrip.ipv6_is_wf_Right
          view.get_IPv6View_right) := by
  rcases hmatch with
      ⟨full, ⟨⟨⟨_, hfield, hmatch⟩, hleft⟩, hright⟩⟩ |
      ⟨compressed, ⟨⟨_, hmatch⟩, hfull⟩⟩
  · refine ⟨Or.inr ?_, Or.inl hleft, Or.inl hright⟩
    rw [hfield]
    exact (matches_full_wf full view).1 hmatch
  · exact ⟨Or.inl hfull, matched_compressed_fields compressed view hmatch⟩

theorem matched_view_fields
    (sequence : Vermilion.Seq Int)
    (view : triptych_ipv6_roundtrip.IPv6View)
    (hmatch :
      triptych_ipv6_roundtrip.ipv6_matches_view sequence view) :
    ((view.get_IPv6View_full = Vermilion.Seq.empty) ∨
        triptych_ipv6_roundtrip.ipv6_is_wf_Full
          view.get_IPv6View_full) ∧
      ((view.get_IPv6View_left = Vermilion.Seq.empty) ∨
        triptych_ipv6_roundtrip.ipv6_is_wf_Left
          view.get_IPv6View_left) ∧
      ((view.get_IPv6View_right = Vermilion.Seq.empty) ∨
        triptych_ipv6_roundtrip.ipv6_is_wf_Right
          view.get_IPv6View_right) ∧
      ((view.get_IPv6View_prefix_ = Vermilion.Seq.empty) ∨
        triptych_ipv6_roundtrip.ipv6_is_wf_Prefix
          view.get_IPv6View_prefix_) := by
  rcases hmatch with ⟨_, hbare | hprefixed⟩
  · rcases hbare with ⟨address, ⟨⟨_, haddress⟩, hprefix⟩⟩
    rcases matched_address_fields address view haddress with
      ⟨hfull, hleft, hright⟩
    exact ⟨hfull, hleft, hright, Or.inl hprefix⟩
  · rcases hprefixed with
      ⟨address, pre, ⟨⟨_, haddress⟩, ⟨hfield, hmatch⟩⟩⟩
    rcases matched_address_fields address view haddress with
      ⟨hfull, hleft, hright⟩
    refine ⟨hfull, hleft, hright, Or.inr ?_⟩
    rw [hfield]
    exact (matches_prefix_wf pre view).1 hmatch

theorem empty_or_full_sequence_range
    (sequence : Vermilion.Seq Int)
    (hwf : sequence = Vermilion.Seq.empty ∨
      triptych_ipv6_roundtrip.ipv6_is_wf_Full sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  rcases hwf with rfl | hwf
  · exact empty_sequence_range Vermilion.Seq.empty (by
      simp [Vermilion.Seq.len, Vermilion.Seq.empty])
  · exact full_sequence_range sequence hwf

theorem empty_or_left_sequence_range
    (sequence : Vermilion.Seq Int)
    (hwf : sequence = Vermilion.Seq.empty ∨
      triptych_ipv6_roundtrip.ipv6_is_wf_Left sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  rcases hwf with rfl | hwf
  · exact empty_sequence_range Vermilion.Seq.empty (by
      simp [Vermilion.Seq.len, Vermilion.Seq.empty])
  · exact left_sequence_range sequence hwf

theorem empty_or_right_sequence_range
    (sequence : Vermilion.Seq Int)
    (hwf : sequence = Vermilion.Seq.empty ∨
      triptych_ipv6_roundtrip.ipv6_is_wf_Right sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  rcases hwf with rfl | hwf
  · exact empty_sequence_range Vermilion.Seq.empty (by
      simp [Vermilion.Seq.len, Vermilion.Seq.empty])
  · exact right_sequence_range sequence hwf

theorem empty_or_prefix_sequence_range
    (sequence : Vermilion.Seq Int)
    (hwf : sequence = Vermilion.Seq.empty ∨
      triptych_ipv6_roundtrip.ipv6_is_wf_Prefix sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  rcases hwf with rfl | hwf
  · exact empty_sequence_range Vermilion.Seq.empty (by
      simp [Vermilion.Seq.len, Vermilion.Seq.empty])
  · exact prefix_sequence_range sequence hwf

theorem normalize_matching_view (input : String)
    (condition : triptych_ipv6_roundtrip.IPv6View → Prop) :
    (∃ view : triptych_ipv6_roundtrip.IPv6View,
      triptych_ipv6_roundtrip.ipv6_matches_view (encodeString input) view ∧
        condition view) ↔
      ∃ full left right pre : String,
        triptych_ipv6_roundtrip.ipv6_matches_view (encodeString input)
            (.IPv6View (encodeString input) (encodeString full)
              (encodeString left) (encodeString right) (encodeString pre)) ∧
          condition
            (.IPv6View (encodeString input) (encodeString full)
              (encodeString left) (encodeString right) (encodeString pre)) := by
  constructor
  · rintro ⟨view, hmatch, hcondition⟩
    cases view with
    | IPv6View viewInput fullSequence leftSequence rightSequence
        prefixSequence =>
      have hfields := matched_view_fields (encodeString input)
        (.IPv6View viewInput fullSequence leftSequence rightSequence
          prefixSequence) hmatch
      have hinput : viewInput = encodeString input := hmatch.1
      let full := decodeSequence fullSequence
      let left := decodeSequence leftSequence
      let right := decodeSequence rightSequence
      let pre := decodeSequence prefixSequence
      have hfull : encodeString full = fullSequence :=
        encode_decode_sequence fullSequence
          (empty_or_full_sequence_range fullSequence hfields.1)
      have hleft : encodeString left = leftSequence :=
        encode_decode_sequence leftSequence
          (empty_or_left_sequence_range leftSequence hfields.2.1)
      have hright : encodeString right = rightSequence :=
        encode_decode_sequence rightSequence
          (empty_or_right_sequence_range rightSequence hfields.2.2.1)
      have hpre : encodeString pre = prefixSequence :=
        encode_decode_sequence prefixSequence
          (empty_or_prefix_sequence_range prefixSequence hfields.2.2.2)
      refine ⟨full, left, right, pre, ?_, ?_⟩
      · simpa only [hinput, hfull, hleft, hright, hpre] using hmatch
      · simpa only [hinput, hfull, hleft, hright, hpre] using hcondition
  · rintro ⟨full, left, right, pre, hmatch, hcondition⟩
    exact ⟨.IPv6View (encodeString input) (encodeString full)
      (encodeString left) (encodeString right) (encodeString pre),
      hmatch, hcondition⟩

theorem recoveredHexDigit_encode (character : Char) :
    triptych_ipv6_roundtrip.triptych_hex_digit_value
        (Int.ofNat character.toNat) =
      Triptych.hexDigitValueInt character := by
  simp [triptych_ipv6_roundtrip.triptych_hex_digit_value,
    Triptych.hexDigitValueInt, Vermilion.iteP]

theorem hexSeqFrom_eq_source
    (characters : List Char) (index : Nat)
    (accumulator current : Int) (hindex : index ≤ characters.length) :
    triptych_ipv6_roundtrip.triptych_hex_seq_from
        (characters.map (fun character => Int.ofNat character.toNat))
        (Int.ofNat index) accumulator current =
      Triptych.hexSeqOfChars (characters.drop index) accumulator current := by
  rw [triptych_ipv6_roundtrip.triptych_hex_seq_from]
  have hrange :
      (0 : Int) ≤
        Vermilion.Seq.len
            (characters.map (fun character => Int.ofNat character.toNat)) -
          Int.ofNat index := by
    simp only [Vermilion.Seq.len, List.length_map]
    exact Int.sub_nonneg.mpr ((Int.ofNat_le).2 hindex)
  rw [dif_pos hrange]
  by_cases hlt : index < characters.length
  · have hltInt :
        Int.ofNat index <
          Vermilion.Seq.len
            (characters.map (fun character => Int.ofNat character.toNat)) := by
      simp only [Vermilion.Seq.len, List.length_map]
      exact (Int.ofNat_lt).2 hlt
    rw [dif_pos hltInt]
    have hnext : index + 1 ≤ characters.length := by omega
    have hindexStep : Int.ofNat index + 1 = Int.ofNat (index + 1) := by simp
    rw [hindexStep]
    rw [index_encoded_characters characters index hlt]
    rw [List.drop_eq_getElem_cons hlt]
    by_cases hcolon : characters[index] = ':'
    · have hcode : Int.ofNat characters[index].toNat = 58 := by
        rw [hcolon]
        rfl
      rw [dif_pos hcode]
      simp only [Triptych.hexSeqOfChars, hcolon, if_pos]
      exact hexSeqFrom_eq_source characters (index + 1)
        (accumulator * 65536 + current) 0 hnext
    · have hcode : Int.ofNat characters[index].toNat ≠ 58 := by
        intro h
        apply hcolon
        apply Char.toNat_inj.mp
        exact Int.ofNat_inj.mp h
      rw [dif_neg hcode]
      simp only [Triptych.hexSeqOfChars, hcolon, if_false]
      rw [recoveredHexDigit_encode]
      exact hexSeqFrom_eq_source characters (index + 1)
        accumulator
        (current * 16 + Triptych.hexDigitValueInt characters[index]) hnext
  · have hltInt :
        ¬Int.ofNat index <
          Vermilion.Seq.len
            (characters.map (fun character => Int.ofNat character.toNat)) := by
      simp only [Vermilion.Seq.len, List.length_map]
      exact fun h => hlt ((Int.ofNat_lt).1 h)
    rw [dif_neg hltInt]
    have heq : index = characters.length :=
      Nat.le_antisymm hindex (Nat.le_of_not_gt hlt)
    simp [heq, Triptych.hexSeqOfChars]
termination_by characters.length - index
decreasing_by
  all_goals
    exact tsub_lt_tsub_left_of_le (Nat.succ_le_iff.mpr hlt)
      (Nat.lt_succ_self index)

theorem hexSeqOf_equiv (source : String) :
    triptych_ipv6_roundtrip.triptych_hex_seq_of (encodeString source) =
      Triptych.hexSeqOf source := by
  unfold triptych_ipv6_roundtrip.triptych_hex_seq_of encodeString
  change
    triptych_ipv6_roundtrip.triptych_hex_seq_from
        (source.toList.map (fun character => Int.ofNat character.toNat))
        (Int.ofNat 0) 0 0 =
      Triptych.hexSeqOfChars source.toList 0 0
  simpa using hexSeqFrom_eq_source source.toList 0 0 0 (Nat.zero_le _)

theorem segmentsFrom_eq_fold
    (characters : List Char) (index : Nat)
    (countValue : Int) (hindex : index ≤ characters.length) :
    triptych_ipv6_roundtrip.triptych_segments_from
        (characters.map (fun character => Int.ofNat character.toNat))
        (Int.ofNat index) countValue =
      (characters.drop index).foldl
        (fun current character =>
          if character = ':' then current + 1 else current)
        countValue := by
  rw [triptych_ipv6_roundtrip.triptych_segments_from]
  have hrange :
      (0 : Int) ≤
        Vermilion.Seq.len
            (characters.map (fun character => Int.ofNat character.toNat)) -
          Int.ofNat index := by
    simp only [Vermilion.Seq.len, List.length_map]
    exact Int.sub_nonneg.mpr ((Int.ofNat_le).2 hindex)
  rw [dif_pos hrange]
  by_cases hlt : index < characters.length
  · have hltInt :
        Int.ofNat index <
          Vermilion.Seq.len
            (characters.map (fun character => Int.ofNat character.toNat)) := by
      simp only [Vermilion.Seq.len, List.length_map]
      exact (Int.ofNat_lt).2 hlt
    rw [dif_pos hltInt]
    have hnext : index + 1 ≤ characters.length := by omega
    have hindexStep : Int.ofNat index + 1 = Int.ofNat (index + 1) := by simp
    rw [hindexStep]
    rw [index_encoded_characters characters index hlt]
    rw [List.drop_eq_getElem_cons hlt]
    simp only [List.foldl_cons]
    by_cases hcolon : characters[index] = ':'
    · have hcode : Int.ofNat characters[index].toNat = 58 := by
        rw [hcolon]
        rfl
      rw [dif_pos hcode, if_pos hcolon]
      exact segmentsFrom_eq_fold characters (index + 1)
        (countValue + 1) hnext
    · have hcode : Int.ofNat characters[index].toNat ≠ 58 := by
        intro h
        apply hcolon
        apply Char.toNat_inj.mp
        exact Int.ofNat_inj.mp h
      rw [dif_neg hcode, if_neg hcolon]
      exact segmentsFrom_eq_fold characters (index + 1)
        countValue hnext
  · have hltInt :
        ¬Int.ofNat index <
          Vermilion.Seq.len
            (characters.map (fun character => Int.ofNat character.toNat)) := by
      simp only [Vermilion.Seq.len, List.length_map]
      exact fun h => hlt ((Int.ofNat_lt).1 h)
    rw [dif_neg hltInt]
    have heq : index = characters.length :=
      Nat.le_antisymm hindex (Nat.le_of_not_gt hlt)
    simp [heq]
termination_by characters.length - index
decreasing_by
  all_goals
    exact tsub_lt_tsub_left_of_le (Nat.succ_le_iff.mpr hlt)
      (Nat.lt_succ_self index)

theorem segmentsOf_equiv (source : String) :
    triptych_ipv6_roundtrip.triptych_segments_of (encodeString source) =
      Triptych.segmentsOf source := by
  unfold triptych_ipv6_roundtrip.triptych_segments_of Triptych.segmentsOf
    encodeString
  change
    Vermilion.iteP
        (Vermilion.Seq.len
          (source.toList.map (fun character => Int.ofNat character.toNat)) = 0)
        0
        (triptych_ipv6_roundtrip.triptych_segments_from
          (source.toList.map (fun character => Int.ofNat character.toNat))
          (Int.ofNat 0) 1) =
      if source.toList.isEmpty then 0
      else source.toList.foldl
        (fun current character =>
          if character = ':' then current + 1 else current) 1
  rw [segmentsFrom_eq_fold source.toList 0 1 (Nat.zero_le _)]
  simp [Vermilion.Seq.len, Vermilion.iteP]

theorem natFrom_eq_fold (bytes : List Int) (index : Nat)
    (accumulator : Int) (hindex : index ≤ bytes.length) :
    triptych_ipv6_roundtrip.triptych_nat_of_from
        bytes (Int.ofNat index) accumulator =
      (bytes.drop index).foldl
        (fun current byte => current * 10 + recoveredDigit byte)
        accumulator := by
  apply Triptych.Vermilion.String.natFrom_eq_fold
    triptych_ipv6_roundtrip.triptych_nat_of_from
  · intro stepBytes stepIndex stepAccumulator hrange
    rw [triptych_ipv6_roundtrip.triptych_nat_of_from, dif_pos hrange]
    rfl
  · exact hindex

theorem natOf_equiv (source : String) :
    triptych_ipv6_roundtrip.triptych_nat_of (encodeString source) =
      Triptych.natOf source := by
  unfold triptych_ipv6_roundtrip.triptych_nat_of
  change triptych_ipv6_roundtrip.triptych_nat_of_from
      (encodeString source) (Int.ofNat 0) 0 = Triptych.natOf source
  rw [natFrom_eq_fold _ 0 0 (Nat.zero_le _)]
  simpa using encodedDigitFold_eq_natOf source

theorem intPow_equiv (base exponent : Int) :
    triptych_ipv6_roundtrip.triptych_int_pow base exponent =
      base ^ exponent.toNat := by
  rw [triptych_ipv6_roundtrip.triptych_int_pow]
  have hrange :
      0 ≤ Vermilion.iteP (exponent > 0) exponent 0 := by
    simp [Vermilion.iteP]
    split_ifs <;> omega
  rw [dif_pos hrange]
  by_cases hpositive : exponent > 0
  · rw [dif_pos hpositive, intPow_equiv]
    have hnat :
        exponent.toNat = (exponent - 1).toNat + 1 := by omega
    rw [hnat, pow_succ]
    ac_rfl
  · rw [dif_neg hpositive]
    have hnonpositive : exponent ≤ 0 := by omega
    simp [Int.toNat_of_nonpos hnonpositive]
termination_by exponent.toNat
decreasing_by omega

theorem ipv6_value_equiv
    (full left right pre : String) :
    IPv6.value full left right pre =
      triptych_ipv6_roundtrip.ipv6_value
        (encodeString full) (encodeString left) (encodeString right)
        (encodeString pre) := by
  unfold IPv6.value triptych_ipv6_roundtrip.ipv6_value
  rw [hexSeqOf_equiv, hexSeqOf_equiv, hexSeqOf_equiv,
    segmentsOf_equiv, natOf_equiv, intPow_equiv]
  simp [Vermilion.iteP, encodeString_inj_iff, encodeString,
    Vermilion.Seq.empty]

theorem ipv6_wf_constraints_equiv
    (left right pre : String) :
    IPv6.WfConstraints left right pre ↔
      triptych_ipv6_roundtrip.ipv6_wf_constraints
        (encodeString left) (encodeString right) (encodeString pre) := by
  unfold IPv6.WfConstraints triptych_ipv6_roundtrip.ipv6_wf_constraints
  rw [segmentsOf_equiv, segmentsOf_equiv, noLeadingZero_iff_encoded pre,
    natOf_equiv]

theorem ipv6_constraints_equiv
    (full left right pre : String) :
    IPv6.Constraints full left right pre ↔
      triptych_ipv6_roundtrip.ipv6_constraints
        (encodeString full) (encodeString left) (encodeString right)
        (encodeString pre) := by
  unfold IPv6.Constraints triptych_ipv6_roundtrip.ipv6_constraints
  rw [← ipv6_value_equiv full left right pre, intPow_equiv]

theorem ipv6_satisfies_wf_constraints_equiv (input : String)
    (hwf : IPv6.IsWf.V6Net input) :
    IPv6.SatisfiesWfConstraints input ↔
      triptych_ipv6_roundtrip.ipv6_satisfies_wf_constraints
        (encodeString input) := by
  rw [source_satisfies_wf_constraints_parts input hwf]
  unfold triptych_ipv6_roundtrip.ipv6_satisfies_wf_constraints
  rw [normalize_matching_view input
    triptych_ipv6_roundtrip.ipv6_view_wf_constraints]
  constructor
  · rintro ⟨full, left, right, pre, hparts, hconstraints⟩
    refine ⟨full, left, right, pre,
      (matches_view_equiv input full left right pre).2 hparts, ?_⟩
    change triptych_ipv6_roundtrip.ipv6_wf_constraints
      (encodeString left) (encodeString right) (encodeString pre)
    exact (ipv6_wf_constraints_equiv left right pre).1 hconstraints
  · rintro ⟨full, left, right, pre, hmatch, hconstraints⟩
    refine ⟨full, left, right, pre,
      (matches_view_equiv input full left right pre).1 hmatch, ?_⟩
    change triptych_ipv6_roundtrip.ipv6_wf_constraints
      (encodeString left) (encodeString right) (encodeString pre) at hconstraints
    exact (ipv6_wf_constraints_equiv left right pre).2 hconstraints

theorem ipv6_satisfies_constraints_equiv (input : String)
    (hwf : IPv6.IsWf.V6Net input) :
    IPv6.SatisfiesConstraints input ↔
      triptych_ipv6_roundtrip.ipv6_satisfies_constraints
        (encodeString input) := by
  rw [source_satisfies_constraints_parts input hwf]
  unfold triptych_ipv6_roundtrip.ipv6_satisfies_constraints
  rw [normalize_matching_view input
    triptych_ipv6_roundtrip.ipv6_view_constraints]
  constructor
  · rintro ⟨full, left, right, pre, hparts, hconstraints⟩
    refine ⟨full, left, right, pre,
      (matches_view_equiv input full left right pre).2 hparts, ?_⟩
    change triptych_ipv6_roundtrip.ipv6_constraints
      (encodeString full) (encodeString left) (encodeString right)
        (encodeString pre)
    exact (ipv6_constraints_equiv full left right pre).1 hconstraints
  · rintro ⟨full, left, right, pre, hmatch, hconstraints⟩
    refine ⟨full, left, right, pre,
      (matches_view_equiv input full left right pre).1 hmatch, ?_⟩
    change triptych_ipv6_roundtrip.ipv6_constraints
      (encodeString full) (encodeString left) (encodeString right)
        (encodeString pre) at hconstraints
    exact (ipv6_constraints_equiv full left right pre).2 hconstraints

theorem ipv6_is_wf_equiv (input : String) :
    IPv6.IsWf input ↔
      triptych_ipv6_roundtrip.ipv6_is_wf (encodeString input) := by
  change
    (IPv6.IsWf.V6Net input ∧ IPv6.SatisfiesWfConstraints input) ↔
      (triptych_ipv6_roundtrip.ipv6_is_wf_V6Net (encodeString input) ∧
        triptych_ipv6_roundtrip.ipv6_satisfies_wf_constraints
          (encodeString input))
  constructor
  · rintro ⟨hgrammar, hconstraints⟩
    exact ⟨(v6net_equiv input).1 hgrammar,
      (ipv6_satisfies_wf_constraints_equiv input hgrammar).1 hconstraints⟩
  · rintro ⟨hgrammar, hconstraints⟩
    have hsourceGrammar := (v6net_equiv input).2 hgrammar
    exact ⟨hsourceGrammar,
      (ipv6_satisfies_wf_constraints_equiv input hsourceGrammar).2
        hconstraints⟩

theorem ipv6_is_valid_equiv (input : String) :
    IPv6.IsValid input ↔
      triptych_ipv6_roundtrip.ipv6_is_valid (encodeString input) := by
  change
    (IPv6.IsWf input ∧ IPv6.SatisfiesConstraints input) ↔
      (triptych_ipv6_roundtrip.ipv6_is_wf (encodeString input) ∧
        triptych_ipv6_roundtrip.ipv6_satisfies_constraints
          (encodeString input))
  constructor
  · rintro ⟨hwellFormed, hconstraints⟩
    exact ⟨(ipv6_is_wf_equiv input).1 hwellFormed,
      (ipv6_satisfies_constraints_equiv input hwellFormed.1).1
        hconstraints⟩
  · rintro ⟨hwellFormed, hconstraints⟩
    have hsourceWf := (ipv6_is_wf_equiv input).2 hwellFormed
    exact ⟨hsourceWf,
      (ipv6_satisfies_constraints_equiv input hsourceWf.1).2 hconstraints⟩

theorem components_of_parts
    (input full left right pre : String)
    (hparts : IPv6Parts input full left right pre) :
    Triptych.component IPv6.grammar input "Full" = full ∧
      Triptych.component IPv6.grammar input "Left" = left ∧
      Triptych.component IPv6.grammar input "Right" = right ∧
      Triptych.component IPv6.grammar input "Prefix" = pre := by
  obtain ⟨view, hsyntax, hrender, hfull, hleft, hright, hpre⟩ :=
    source_view_of_parts input full left right pre hparts
  have hdecode :
      decode IPv6.grammar input = some view.captures := by
    rw [← hrender]
    exact IPv6.GrammarView.decode_eq_of_view view hsyntax
  have hcFull := Triptych.component_eq_of_decode hdecode "Full"
  rw [IPv6.GrammarView.captures_full_component] at hcFull
  have hcLeft := Triptych.component_eq_of_decode hdecode "Left"
  rw [IPv6.GrammarView.captures_left_component] at hcLeft
  have hcRight := Triptych.component_eq_of_decode hdecode "Right"
  rw [IPv6.GrammarView.captures_right_component] at hcRight
  have hcPre := Triptych.component_eq_of_decode hdecode "Prefix"
  rw [IPv6.GrammarView.captures_prefix] at hcPre
  exact ⟨hcFull.trans hfull, hcLeft.trans hleft, hcRight.trans hright,
    hcPre.trans hpre⟩

theorem compute_value_of_parts
    (input full left right pre : String)
    (hparts : IPv6Parts input full left right pre) :
    IPv6.computeValue input = some (IPv6.value full left right pre) := by
  obtain ⟨hfull, hleft, hright, hpre⟩ :=
    components_of_parts input full left right pre hparts
  have hgrammar : IPv6.IsWf.V6Net input :=
    (parts_exists_equiv input).2 ⟨full, left, right, pre, hparts⟩
  have hengine : Triptych.IsWf IPv6.grammar input :=
    (IPv6.IsWfGrammar_equiv input).mpr hgrammar
  have hsome : (decode IPv6.grammar input).isSome = true :=
    (decodeSome_iff_IsWf IPv6.grammar (by decide) input).mpr hengine
  obtain ⟨captures, hdecode⟩ := Option.isSome_iff_exists.mp hsome
  rw [IPv6.computeValue_eq, hdecode]
  simpa only [Option.map_some, hfull, hleft, hright, hpre]

theorem view_denotation_equiv :
    ∀ input s0 s1 s2 s3 : String, Recovered.ipv6_view_denotation (Recovered.mkIPv6View (encodeString input) (encodeString s0) (encodeString s1) (encodeString s2) (encodeString s3)) = IPv6.value s0 s1 s2 s3 := by
  intro input full left right pre
  exact (ipv6_value_equiv full left right pre).symm

theorem view_valid_equiv :
    ∀ input s0 s1 s2 s3 : String, Recovered.ipv6_view_valid (Recovered.mkIPv6View (encodeString input) (encodeString s0) (encodeString s1) (encodeString s2) (encodeString s3)) ↔ (IPv6.WfConstraints s1 s2 s3 ∧ IPv6.Constraints s0 s1 s2 s3) := by
  intro input full left right pre
  change
    (triptych_ipv6_roundtrip.ipv6_wf_constraints
          (encodeString left) (encodeString right) (encodeString pre) ∧
        triptych_ipv6_roundtrip.ipv6_constraints
          (encodeString full) (encodeString left) (encodeString right)
          (encodeString pre)) ↔ _
  rw [← ipv6_wf_constraints_equiv left right pre,
    ← ipv6_constraints_equiv full left right pre]

theorem matching_view_normalizes_equiv :
    ∀ input : String, ∀ view : Recovered.IPv6View,
      Recovered.ipv6_matches_view (encodeString input) view →
        ∃ full left right pre : String,
          view =
            Recovered.mkIPv6View (encodeString input) (encodeString full)
              (encodeString left) (encodeString right) (encodeString pre) := by
  intro input view hmatch
  obtain ⟨full, left, right, pre, _, heq⟩ :=
    (normalize_matching_view input (fun candidate => candidate = view)).1
      ⟨view, hmatch, rfl⟩
  exact ⟨full, left, right, pre, heq.symm⟩

theorem matches_view_exact_equiv :
    ∀ input full left right pre : String,
      Recovered.ipv6_matches_view (encodeString input)
          (Recovered.mkIPv6View (encodeString input) (encodeString full)
            (encodeString left) (encodeString right) (encodeString pre)) ↔
        ((((IPv6.IsWf.V6Net input ∧
                Triptych.component IPv6.grammar input "Full" = full) ∧
              Triptych.component IPv6.grammar input "Left" = left) ∧
            Triptych.component IPv6.grammar input "Right" = right) ∧
          Triptych.component IPv6.grammar input "Prefix" = pre) := by
  intro input full left right pre
  change
    triptych_ipv6_roundtrip.ipv6_matches_view (encodeString input)
        (.IPv6View (encodeString input) (encodeString full)
          (encodeString left) (encodeString right) (encodeString pre)) ↔ _
  rw [matches_view_equiv]
  constructor
  · intro hparts
    obtain ⟨hf, hl, hr, hp⟩ :=
      components_of_parts input full left right pre hparts
    exact ⟨⟨⟨⟨(parts_exists_equiv input).2
      ⟨full, left, right, pre, hparts⟩, hf⟩, hl⟩, hr⟩, hp⟩
  · rintro ⟨⟨⟨⟨hgrammar, hf⟩, hl⟩, hr⟩, hp⟩
    obtain ⟨full', left', right', pre', hparts⟩ :=
      (parts_exists_equiv input).1 hgrammar
    obtain ⟨hf', hl', hr', hp'⟩ :=
      components_of_parts input full' left' right' pre' hparts
    have ef : full' = full := hf'.symm.trans hf
    have el : left' = left := hl'.symm.trans hl
    have er : right' = right := hr'.symm.trans hr
    have ep : pre' = pre := hp'.symm.trans hp
    simpa only [ef, el, er, ep] using hparts

theorem matches_result_equiv :
    ∀ input : String, ∀ result : Int,
      (IPv6.IsValid input ∧ IPv6.computeValue input = some result) ↔
        Recovered.ipv6_matches_result (encodeString input) result := by
  intro input result
  change
    (IPv6.IsValid input ∧ IPv6.computeValue input = some result) ↔
      triptych_ipv6_roundtrip.ipv6_matches_result
        (encodeString input) result
  unfold triptych_ipv6_roundtrip.ipv6_matches_result
  constructor
  · rintro ⟨⟨⟨hgrammar, hsourceWf⟩, hsourceConstraints⟩, hcompute⟩
    obtain ⟨full, left, right, pre, hparts⟩ :=
      (parts_exists_equiv input).1 hgrammar
    obtain ⟨hf, hl, hr, hp⟩ :=
      components_of_parts input full left right pre hparts
    have hwfConstraints : IPv6.WfConstraints left right pre := by
      unfold IPv6.SatisfiesWfConstraints at hsourceWf
      simpa only [hl, hr, hp] using hsourceWf
    have hconstraints : IPv6.Constraints full left right pre := by
      unfold IPv6.SatisfiesConstraints at hsourceConstraints
      simpa only [hf, hl, hr, hp] using hsourceConstraints
    have hvalue : IPv6.value full left right pre = result := by
      rw [compute_value_of_parts input full left right pre hparts] at hcompute
      exact Option.some.inj hcompute
    let view :=
      triptych_ipv6_roundtrip.IPv6View.IPv6View (encodeString input)
        (encodeString full) (encodeString left) (encodeString right)
        (encodeString pre)
    refine ⟨view, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · exact (matches_view_equiv input full left right pre).2 hparts
    · exact (view_valid_equiv input full left right pre).2
        ⟨hwfConstraints, hconstraints⟩
    · exact (view_denotation_equiv input full left right pre).trans hvalue
  · rintro ⟨view, ⟨⟨hmatch, hviewValid⟩, hdenotation⟩⟩
    obtain ⟨full, left, right, pre, heq⟩ :=
      matching_view_normalizes_equiv input view hmatch
    subst view
    have hparts := (matches_view_equiv input full left right pre).1 hmatch
    obtain ⟨hf, hl, hr, hp⟩ :=
      components_of_parts input full left right pre hparts
    obtain ⟨hwfConstraints, hconstraints⟩ :=
      (view_valid_equiv input full left right pre).1 hviewValid
    have hgrammar : IPv6.IsWf.V6Net input :=
      (parts_exists_equiv input).2 ⟨full, left, right, pre, hparts⟩
    have hsatisfiesWf : IPv6.SatisfiesWfConstraints input := by
      unfold IPv6.SatisfiesWfConstraints
      simpa only [hl, hr, hp] using hwfConstraints
    have hsatisfies : IPv6.SatisfiesConstraints input := by
      unfold IPv6.SatisfiesConstraints
      simpa only [hf, hl, hr, hp] using hconstraints
    have hvalue : IPv6.value full left right pre = result :=
      (view_denotation_equiv input full left right pre).symm.trans hdenotation
    refine ⟨⟨⟨hgrammar, hsatisfiesWf⟩, hsatisfies⟩, ?_⟩
    rw [compute_value_of_parts input full left right pre hparts]
    exact congrArg some hvalue

end Triptych.Vermilion.Proofs.IPv6
