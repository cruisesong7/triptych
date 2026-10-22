import TriptychVermilionGenerated.IPv4
import Proofs.IPv4.GrammarView
import Triptych.Backend.Verus.AstSemantics

namespace Triptych.Vermilion.Proofs.IPv4

open Triptych
open Triptych.Vermilion.String
open Triptych.Vermilion.Generated.IPv4
open IPv4.GrammarView

theorem digits_between_equiv (lower upper : Nat) (source : String) :
    IsDigitsBetween lower upper source ↔
      ∃ digits : Vermilion.Seq Int,
        encodeString source = digits ∧
          ((Int.ofNat lower ≤ Vermilion.Seq.len digits ∧
              Vermilion.Seq.len digits ≤ Int.ofNat upper) ∧
            ∀ index : Int,
              0 ≤ index ∧ index < Vermilion.Seq.len digits →
                triptych_ipv4_roundtrip.triptych_is_digit
                  (Vermilion.Seq.index digits index)) := by
  simpa [triptych_ipv4_roundtrip.triptych_is_digit, IsDigitCode] using
    digitsBetween_iff_encoded lower upper source

theorem oct1_equiv (source : String) :
    IPv4.IsWf.Oct1 source ↔
      triptych_ipv4_roundtrip.ipv4_is_wf_Oct1 (encodeString source) := by
  simpa [IPv4.IsWf.Oct1, triptych_ipv4_roundtrip.ipv4_is_wf_Oct1] using
    digits_between_equiv 1 3 source

theorem oct2_equiv (source : String) :
    IPv4.IsWf.Oct2 source ↔
      triptych_ipv4_roundtrip.ipv4_is_wf_Oct2 (encodeString source) := by
  simpa [IPv4.IsWf.Oct2, triptych_ipv4_roundtrip.ipv4_is_wf_Oct2] using
    digits_between_equiv 1 3 source

theorem oct3_equiv (source : String) :
    IPv4.IsWf.Oct3 source ↔
      triptych_ipv4_roundtrip.ipv4_is_wf_Oct3 (encodeString source) := by
  simpa [IPv4.IsWf.Oct3, triptych_ipv4_roundtrip.ipv4_is_wf_Oct3] using
    digits_between_equiv 1 3 source

theorem oct4_equiv (source : String) :
    IPv4.IsWf.Oct4 source ↔
      triptych_ipv4_roundtrip.ipv4_is_wf_Oct4 (encodeString source) := by
  simpa [IPv4.IsWf.Oct4, triptych_ipv4_roundtrip.ipv4_is_wf_Oct4] using
    digits_between_equiv 1 3 source

theorem prefix_equiv (source : String) :
    IPv4.IsWf.Prefix source ↔
      triptych_ipv4_roundtrip.ipv4_is_wf_Prefix (encodeString source) := by
  simpa [IPv4.IsWf.Prefix, triptych_ipv4_roundtrip.ipv4_is_wf_Prefix] using
    digits_between_equiv 1 2 source

theorem digit_sequence_range
    (sequence : Vermilion.Seq Int) (lower upper : Int)
    (hwf :
      ∃ digits : Vermilion.Seq Int,
        sequence = digits ∧
          ((lower ≤ Vermilion.Seq.len digits ∧
              Vermilion.Seq.len digits ≤ upper) ∧
            ∀ index : Int,
              0 ≤ index ∧ index < Vermilion.Seq.len digits →
                triptych_ipv4_roundtrip.triptych_is_digit
                  (Vermilion.Seq.index digits index))) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  apply digit_witness_sequence_range sequence
    (fun digits =>
      (lower ≤ Vermilion.Seq.len digits ∧
        Vermilion.Seq.len digits ≤ upper))
  simpa [triptych_ipv4_roundtrip.triptych_is_digit, IsDigitCode] using hwf

theorem oct1_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv4_roundtrip.ipv4_is_wf_Oct1 sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  apply digit_sequence_range sequence 1 3
  simpa [triptych_ipv4_roundtrip.ipv4_is_wf_Oct1] using hwf

theorem oct2_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv4_roundtrip.ipv4_is_wf_Oct2 sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  apply digit_sequence_range sequence 1 3
  simpa [triptych_ipv4_roundtrip.ipv4_is_wf_Oct2] using hwf

theorem oct3_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv4_roundtrip.ipv4_is_wf_Oct3 sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  apply digit_sequence_range sequence 1 3
  simpa [triptych_ipv4_roundtrip.ipv4_is_wf_Oct3] using hwf

theorem oct4_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv4_roundtrip.ipv4_is_wf_Oct4 sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  apply digit_sequence_range sequence 1 3
  simpa [triptych_ipv4_roundtrip.ipv4_is_wf_Oct4] using hwf

theorem prefix_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv4_roundtrip.ipv4_is_wf_Prefix sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  apply digit_sequence_range sequence 1 2
  simpa [triptych_ipv4_roundtrip.ipv4_is_wf_Prefix] using hwf

theorem decode_v4addr_wf (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv4_roundtrip.ipv4_is_wf_V4Addr sequence) :
    ∃ oct1 oct2 oct3 oct4 : String,
      sequence = encodeString (oct1 ++ "." ++ oct2 ++ "." ++ oct3 ++ "." ++ oct4) ∧
        IPv4.IsWf.Oct1 oct1 ∧ IPv4.IsWf.Oct2 oct2 ∧
          IPv4.IsWf.Oct3 oct3 ∧ IPv4.IsWf.Oct4 oct4 := by
  rcases hwf with ⟨oct1Sequence, oct2Sequence, oct3Sequence, oct4Sequence,
    ⟨⟨⟨⟨hsequence, hoct1⟩, hoct2⟩, hoct3⟩, hoct4⟩⟩
  let oct1 := decodeSequence oct1Sequence
  let oct2 := decodeSequence oct2Sequence
  let oct3 := decodeSequence oct3Sequence
  let oct4 := decodeSequence oct4Sequence
  have hoct1Encode : encodeString oct1 = oct1Sequence :=
    encode_decode_sequence oct1Sequence (oct1_sequence_range oct1Sequence hoct1)
  have hoct2Encode : encodeString oct2 = oct2Sequence :=
    encode_decode_sequence oct2Sequence (oct2_sequence_range oct2Sequence hoct2)
  have hoct3Encode : encodeString oct3 = oct3Sequence :=
    encode_decode_sequence oct3Sequence (oct3_sequence_range oct3Sequence hoct3)
  have hoct4Encode : encodeString oct4 = oct4Sequence :=
    encode_decode_sequence oct4Sequence (oct4_sequence_range oct4Sequence hoct4)
  refine ⟨oct1, oct2, oct3, oct4, ?_, ?_, ?_, ?_, ?_⟩
  · rw [encodeString_append, encodeString_append, encodeString_append,
      encodeString_append, encodeString_append, encodeString_append,
      hoct1Encode, hoct2Encode, hoct3Encode, hoct4Encode]
    simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
      Vermilion.Seq.empty] using hsequence
  · exact (oct1_equiv oct1).2 (by simpa [hoct1Encode] using hoct1)
  · exact (oct2_equiv oct2).2 (by simpa [hoct2Encode] using hoct2)
  · exact (oct3_equiv oct3).2 (by simpa [hoct3Encode] using hoct3)
  · exact (oct4_equiv oct4).2 (by simpa [hoct4Encode] using hoct4)

theorem v4addr_equiv (source : String) :
    IPv4.IsWf.V4Addr source ↔
      triptych_ipv4_roundtrip.ipv4_is_wf_V4Addr (encodeString source) := by
  constructor
  · rintro ⟨oct1, oct2, oct3, oct4,
      ⟨⟨⟨⟨hsource, hoct1⟩, hoct2⟩, hoct3⟩, hoct4⟩⟩
    refine ⟨encodeString oct1, encodeString oct2, encodeString oct3,
      encodeString oct4, ?_⟩
    refine ⟨⟨⟨⟨?_, (oct1_equiv oct1).1 hoct1⟩,
      (oct2_equiv oct2).1 hoct2⟩, (oct3_equiv oct3).1 hoct3⟩,
      (oct4_equiv oct4).1 hoct4⟩
    simpa [encodeString_append, encodeString, Vermilion.Seq.add,
      Vermilion.Seq.push, Vermilion.Seq.empty] using congrArg encodeString hsource
  · intro hwf
    obtain ⟨oct1, oct2, oct3, oct4, hsource, hoct1, hoct2, hoct3, hoct4⟩ :=
      decode_v4addr_wf (encodeString source) hwf
    refine ⟨oct1, oct2, oct3, oct4,
      ⟨⟨⟨⟨?_, hoct1⟩, hoct2⟩, hoct3⟩, hoct4⟩⟩
    exact encodeString_injective hsource

theorem decode_prefix_wf (sequence : Vermilion.Seq Int)
    (hwf : triptych_ipv4_roundtrip.ipv4_is_wf_Prefix sequence) :
    ∃ pre : String,
      sequence = encodeString pre ∧ IPv4.IsWf.Prefix pre := by
  let pre := decodeSequence sequence
  have hprefixEncode : encodeString pre = sequence :=
    encode_decode_sequence sequence (prefix_sequence_range sequence hwf)
  exact ⟨pre, hprefixEncode.symm,
    (prefix_equiv pre).2 (by simpa [hprefixEncode] using hwf)⟩

theorem v4net_equiv (source : String) :
    IPv4.IsWf.V4Net source ↔
      triptych_ipv4_roundtrip.ipv4_is_wf_V4Net (encodeString source) := by
  unfold IPv4.IsWf.V4Net IPv4.Production
  constructor
  · rintro (haddr | ⟨addr, pre, ⟨hsource, haddr⟩, hprefix⟩)
    · exact Or.inl ⟨encodeString source, rfl, (v4addr_equiv source).1 haddr⟩
    · refine Or.inr ⟨encodeString addr, encodeString pre, ?_⟩
      refine ⟨⟨?_, (v4addr_equiv addr).1 haddr⟩,
        (prefix_equiv pre).1 hprefix⟩
      simpa [encodeString_append, encodeString, Vermilion.Seq.add,
        Vermilion.Seq.push, Vermilion.Seq.empty] using
          congrArg encodeString hsource
  · rintro (⟨addrSequence, hsource, haddr⟩ |
      ⟨addrSequence, prefixSequence, ⟨⟨hsource, haddr⟩, hprefix⟩⟩)
    · subst addrSequence
      exact Or.inl ((v4addr_equiv source).2 haddr)
    · obtain ⟨oct1, oct2, oct3, oct4, haddrSequence,
        hoct1, hoct2, hoct3, hoct4⟩ :=
        decode_v4addr_wf addrSequence haddr
      obtain ⟨pre, hprefixSequence, hprefixWf⟩ :=
        decode_prefix_wf prefixSequence hprefix
      let addr := oct1 ++ "." ++ oct2 ++ "." ++ oct3 ++ "." ++ oct4
      have hsourceText : source = addr ++ "/" ++ pre := by
        apply encodeString_injective
        rw [encodeString_append, encodeString_append, haddrSequence.symm,
          hprefixSequence.symm]
        simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
          Vermilion.Seq.empty] using hsource
      have haddrWf : IPv4.IsWf.V4Addr addr :=
        ⟨oct1, oct2, oct3, oct4,
          ⟨⟨⟨⟨rfl, hoct1⟩, hoct2⟩, hoct3⟩, hoct4⟩⟩
      exact Or.inr ⟨addr, pre, ⟨hsourceText, haddrWf⟩, hprefixWf⟩

theorem natFrom_eq_fold (bytes : List Int) (index : Nat)
    (accumulator : Int) (hindex : index ≤ bytes.length) :
    triptych_ipv4_roundtrip.triptych_nat_of_from
        bytes (Int.ofNat index) accumulator =
      (bytes.drop index).foldl
        (fun current byte => current * 10 + recoveredDigit byte)
        accumulator := by
  apply Triptych.Vermilion.String.natFrom_eq_fold
    triptych_ipv4_roundtrip.triptych_nat_of_from
  · intro stepBytes stepIndex stepAccumulator hrange
    rw [triptych_ipv4_roundtrip.triptych_nat_of_from, dif_pos hrange]
    rfl
  · exact hindex

theorem natOf_equiv (source : String) :
    triptych_ipv4_roundtrip.triptych_nat_of (encodeString source) =
      Triptych.natOf source := by
  unfold triptych_ipv4_roundtrip.triptych_nat_of
  change triptych_ipv4_roundtrip.triptych_nat_of_from
      (encodeString source) (Int.ofNat 0) 0 = Triptych.natOf source
  rw [natFrom_eq_fold _ 0 0 (Nat.zero_le _)]
  simpa using encodedDigitFold_eq_natOf source

theorem ipv4_value_equiv
    (oct1 oct2 oct3 oct4 pre : String) :
    IPv4.value oct1 oct2 oct3 oct4 pre =
      triptych_ipv4_roundtrip.ipv4_value
        (encodeString oct1) (encodeString oct2) (encodeString oct3)
        (encodeString oct4) (encodeString pre) := by
  unfold IPv4.value triptych_ipv4_roundtrip.ipv4_value
  rw [natOf_equiv, natOf_equiv, natOf_equiv, natOf_equiv, natOf_equiv]
  simp [Vermilion.iteP, encodeString_inj_iff, encodeString,
    Vermilion.Seq.empty]

theorem ipv4_wf_constraints_equiv
    (oct1 oct2 oct3 oct4 pre : String) :
    IPv4.WfConstraints oct1 oct2 oct3 oct4 pre ↔
      triptych_ipv4_roundtrip.ipv4_wf_constraints
        (encodeString oct1) (encodeString oct2) (encodeString oct3)
        (encodeString oct4) (encodeString pre) := by
  unfold IPv4.WfConstraints triptych_ipv4_roundtrip.ipv4_wf_constraints
  rw [noLeadingZero_iff_encoded oct1, noLeadingZero_iff_encoded oct2,
    noLeadingZero_iff_encoded oct3, noLeadingZero_iff_encoded oct4,
    noLeadingZero_iff_encoded pre]
  rw [natOf_equiv, natOf_equiv, natOf_equiv, natOf_equiv, natOf_equiv]

set_option maxRecDepth 10000 in
theorem intPow_two_thirty_two :
    triptych_ipv4_roundtrip.triptych_int_pow 2 32 =
      (2 : Int) ^ 32 := by
  norm_num [triptych_ipv4_roundtrip.triptych_int_pow, Vermilion.iteP]

theorem ipv4_constraints_equiv
    (oct1 oct2 oct3 oct4 pre : String) :
    IPv4.Constraints oct1 oct2 oct3 oct4 pre ↔
      triptych_ipv4_roundtrip.ipv4_constraints
        (encodeString oct1) (encodeString oct2) (encodeString oct3)
        (encodeString oct4) (encodeString pre) := by
  unfold IPv4.Constraints triptych_ipv4_roundtrip.ipv4_constraints
  rw [← ipv4_value_equiv oct1 oct2 oct3 oct4 pre,
    intPow_two_thirty_two]
  norm_num

def ipv4Parts
    (input oct1 oct2 oct3 oct4 pre : String) : Prop :=
  IPv4.IsWf.Oct1 oct1 ∧ IPv4.IsWf.Oct2 oct2 ∧
    IPv4.IsWf.Oct3 oct3 ∧ IPv4.IsWf.Oct4 oct4 ∧
      ((pre = "" ∧ input = renderV4 oct1 oct2 oct3 oct4 none) ∨
        (IPv4.IsWf.Prefix pre ∧
          input = renderV4 oct1 oct2 oct3 oct4 (some pre)))

theorem matches_address_equiv
    (sequence : Vermilion.Seq Int)
    (input oct1 oct2 oct3 oct4 pre : String) :
    triptych_ipv4_roundtrip.ipv4_matches_V4Addr sequence
        (.IPv4View (encodeString input) (encodeString oct1)
          (encodeString oct2) (encodeString oct3) (encodeString oct4)
          (encodeString pre)) ↔
      sequence =
          encodeString (oct1 ++ "." ++ oct2 ++ "." ++ oct3 ++ "." ++ oct4) ∧
        IPv4.IsWf.Oct1 oct1 ∧ IPv4.IsWf.Oct2 oct2 ∧
          IPv4.IsWf.Oct3 oct3 ∧ IPv4.IsWf.Oct4 oct4 := by
  constructor
  · rintro ⟨oct1Sequence, oct2Sequence, oct3Sequence, oct4Sequence,
      ⟨⟨⟨⟨hsequence, ⟨hoct1Field, hoct1⟩⟩,
        ⟨hoct2Field, hoct2⟩⟩, ⟨hoct3Field, hoct3⟩⟩,
        ⟨hoct4Field, hoct4⟩⟩⟩
    simp only [
      triptych_ipv4_roundtrip.IPv4View.get_IPv4View_oct1] at hoct1Field
    simp only [
      triptych_ipv4_roundtrip.IPv4View.get_IPv4View_oct2] at hoct2Field
    simp only [
      triptych_ipv4_roundtrip.IPv4View.get_IPv4View_oct3] at hoct3Field
    simp only [
      triptych_ipv4_roundtrip.IPv4View.get_IPv4View_oct4] at hoct4Field
    subst oct1Sequence
    subst oct2Sequence
    subst oct3Sequence
    subst oct4Sequence
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [encodeString_append, encodeString_append, encodeString_append,
        encodeString_append, encodeString_append, encodeString_append]
      simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
        Vermilion.Seq.empty] using hsequence
    · exact (oct1_equiv oct1).2 (by
        simpa [triptych_ipv4_roundtrip.ipv4_matches_Oct1,
          triptych_ipv4_roundtrip.ipv4_is_wf_Oct1] using hoct1)
    · exact (oct2_equiv oct2).2 (by
        simpa [triptych_ipv4_roundtrip.ipv4_matches_Oct2,
          triptych_ipv4_roundtrip.ipv4_is_wf_Oct2] using hoct2)
    · exact (oct3_equiv oct3).2 (by
        simpa [triptych_ipv4_roundtrip.ipv4_matches_Oct3,
          triptych_ipv4_roundtrip.ipv4_is_wf_Oct3] using hoct3)
    · exact (oct4_equiv oct4).2 (by
        simpa [triptych_ipv4_roundtrip.ipv4_matches_Oct4,
          triptych_ipv4_roundtrip.ipv4_is_wf_Oct4] using hoct4)
  · rintro ⟨hsequence, hoct1, hoct2, hoct3, hoct4⟩
    refine ⟨encodeString oct1, encodeString oct2, encodeString oct3,
      encodeString oct4, ?_⟩
    refine ⟨⟨⟨⟨?_, ⟨rfl, ?_⟩⟩, ⟨rfl, ?_⟩⟩,
      ⟨rfl, ?_⟩⟩, ⟨rfl, ?_⟩⟩
    · rw [encodeString_append, encodeString_append, encodeString_append,
        encodeString_append, encodeString_append, encodeString_append] at hsequence
      simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
        Vermilion.Seq.empty] using hsequence
    · simpa [triptych_ipv4_roundtrip.ipv4_matches_Oct1,
        triptych_ipv4_roundtrip.ipv4_is_wf_Oct1] using
          (oct1_equiv oct1).1 hoct1
    · simpa [triptych_ipv4_roundtrip.ipv4_matches_Oct2,
        triptych_ipv4_roundtrip.ipv4_is_wf_Oct2] using
          (oct2_equiv oct2).1 hoct2
    · simpa [triptych_ipv4_roundtrip.ipv4_matches_Oct3,
        triptych_ipv4_roundtrip.ipv4_is_wf_Oct3] using
          (oct3_equiv oct3).1 hoct3
    · simpa [triptych_ipv4_roundtrip.ipv4_matches_Oct4,
        triptych_ipv4_roundtrip.ipv4_is_wf_Oct4] using
          (oct4_equiv oct4).1 hoct4

theorem matches_view_equiv
    (input oct1 oct2 oct3 oct4 pre : String) :
    triptych_ipv4_roundtrip.ipv4_matches_view (encodeString input)
        (.IPv4View (encodeString input) (encodeString oct1)
          (encodeString oct2) (encodeString oct3) (encodeString oct4)
          (encodeString pre)) ↔
      ipv4Parts input oct1 oct2 oct3 oct4 pre := by
  constructor
  · rintro ⟨_, hbare | hprefixed⟩
    · rcases hbare with ⟨addrSequence, ⟨⟨hinput, haddr⟩, hprefix⟩⟩
      have haddr' :=
        (matches_address_equiv addrSequence input oct1 oct2 oct3 oct4 pre).1
          haddr
      simp only [
        triptych_ipv4_roundtrip.IPv4View.get_IPv4View_prefix_] at hprefix
      refine ⟨haddr'.2.1, haddr'.2.2.1, haddr'.2.2.2.1,
        haddr'.2.2.2.2, Or.inl ⟨?_, ?_⟩⟩
      · exact encodeString_injective (by
          simpa [encodeString, Vermilion.Seq.empty] using hprefix)
      · unfold renderV4
        apply encodeString_injective
        rw [hinput, haddr'.1]
        simp [encodeString_append, encodeString, Vermilion.Seq.empty]
    · rcases hprefixed with
        ⟨addrSequence, prefixSequence,
          ⟨⟨hinput, haddr⟩, ⟨hprefixField, hprefixMatch⟩⟩⟩
      have haddr' :=
        (matches_address_equiv addrSequence input oct1 oct2 oct3 oct4 pre).1
          haddr
      simp only [
        triptych_ipv4_roundtrip.IPv4View.get_IPv4View_prefix_] at hprefixField
      subst prefixSequence
      have hprefixWf : IPv4.IsWf.Prefix pre := by
        apply (prefix_equiv pre).2
        simpa [triptych_ipv4_roundtrip.ipv4_matches_Prefix,
          triptych_ipv4_roundtrip.ipv4_is_wf_Prefix] using hprefixMatch
      refine ⟨haddr'.2.1, haddr'.2.2.1, haddr'.2.2.2.1,
        haddr'.2.2.2.2, Or.inr ⟨hprefixWf, ?_⟩⟩
      unfold renderV4
      apply encodeString_injective
      rw [hinput, haddr'.1]
      simp [encodeString_append, encodeString, Vermilion.Seq.add,
        Vermilion.Seq.push, Vermilion.Seq.empty]
  · rintro ⟨hoct1, hoct2, hoct3, hoct4,
      ⟨hprefix, hinput⟩ | ⟨hprefixWf, hinput⟩⟩
    · subst pre
      refine ⟨rfl, Or.inl
        ⟨encodeString (oct1 ++ "." ++ oct2 ++ "." ++ oct3 ++ "." ++ oct4),
          ?_⟩⟩
      refine ⟨⟨?_, (matches_address_equiv _ input oct1 oct2 oct3 oct4 "").2
        ⟨rfl, hoct1, hoct2, hoct3, hoct4⟩⟩, ?_⟩
      · unfold renderV4 at hinput
        simpa [encodeString_append, encodeString, Vermilion.Seq.empty] using
          congrArg encodeString hinput
      · rfl
    · refine ⟨rfl, Or.inr
        ⟨encodeString (oct1 ++ "." ++ oct2 ++ "." ++ oct3 ++ "." ++ oct4),
          encodeString pre, ?_⟩⟩
      refine ⟨⟨?_, (matches_address_equiv _ input oct1 oct2 oct3 oct4 pre).2
        ⟨rfl, hoct1, hoct2, hoct3, hoct4⟩⟩, ⟨rfl, ?_⟩⟩
      · unfold renderV4 at hinput
        simpa [encodeString_append, encodeString, Vermilion.Seq.add,
          Vermilion.Seq.push, Vermilion.Seq.empty] using
            congrArg encodeString hinput
      · simpa [triptych_ipv4_roundtrip.ipv4_matches_Prefix,
          triptych_ipv4_roundtrip.ipv4_is_wf_Prefix] using
            (prefix_equiv pre).1 hprefixWf

theorem parts_exists_equiv (input : String) :
    IPv4.IsWf.V4Net input ↔
      ∃ oct1 oct2 oct3 oct4 pre : String,
        ipv4Parts input oct1 oct2 oct3 oct4 pre := by
  unfold IPv4.IsWf.V4Net IPv4.Production
  constructor
  · rintro (⟨oct1, oct2, oct3, oct4,
      ⟨⟨⟨⟨hinput, hoct1⟩, hoct2⟩, hoct3⟩, hoct4⟩⟩ |
      ⟨addr, pre, ⟨hinput, ⟨oct1, oct2, oct3, oct4,
        ⟨⟨⟨⟨haddr, hoct1⟩, hoct2⟩, hoct3⟩, hoct4⟩⟩⟩, hprefix⟩)
    · refine ⟨oct1, oct2, oct3, oct4, "", hoct1, hoct2, hoct3, hoct4,
        Or.inl ⟨rfl, ?_⟩⟩
      simpa [renderV4, String.append_assoc] using hinput
    · refine ⟨oct1, oct2, oct3, oct4, pre, hoct1, hoct2, hoct3, hoct4,
        Or.inr ⟨hprefix, ?_⟩⟩
      rw [hinput, haddr]
      simp [renderV4, String.append_assoc]
  · rintro ⟨oct1, oct2, oct3, oct4, pre,
      hoct1, hoct2, hoct3, hoct4,
      ⟨rfl, hinput⟩ | ⟨hprefix, hinput⟩⟩
    · left
      refine ⟨oct1, oct2, oct3, oct4,
        ⟨⟨⟨⟨?_, hoct1⟩, hoct2⟩, hoct3⟩, hoct4⟩⟩
      simpa [renderV4, String.append_assoc] using hinput
    · right
      let addr := oct1 ++ "." ++ oct2 ++ "." ++ oct3 ++ "." ++ oct4
      refine ⟨addr, pre, ⟨?_, ?_⟩, hprefix⟩
      · simpa [addr, renderV4, String.append_assoc] using hinput
      · exact ⟨oct1, oct2, oct3, oct4,
          ⟨⟨⟨⟨rfl, hoct1⟩, hoct2⟩, hoct3⟩, hoct4⟩⟩

theorem matching_view_exists_equiv (input : String) :
    IPv4.IsWf.V4Net input ↔
      ∃ oct1 oct2 oct3 oct4 pre : String,
        triptych_ipv4_roundtrip.ipv4_matches_view (encodeString input)
          (.IPv4View (encodeString input) (encodeString oct1)
            (encodeString oct2) (encodeString oct3) (encodeString oct4)
            (encodeString pre)) := by
  rw [parts_exists_equiv]
  apply exists_congr
  intro oct1
  apply exists_congr
  intro oct2
  apply exists_congr
  intro oct3
  apply exists_congr
  intro oct4
  apply exists_congr
  intro pre
  exact (matches_view_equiv input oct1 oct2 oct3 oct4 pre).symm

theorem components_of_parts
    (input oct1 oct2 oct3 oct4 pre : String)
    (hparts : ipv4Parts input oct1 oct2 oct3 oct4 pre) :
    Triptych.component IPv4.grammar input "Oct1" = oct1 ∧
      Triptych.component IPv4.grammar input "Oct2" = oct2 ∧
      Triptych.component IPv4.grammar input "Oct3" = oct3 ∧
      Triptych.component IPv4.grammar input "Oct4" = oct4 ∧
      Triptych.component IPv4.grammar input "Prefix" = pre := by
  rcases hparts with ⟨hoct1, hoct2, hoct3, hoct4,
    ⟨rfl, hinput⟩ | ⟨hprefix, hinput⟩⟩
  · have hdecode :=
      IPv4.GrammarView.decode_eq_of_parts (pre := none) hinput
        hoct1 hoct2 hoct3 hoct4 (by trivial)
    simp only [Triptych.component_eq_of_decode hdecode]
    simp [v4NetCaptures, v4AddrCaptures, CaptureMap.toEnv]
  · have hprefix' : OptionalPrefixSyntax (some pre) := by
      simpa [OptionalPrefixSyntax, IPv4.IsWf.Prefix] using hprefix
    have hdecode :=
      IPv4.GrammarView.decode_eq_of_parts (pre := some pre) hinput
        hoct1 hoct2 hoct3 hoct4 hprefix'
    simp only [Triptych.component_eq_of_decode hdecode]
    simp [v4NetCaptures, v4AddrCaptures, CaptureMap.toEnv]

theorem compute_value_of_parts
    (input oct1 oct2 oct3 oct4 pre : String)
    (hparts : ipv4Parts input oct1 oct2 oct3 oct4 pre) :
    IPv4.computeValue input = some (IPv4.value oct1 oct2 oct3 oct4 pre) := by
  obtain ⟨h1, h2, h3, h4, hp⟩ :=
    components_of_parts input oct1 oct2 oct3 oct4 pre hparts
  have hgrammar : IPv4.IsWf.V4Net input :=
    (parts_exists_equiv input).2
      ⟨oct1, oct2, oct3, oct4, pre, hparts⟩
  have hengine : Triptych.IsWf IPv4.grammar input :=
    (IPv4.IsWfGrammar_equiv input).mpr hgrammar
  have hsome : (decode IPv4.grammar input).isSome = true :=
    (decodeSome_iff_IsWf IPv4.grammar (by decide) input).mpr hengine
  obtain ⟨captures, hdecode⟩ := Option.isSome_iff_exists.mp hsome
  rw [IPv4.computeValue_eq, hdecode]
  simpa only [Option.map_some, h1, h2, h3, h4, hp]

theorem view_octets_wf
    (sequence : Vermilion.Seq Int)
    (view : triptych_ipv4_roundtrip.IPv4View)
    (hmatch : triptych_ipv4_roundtrip.ipv4_matches_V4Addr sequence view) :
    triptych_ipv4_roundtrip.ipv4_is_wf_Oct1
        (triptych_ipv4_roundtrip.IPv4View.get_IPv4View_oct1 view) ∧
      triptych_ipv4_roundtrip.ipv4_is_wf_Oct2
        (triptych_ipv4_roundtrip.IPv4View.get_IPv4View_oct2 view) ∧
      triptych_ipv4_roundtrip.ipv4_is_wf_Oct3
        (triptych_ipv4_roundtrip.IPv4View.get_IPv4View_oct3 view) ∧
      triptych_ipv4_roundtrip.ipv4_is_wf_Oct4
        (triptych_ipv4_roundtrip.IPv4View.get_IPv4View_oct4 view) := by
  rcases hmatch with ⟨oct1, oct2, oct3, oct4,
    ⟨⟨⟨⟨_, ⟨hoct1Field, hoct1⟩⟩, ⟨hoct2Field, hoct2⟩⟩,
      ⟨hoct3Field, hoct3⟩⟩, ⟨hoct4Field, hoct4⟩⟩⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hoct1Field]
    simpa [triptych_ipv4_roundtrip.ipv4_matches_Oct1,
      triptych_ipv4_roundtrip.ipv4_is_wf_Oct1] using hoct1
  · rw [hoct2Field]
    simpa [triptych_ipv4_roundtrip.ipv4_matches_Oct2,
      triptych_ipv4_roundtrip.ipv4_is_wf_Oct2] using hoct2
  · rw [hoct3Field]
    simpa [triptych_ipv4_roundtrip.ipv4_matches_Oct3,
      triptych_ipv4_roundtrip.ipv4_is_wf_Oct3] using hoct3
  · rw [hoct4Field]
    simpa [triptych_ipv4_roundtrip.ipv4_matches_Oct4,
      triptych_ipv4_roundtrip.ipv4_is_wf_Oct4] using hoct4

theorem normalize_matching_view (input : String)
    (condition : triptych_ipv4_roundtrip.IPv4View → Prop) :
    (∃ view : triptych_ipv4_roundtrip.IPv4View,
      triptych_ipv4_roundtrip.ipv4_matches_view (encodeString input) view ∧
        condition view) ↔
      ∃ oct1 oct2 oct3 oct4 pre : String,
        triptych_ipv4_roundtrip.ipv4_matches_view (encodeString input)
            (.IPv4View (encodeString input) (encodeString oct1)
              (encodeString oct2) (encodeString oct3) (encodeString oct4)
              (encodeString pre)) ∧
          condition
            (.IPv4View (encodeString input) (encodeString oct1)
              (encodeString oct2) (encodeString oct3) (encodeString oct4)
              (encodeString pre)) := by
  constructor
  · rintro ⟨view, hmatch, hcondition⟩
    cases view with
    | IPv4View viewInput oct1Sequence oct2Sequence oct3Sequence oct4Sequence
        prefixSequence =>
      rcases hmatch with ⟨hviewInput, hbare | hprefixed⟩
      change viewInput = encodeString input at hviewInput
      have hconditionCanonical :
          condition
            (.IPv4View (encodeString input) oct1Sequence oct2Sequence
              oct3Sequence oct4Sequence prefixSequence) := by
        rw [← hviewInput]
        exact hcondition
      subst viewInput
      rcases hbare with
        ⟨addrSequence, ⟨⟨hinput, haddrMatch⟩, hprefixField⟩⟩
      · have hoctets := view_octets_wf addrSequence
          (.IPv4View (encodeString input) oct1Sequence oct2Sequence
            oct3Sequence oct4Sequence prefixSequence) haddrMatch
        let oct1 := decodeSequence oct1Sequence
        let oct2 := decodeSequence oct2Sequence
        let oct3 := decodeSequence oct3Sequence
        let oct4 := decodeSequence oct4Sequence
        have hoct1Encode : encodeString oct1 = oct1Sequence :=
          encode_decode_sequence oct1Sequence
            (oct1_sequence_range oct1Sequence hoctets.1)
        have hoct2Encode : encodeString oct2 = oct2Sequence :=
          encode_decode_sequence oct2Sequence
            (oct2_sequence_range oct2Sequence hoctets.2.1)
        have hoct3Encode : encodeString oct3 = oct3Sequence :=
          encode_decode_sequence oct3Sequence
            (oct3_sequence_range oct3Sequence hoctets.2.2.1)
        have hoct4Encode : encodeString oct4 = oct4Sequence :=
          encode_decode_sequence oct4Sequence
            (oct4_sequence_range oct4Sequence hoctets.2.2.2)
        change prefixSequence = Vermilion.Seq.empty at hprefixField
        have hprefixEncode : encodeString "" = prefixSequence := by
          simpa [encodeString, Vermilion.Seq.empty] using hprefixField.symm
        refine ⟨oct1, oct2, oct3, oct4, "", ?_, ?_⟩
        · simpa only [hoct1Encode, hoct2Encode, hoct3Encode, hoct4Encode,
            hprefixEncode] using
              ⟨rfl, Or.inl
                ⟨addrSequence, ⟨⟨hinput, haddrMatch⟩, hprefixField⟩⟩⟩
        · simpa only [hoct1Encode, hoct2Encode, hoct3Encode, hoct4Encode,
            hprefixEncode] using hconditionCanonical
      · rcases hprefixed with
          ⟨addrSequence, prefixWitness,
            ⟨⟨hinput, haddrMatch⟩, ⟨hprefixField, hprefixMatch⟩⟩⟩
        change viewInput = encodeString input at hviewInput
        have hconditionCanonical :
            condition
              (.IPv4View (encodeString input) oct1Sequence oct2Sequence
                oct3Sequence oct4Sequence prefixSequence) := by
          rw [← hviewInput]
          exact hcondition
        subst viewInput
        have hoctets := view_octets_wf addrSequence
          (.IPv4View (encodeString input) oct1Sequence oct2Sequence
            oct3Sequence oct4Sequence prefixSequence) haddrMatch
        have hprefixWf :
            triptych_ipv4_roundtrip.ipv4_is_wf_Prefix prefixSequence := by
          change prefixSequence = prefixWitness at hprefixField
          rw [hprefixField]
          simpa [triptych_ipv4_roundtrip.ipv4_matches_Prefix,
            triptych_ipv4_roundtrip.ipv4_is_wf_Prefix] using hprefixMatch
        let oct1 := decodeSequence oct1Sequence
        let oct2 := decodeSequence oct2Sequence
        let oct3 := decodeSequence oct3Sequence
        let oct4 := decodeSequence oct4Sequence
        let pre := decodeSequence prefixSequence
        have hoct1Encode : encodeString oct1 = oct1Sequence :=
          encode_decode_sequence oct1Sequence
            (oct1_sequence_range oct1Sequence hoctets.1)
        have hoct2Encode : encodeString oct2 = oct2Sequence :=
          encode_decode_sequence oct2Sequence
            (oct2_sequence_range oct2Sequence hoctets.2.1)
        have hoct3Encode : encodeString oct3 = oct3Sequence :=
          encode_decode_sequence oct3Sequence
            (oct3_sequence_range oct3Sequence hoctets.2.2.1)
        have hoct4Encode : encodeString oct4 = oct4Sequence :=
          encode_decode_sequence oct4Sequence
            (oct4_sequence_range oct4Sequence hoctets.2.2.2)
        have hprefixEncode : encodeString pre = prefixSequence :=
          encode_decode_sequence prefixSequence
            (prefix_sequence_range prefixSequence hprefixWf)
        refine ⟨oct1, oct2, oct3, oct4, pre, ?_, ?_⟩
        · simpa only [hoct1Encode, hoct2Encode, hoct3Encode, hoct4Encode,
            hprefixEncode] using
              ⟨rfl, Or.inr
                ⟨addrSequence, prefixWitness,
                  ⟨⟨hinput, haddrMatch⟩, ⟨hprefixField, hprefixMatch⟩⟩⟩⟩
        · simpa only [hoct1Encode, hoct2Encode, hoct3Encode, hoct4Encode,
            hprefixEncode] using hconditionCanonical
  · rintro ⟨oct1, oct2, oct3, oct4, pre, hmatch, hcondition⟩
    exact ⟨.IPv4View (encodeString input) (encodeString oct1)
      (encodeString oct2) (encodeString oct3) (encodeString oct4)
      (encodeString pre), hmatch, hcondition⟩

theorem wf_constraints_of_decode
    (input oct1 oct2 oct3 oct4 : String) (pre : Option String)
    (hdecode :
      decode IPv4.grammar input =
        some (v4NetCaptures oct1 oct2 oct3 oct4 pre)) :
    IPv4.SatisfiesWfConstraints input ↔
      IPv4.WfConstraints oct1 oct2 oct3 oct4 (pre.getD "") := by
  rw [IPv4.SatisfiesWfConstraints_of_decode hdecode]
  cases pre <;>
    simp [v4NetCaptures, v4AddrCaptures, CaptureMap.toEnv]

theorem constraints_of_decode
    (input oct1 oct2 oct3 oct4 : String) (pre : Option String)
    (hdecode :
      decode IPv4.grammar input =
        some (v4NetCaptures oct1 oct2 oct3 oct4 pre)) :
    IPv4.SatisfiesConstraints input ↔
      IPv4.Constraints oct1 oct2 oct3 oct4 (pre.getD "") := by
  rw [IPv4.SatisfiesConstraints_of_decode hdecode]
  cases pre <;>
    simp [v4NetCaptures, v4AddrCaptures, CaptureMap.toEnv]

theorem decoded_parts_eq
    (input decoded1 decoded2 decoded3 decoded4 : String)
    (decodedPrefix : Option String)
    (hdecodedInput :
      input = renderV4 decoded1 decoded2 decoded3 decoded4 decodedPrefix)
    (hdecoded1 : IsDigitsBetween 1 3 decoded1)
    (hdecoded2 : IsDigitsBetween 1 3 decoded2)
    (hdecoded3 : IsDigitsBetween 1 3 decoded3)
    (hdecoded4 : IsDigitsBetween 1 3 decoded4)
    (hdecodedPrefix : OptionalPrefixSyntax decodedPrefix)
    (oct1 oct2 oct3 oct4 pre : String)
    (hparts : ipv4Parts input oct1 oct2 oct3 oct4 pre) :
    decoded1 = oct1 ∧ decoded2 = oct2 ∧ decoded3 = oct3 ∧ decoded4 = oct4 ∧
      decodedPrefix.getD "" = pre := by
  rcases hparts with ⟨hoct1, hoct2, hoct3, hoct4,
    ⟨rfl, hinput⟩ | ⟨hprefix, hinput⟩⟩
  · have hunique := renderV4_injective hdecoded1 hdecoded2 hdecoded3 hdecoded4
      hoct1 hoct2 hoct3 hoct4 hdecodedPrefix (by trivial)
      (hdecodedInput.symm.trans hinput)
    rcases hunique with ⟨h1, h2, h3, h4, hp⟩
    exact ⟨h1, h2, h3, h4, by simp [hp]⟩
  · have hunique := renderV4_injective hdecoded1 hdecoded2 hdecoded3 hdecoded4
      (pre₂ := some pre) hoct1 hoct2 hoct3 hoct4 hdecodedPrefix
      (by
        unfold OptionalPrefixSyntax
        simpa only [IPv4.IsWf.Prefix] using hprefix)
      (hdecodedInput.symm.trans hinput)
    rcases hunique with ⟨h1, h2, h3, h4, hp⟩
    exact ⟨h1, h2, h3, h4, by simpa [hp]⟩

theorem source_satisfies_wf_constraints_parts (input : String)
    (hwf : IPv4.IsWf.V4Net input) :
    IPv4.SatisfiesWfConstraints input ↔
      ∃ oct1 oct2 oct3 oct4 pre : String,
        ipv4Parts input oct1 oct2 oct3 oct4 pre ∧
          IPv4.WfConstraints oct1 oct2 oct3 oct4 pre := by
  obtain ⟨decoded1, decoded2, decoded3, decoded4, decodedPrefix,
    hdecode, hdecodedInput, hdecoded1, hdecoded2, hdecoded3, hdecoded4,
    hdecodedPrefix⟩ := decode_parts_of_surface_wf hwf
  constructor
  · intro hconstraints
    cases decodedPrefix with
    | none =>
        refine ⟨decoded1, decoded2, decoded3, decoded4, "",
          ⟨hdecoded1, hdecoded2, hdecoded3, hdecoded4,
            Or.inl ⟨rfl, hdecodedInput⟩⟩, ?_⟩
        exact (wf_constraints_of_decode input decoded1 decoded2 decoded3 decoded4
          none hdecode).1 hconstraints
    | some decodedPrefix =>
        refine ⟨decoded1, decoded2, decoded3, decoded4, decodedPrefix,
          ⟨hdecoded1, hdecoded2, hdecoded3, hdecoded4,
            Or.inr ⟨hdecodedPrefix, hdecodedInput⟩⟩, ?_⟩
        exact (wf_constraints_of_decode input decoded1 decoded2 decoded3 decoded4
          (some decodedPrefix) hdecode).1 hconstraints
  · rintro ⟨oct1, oct2, oct3, oct4, pre, hparts, hconstraints⟩
    have hunique := decoded_parts_eq input decoded1 decoded2 decoded3 decoded4
      decodedPrefix hdecodedInput hdecoded1 hdecoded2 hdecoded3 hdecoded4
      hdecodedPrefix oct1 oct2 oct3 oct4 pre hparts
    rcases hunique with ⟨rfl, rfl, rfl, rfl, hprefix⟩
    apply (wf_constraints_of_decode input decoded1 decoded2 decoded3 decoded4
      decodedPrefix hdecode).2
    rw [hprefix]
    exact hconstraints

theorem source_satisfies_constraints_parts (input : String)
    (hwf : IPv4.IsWf.V4Net input) :
    IPv4.SatisfiesConstraints input ↔
      ∃ oct1 oct2 oct3 oct4 pre : String,
        ipv4Parts input oct1 oct2 oct3 oct4 pre ∧
          IPv4.Constraints oct1 oct2 oct3 oct4 pre := by
  obtain ⟨decoded1, decoded2, decoded3, decoded4, decodedPrefix,
    hdecode, hdecodedInput, hdecoded1, hdecoded2, hdecoded3, hdecoded4,
    hdecodedPrefix⟩ := decode_parts_of_surface_wf hwf
  constructor
  · intro hconstraints
    cases decodedPrefix with
    | none =>
        refine ⟨decoded1, decoded2, decoded3, decoded4, "",
          ⟨hdecoded1, hdecoded2, hdecoded3, hdecoded4,
            Or.inl ⟨rfl, hdecodedInput⟩⟩, ?_⟩
        exact (constraints_of_decode input decoded1 decoded2 decoded3 decoded4
          none hdecode).1 hconstraints
    | some decodedPrefix =>
        refine ⟨decoded1, decoded2, decoded3, decoded4, decodedPrefix,
          ⟨hdecoded1, hdecoded2, hdecoded3, hdecoded4,
            Or.inr ⟨hdecodedPrefix, hdecodedInput⟩⟩, ?_⟩
        exact (constraints_of_decode input decoded1 decoded2 decoded3 decoded4
          (some decodedPrefix) hdecode).1 hconstraints
  · rintro ⟨oct1, oct2, oct3, oct4, pre, hparts, hconstraints⟩
    have hunique := decoded_parts_eq input decoded1 decoded2 decoded3 decoded4
      decodedPrefix hdecodedInput hdecoded1 hdecoded2 hdecoded3 hdecoded4
      hdecodedPrefix oct1 oct2 oct3 oct4 pre hparts
    rcases hunique with ⟨rfl, rfl, rfl, rfl, hprefix⟩
    apply (constraints_of_decode input decoded1 decoded2 decoded3 decoded4
      decodedPrefix hdecode).2
    rw [hprefix]
    exact hconstraints

theorem ipv4_satisfies_wf_constraints_equiv (input : String)
    (hwf : IPv4.IsWf.V4Net input) :
    IPv4.SatisfiesWfConstraints input ↔
      triptych_ipv4_roundtrip.ipv4_satisfies_wf_constraints
        (encodeString input) := by
  rw [source_satisfies_wf_constraints_parts input hwf]
  unfold triptych_ipv4_roundtrip.ipv4_satisfies_wf_constraints
  rw [normalize_matching_view input
    triptych_ipv4_roundtrip.ipv4_view_wf_constraints]
  constructor
  · rintro ⟨oct1, oct2, oct3, oct4, pre, hparts, hconstraints⟩
    refine ⟨oct1, oct2, oct3, oct4, pre,
      (matches_view_equiv input oct1 oct2 oct3 oct4 pre).2 hparts, ?_⟩
    change triptych_ipv4_roundtrip.ipv4_wf_constraints
      (encodeString oct1) (encodeString oct2) (encodeString oct3)
      (encodeString oct4) (encodeString pre)
    exact (ipv4_wf_constraints_equiv oct1 oct2 oct3 oct4 pre).1 hconstraints
  · rintro ⟨oct1, oct2, oct3, oct4, pre, hmatch, hconstraints⟩
    refine ⟨oct1, oct2, oct3, oct4, pre,
      (matches_view_equiv input oct1 oct2 oct3 oct4 pre).1 hmatch, ?_⟩
    change triptych_ipv4_roundtrip.ipv4_wf_constraints
      (encodeString oct1) (encodeString oct2) (encodeString oct3)
      (encodeString oct4) (encodeString pre) at hconstraints
    exact (ipv4_wf_constraints_equiv oct1 oct2 oct3 oct4 pre).2 hconstraints

theorem ipv4_satisfies_constraints_equiv (input : String)
    (hwf : IPv4.IsWf.V4Net input) :
    IPv4.SatisfiesConstraints input ↔
      triptych_ipv4_roundtrip.ipv4_satisfies_constraints
        (encodeString input) := by
  rw [source_satisfies_constraints_parts input hwf]
  unfold triptych_ipv4_roundtrip.ipv4_satisfies_constraints
  rw [normalize_matching_view input
    triptych_ipv4_roundtrip.ipv4_view_constraints]
  constructor
  · rintro ⟨oct1, oct2, oct3, oct4, pre, hparts, hconstraints⟩
    refine ⟨oct1, oct2, oct3, oct4, pre,
      (matches_view_equiv input oct1 oct2 oct3 oct4 pre).2 hparts, ?_⟩
    change triptych_ipv4_roundtrip.ipv4_constraints
      (encodeString oct1) (encodeString oct2) (encodeString oct3)
      (encodeString oct4) (encodeString pre)
    exact (ipv4_constraints_equiv oct1 oct2 oct3 oct4 pre).1 hconstraints
  · rintro ⟨oct1, oct2, oct3, oct4, pre, hmatch, hconstraints⟩
    refine ⟨oct1, oct2, oct3, oct4, pre,
      (matches_view_equiv input oct1 oct2 oct3 oct4 pre).1 hmatch, ?_⟩
    change triptych_ipv4_roundtrip.ipv4_constraints
      (encodeString oct1) (encodeString oct2) (encodeString oct3)
      (encodeString oct4) (encodeString pre) at hconstraints
    exact (ipv4_constraints_equiv oct1 oct2 oct3 oct4 pre).2 hconstraints

theorem ipv4_is_wf_equiv (input : String) :
    IPv4.IsWf input ↔
      triptych_ipv4_roundtrip.ipv4_is_wf (encodeString input) := by
  change
    (IPv4.IsWf.V4Net input ∧ IPv4.SatisfiesWfConstraints input) ↔
      (triptych_ipv4_roundtrip.ipv4_is_wf_V4Net (encodeString input) ∧
        triptych_ipv4_roundtrip.ipv4_satisfies_wf_constraints
          (encodeString input))
  constructor
  · rintro ⟨hgrammar, hconstraints⟩
    exact ⟨(v4net_equiv input).1 hgrammar,
      (ipv4_satisfies_wf_constraints_equiv input hgrammar).1 hconstraints⟩
  · rintro ⟨hgrammar, hconstraints⟩
    have hsourceGrammar := (v4net_equiv input).2 hgrammar
    exact ⟨hsourceGrammar,
      (ipv4_satisfies_wf_constraints_equiv input hsourceGrammar).2 hconstraints⟩

theorem ipv4_is_valid_equiv (input : String) :
    IPv4.IsValid input ↔
      triptych_ipv4_roundtrip.ipv4_is_valid (encodeString input) := by
  change
    (IPv4.IsWf input ∧ IPv4.SatisfiesConstraints input) ↔
      (triptych_ipv4_roundtrip.ipv4_is_wf (encodeString input) ∧
        triptych_ipv4_roundtrip.ipv4_satisfies_constraints
          (encodeString input))
  constructor
  · rintro ⟨hwellFormed, hconstraints⟩
    exact ⟨(ipv4_is_wf_equiv input).1 hwellFormed,
      (ipv4_satisfies_constraints_equiv input hwellFormed.1).1 hconstraints⟩
  · rintro ⟨hwellFormed, hconstraints⟩
    have hsourceWf := (ipv4_is_wf_equiv input).2 hwellFormed
    exact ⟨hsourceWf,
      (ipv4_satisfies_constraints_equiv input hsourceWf.1).2 hconstraints⟩

theorem view_denotation_equiv :
    ∀ input oct1 oct2 oct3 oct4 pre : String,
      Recovered.ipv4_view_denotation
          (Recovered.mkIPv4View (encodeString input) (encodeString oct1)
            (encodeString oct2) (encodeString oct3) (encodeString oct4)
            (encodeString pre)) =
        IPv4.value oct1 oct2 oct3 oct4 pre := by
  intro input oct1 oct2 oct3 oct4 pre
  exact (ipv4_value_equiv oct1 oct2 oct3 oct4 pre).symm

theorem view_valid_equiv :
    ∀ input oct1 oct2 oct3 oct4 pre : String,
      Recovered.ipv4_view_valid
          (Recovered.mkIPv4View (encodeString input) (encodeString oct1)
            (encodeString oct2) (encodeString oct3) (encodeString oct4)
            (encodeString pre)) ↔
        (IPv4.WfConstraints oct1 oct2 oct3 oct4 pre ∧
          IPv4.Constraints oct1 oct2 oct3 oct4 pre) := by
  intro input oct1 oct2 oct3 oct4 pre
  change
    (triptych_ipv4_roundtrip.ipv4_wf_constraints
          (encodeString oct1) (encodeString oct2) (encodeString oct3)
          (encodeString oct4) (encodeString pre) ∧
        triptych_ipv4_roundtrip.ipv4_constraints
          (encodeString oct1) (encodeString oct2) (encodeString oct3)
          (encodeString oct4) (encodeString pre)) ↔ _
  rw [← ipv4_wf_constraints_equiv oct1 oct2 oct3 oct4 pre,
    ← ipv4_constraints_equiv oct1 oct2 oct3 oct4 pre]

theorem matching_view_normalizes_equiv :
    ∀ input : String, ∀ view : Recovered.IPv4View,
      Recovered.ipv4_matches_view (encodeString input) view →
        ∃ oct1 oct2 oct3 oct4 pre : String,
          view =
            Recovered.mkIPv4View (encodeString input) (encodeString oct1)
              (encodeString oct2) (encodeString oct3) (encodeString oct4)
              (encodeString pre) := by
  intro input view hmatch
  obtain ⟨oct1, oct2, oct3, oct4, pre, _, heq⟩ :=
    (normalize_matching_view input (fun candidate => candidate = view)).1
      ⟨view, hmatch, rfl⟩
  exact ⟨oct1, oct2, oct3, oct4, pre, heq.symm⟩

theorem matches_view_exact_equiv :
    ∀ input oct1 oct2 oct3 oct4 pre : String,
      Recovered.ipv4_matches_view (encodeString input)
          (Recovered.mkIPv4View (encodeString input) (encodeString oct1)
            (encodeString oct2) (encodeString oct3) (encodeString oct4)
            (encodeString pre)) ↔
        (((((IPv4.IsWf.V4Net input ∧
                Triptych.component IPv4.grammar input "Oct1" = oct1) ∧
              Triptych.component IPv4.grammar input "Oct2" = oct2) ∧
            Triptych.component IPv4.grammar input "Oct3" = oct3) ∧
          Triptych.component IPv4.grammar input "Oct4" = oct4) ∧
        Triptych.component IPv4.grammar input "Prefix" = pre) := by
  intro input oct1 oct2 oct3 oct4 pre
  change
    triptych_ipv4_roundtrip.ipv4_matches_view (encodeString input)
        (.IPv4View (encodeString input) (encodeString oct1)
          (encodeString oct2) (encodeString oct3) (encodeString oct4)
          (encodeString pre)) ↔ _
  rw [matches_view_equiv]
  constructor
  · intro hparts
    obtain ⟨h1, h2, h3, h4, hp⟩ :=
      components_of_parts input oct1 oct2 oct3 oct4 pre hparts
    exact ⟨⟨⟨⟨⟨(parts_exists_equiv input).2
      ⟨oct1, oct2, oct3, oct4, pre, hparts⟩, h1⟩, h2⟩, h3⟩, h4⟩, hp⟩
  · rintro ⟨⟨⟨⟨⟨hgrammar, h1⟩, h2⟩, h3⟩, h4⟩, hp⟩
    obtain ⟨decoded1, decoded2, decoded3, decoded4, decodedPre, hparts⟩ :=
      (parts_exists_equiv input).1 hgrammar
    obtain ⟨hd1, hd2, hd3, hd4, hdp⟩ :=
      components_of_parts input decoded1 decoded2 decoded3 decoded4
        decodedPre hparts
    have heq1 : decoded1 = oct1 := hd1.symm.trans h1
    have heq2 : decoded2 = oct2 := hd2.symm.trans h2
    have heq3 : decoded3 = oct3 := hd3.symm.trans h3
    have heq4 : decoded4 = oct4 := hd4.symm.trans h4
    have heqp : decodedPre = pre := hdp.symm.trans hp
    simpa only [heq1, heq2, heq3, heq4, heqp] using hparts

theorem matches_result_equiv :
    ∀ input : String, ∀ result : Int,
      (IPv4.IsValid input ∧ IPv4.computeValue input = some result) ↔
        Recovered.ipv4_matches_result (encodeString input) result := by
  intro input result
  change
    (IPv4.IsValid input ∧ IPv4.computeValue input = some result) ↔
      triptych_ipv4_roundtrip.ipv4_matches_result
        (encodeString input) result
  unfold triptych_ipv4_roundtrip.ipv4_matches_result
  constructor
  · rintro ⟨⟨⟨hgrammar, hsourceWf⟩, hsourceConstraints⟩, hcompute⟩
    obtain ⟨oct1, oct2, oct3, oct4, pre, hparts⟩ :=
      (parts_exists_equiv input).1 hgrammar
    obtain ⟨h1, h2, h3, h4, hp⟩ :=
      components_of_parts input oct1 oct2 oct3 oct4 pre hparts
    have hwfConstraints :
        IPv4.WfConstraints oct1 oct2 oct3 oct4 pre := by
      unfold IPv4.SatisfiesWfConstraints at hsourceWf
      simpa only [h1, h2, h3, h4, hp] using hsourceWf
    have hconstraints :
        IPv4.Constraints oct1 oct2 oct3 oct4 pre := by
      unfold IPv4.SatisfiesConstraints at hsourceConstraints
      simpa only [h1, h2, h3, h4, hp] using hsourceConstraints
    have hvalue : IPv4.value oct1 oct2 oct3 oct4 pre = result := by
      rw [compute_value_of_parts input oct1 oct2 oct3 oct4 pre hparts]
        at hcompute
      exact Option.some.inj hcompute
    let view :=
      triptych_ipv4_roundtrip.IPv4View.IPv4View (encodeString input)
        (encodeString oct1) (encodeString oct2) (encodeString oct3)
        (encodeString oct4) (encodeString pre)
    refine ⟨view, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · exact (matches_view_equiv input oct1 oct2 oct3 oct4 pre).2 hparts
    · exact (view_valid_equiv input oct1 oct2 oct3 oct4 pre).2
        ⟨hwfConstraints, hconstraints⟩
    · exact (view_denotation_equiv input oct1 oct2 oct3 oct4 pre).trans hvalue
  · rintro ⟨view, ⟨⟨hmatch, hviewValid⟩, hdenotation⟩⟩
    obtain ⟨oct1, oct2, oct3, oct4, pre, heq⟩ :=
      matching_view_normalizes_equiv input view hmatch
    subst view
    have hparts :=
      (matches_view_equiv input oct1 oct2 oct3 oct4 pre).1 hmatch
    obtain ⟨h1, h2, h3, h4, hp⟩ :=
      components_of_parts input oct1 oct2 oct3 oct4 pre hparts
    obtain ⟨hwfConstraints, hconstraints⟩ :=
      (view_valid_equiv input oct1 oct2 oct3 oct4 pre).1 hviewValid
    have hgrammar : IPv4.IsWf.V4Net input :=
      (parts_exists_equiv input).2
        ⟨oct1, oct2, oct3, oct4, pre, hparts⟩
    have hsatisfiesWf : IPv4.SatisfiesWfConstraints input := by
      unfold IPv4.SatisfiesWfConstraints
      simpa only [h1, h2, h3, h4, hp] using hwfConstraints
    have hsatisfies : IPv4.SatisfiesConstraints input := by
      unfold IPv4.SatisfiesConstraints
      simpa only [h1, h2, h3, h4, hp] using hconstraints
    have hvalue : IPv4.value oct1 oct2 oct3 oct4 pre = result :=
      (view_denotation_equiv input oct1 oct2 oct3 oct4 pre).symm.trans
        hdenotation
    refine ⟨⟨⟨hgrammar, hsatisfiesWf⟩, hsatisfies⟩, ?_⟩
    rw [compute_value_of_parts input oct1 oct2 oct3 oct4 pre hparts]
    exact congrArg some hvalue

end Triptych.Vermilion.Proofs.IPv4
