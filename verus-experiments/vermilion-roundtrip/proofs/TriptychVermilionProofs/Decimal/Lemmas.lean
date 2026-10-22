import TriptychVermilionGenerated.Decimal
import Triptych.Backend.Verus.AstSemantics
import Proofs.Decimal.RuleRegistryProof

namespace Triptych.Vermilion.Proofs.Decimal

open Triptych
open Triptych.Vermilion.String
open Triptych.Vermilion.Generated.Decimal

theorem sign_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_decimal_roundtrip.decimal_is_wf_Sign sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  exact optional_minus_sequence_range sequence hwf

theorem natural_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_decimal_roundtrip.decimal_is_wf_Natural sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  apply digit_witness_sequence_range sequence
    (fun digits => 1 ≤ Vermilion.Seq.len digits)
  simpa [triptych_decimal_roundtrip.decimal_is_wf_Natural,
    triptych_decimal_roundtrip.triptych_is_digit, IsDigitCode] using hwf

theorem fraction_sequence_range (sequence : Vermilion.Seq Int)
    (hwf : triptych_decimal_roundtrip.decimal_is_wf_Fraction sequence) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  apply digit_witness_sequence_range sequence
    (fun digits =>
      1 ≤ Vermilion.Seq.len digits ∧ Vermilion.Seq.len digits ≤ 4)
  simpa [triptych_decimal_roundtrip.decimal_is_wf_Fraction,
    triptych_decimal_roundtrip.triptych_is_digit, IsDigitCode] using hwf

theorem sign_equiv (source : String) :
    Decimal.IsWf.Sign source ↔
      triptych_decimal_roundtrip.decimal_is_wf_Sign
        (encodeString source) := by
  constructor
  · intro hsource
    rcases hsource with hsource | hsource
    · subst source
      exact ⟨encodeString "-", rfl, Or.inr rfl⟩
    · subst source
      exact ⟨encodeString "", rfl, Or.inl (by simp)⟩
  · rintro ⟨literal, hsource, hempty | hminus⟩
    · right
      apply encodeString_injective
      rw [hsource]
      exact sequence_eq_empty_of_length_zero literal hempty
    · left
      apply encodeString_injective
      rw [hsource, hminus]
      rfl

theorem natural_equiv (source : String) :
    Decimal.IsWf.Natural source ↔
      triptych_decimal_roundtrip.decimal_is_wf_Natural
        (encodeString source) := by
  simpa [Decimal.IsWf.Natural,
    triptych_decimal_roundtrip.decimal_is_wf_Natural,
    triptych_decimal_roundtrip.triptych_is_digit, IsDigitCode] using
      digits_iff_encoded source

theorem fraction_equiv (source : String) :
    Decimal.IsWf.Fraction source ↔
      triptych_decimal_roundtrip.decimal_is_wf_Fraction
        (encodeString source) := by
  simpa [Decimal.IsWf.Fraction,
    triptych_decimal_roundtrip.decimal_is_wf_Fraction,
    triptych_decimal_roundtrip.triptych_is_digit, IsDigitCode] using
      digitsBetween_iff_encoded 1 4 source

theorem decimal_equiv (source : String) :
    Decimal.IsWf.Decimal source ↔
      triptych_decimal_roundtrip.decimal_is_wf_Decimal
        (encodeString source) := by
  unfold Decimal.IsWf.Decimal Decimal.Production
  constructor
  · rintro ⟨signPart, natural, fraction,
      ⟨⟨hinput, hsign⟩, hnatural⟩, hfraction⟩
    refine ⟨encodeString signPart, encodeString natural, encodeString fraction,
      ⟨⟨⟨?_, (sign_equiv signPart).1 hsign⟩,
      (natural_equiv natural).1 hnatural⟩,
      (fraction_equiv fraction).1 hfraction⟩⟩
    simpa [encodeString_append, encodeString, Vermilion.Seq.add,
      Vermilion.Seq.push, Vermilion.Seq.empty] using congrArg encodeString hinput
  · rintro ⟨signSequence, natural, fraction,
      ⟨⟨⟨hinput, hsign⟩, hnatural⟩, hfraction⟩⟩
    have hsignRange := sign_sequence_range signSequence hsign
    have hnaturalRange := natural_sequence_range natural hnatural
    have hfractionRange := fraction_sequence_range fraction hfraction
    let signText := decodeSequence signSequence
    let naturalText := decodeSequence natural
    let fractionText := decodeSequence fraction
    have hsignEncode : encodeString signText = signSequence :=
      encode_decode_sequence signSequence hsignRange
    have hnaturalEncode : encodeString naturalText = natural :=
      encode_decode_sequence natural hnaturalRange
    have hfractionEncode : encodeString fractionText = fraction :=
      encode_decode_sequence fraction hfractionRange
    refine ⟨signText, naturalText, fractionText, ?_⟩
    have hsource :
        source = signText ++ naturalText ++ "." ++ fractionText := by
      apply encodeString_injective
      rw [encodeString_append, encodeString_append, encodeString_append,
        hsignEncode, hnaturalEncode, hfractionEncode]
      simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
        Vermilion.Seq.empty] using hinput
    refine ⟨⟨⟨hsource, ?_⟩, ?_⟩, ?_⟩
    · apply (sign_equiv signText).2
      simpa [hsignEncode] using hsign
    · apply (natural_equiv naturalText).2
      simpa [hnaturalEncode] using hnatural
    · apply (fraction_equiv fractionText).2
      simpa [hfractionEncode] using hfraction

theorem natFrom_eq_fold (bytes : List Int) (index : Nat)
    (accumulator : Int) (hindex : index ≤ bytes.length) :
    triptych_decimal_roundtrip.triptych_nat_of_from
        bytes (Int.ofNat index) accumulator =
      (bytes.drop index).foldl
        (fun current byte => current * 10 + recoveredDigit byte)
        accumulator := by
  apply Triptych.Vermilion.String.natFrom_eq_fold
    triptych_decimal_roundtrip.triptych_nat_of_from
  · intro stepBytes stepIndex stepAccumulator hrange
    rw [triptych_decimal_roundtrip.triptych_nat_of_from, dif_pos hrange]
    rfl
  · exact hindex

theorem natOf_equiv (source : String) :
    triptych_decimal_roundtrip.triptych_nat_of (encodeString source) =
      Triptych.natOf source := by
  unfold triptych_decimal_roundtrip.triptych_nat_of
  change triptych_decimal_roundtrip.triptych_nat_of_from
      (encodeString source) (Int.ofNat 0) 0 = Triptych.natOf source
  rw [natFrom_eq_fold _ 0 0 (Nat.zero_le _)]
  simpa using encodedDigitFold_eq_natOf source

theorem signOf_equiv (source : String) :
    triptych_decimal_roundtrip.triptych_sign_of (encodeString source) =
      Triptych.signOf source := by
  simpa [triptych_decimal_roundtrip.triptych_sign_of,
    triptych_decimal_roundtrip.TRIPTYCH_MINUS, recoveredSignOf] using
      recoveredSignOf_encodeString source

theorem intPow_four :
    triptych_decimal_roundtrip.triptych_int_pow 10 4 =
      (10 : Int) ^ 4 := by
  norm_num [triptych_decimal_roundtrip.triptych_int_pow, Vermilion.iteP]

theorem intPow_four_sub_length (source : String) :
    triptych_decimal_roundtrip.triptych_int_pow
        10 (4 - Int.ofNat source.length) =
      (10 : Int) ^ (4 - Int.ofNat source.length).toNat := by
  by_cases hlength : source.length ≤ 4
  · interval_cases source.length <;>
      norm_num [triptych_decimal_roundtrip.triptych_int_pow, Vermilion.iteP]
  · have hnot : ¬source.length < 4 := by omega
    have hzero : 4 - source.length = 0 :=
      Nat.sub_eq_zero_of_le (by omega)
    rw [triptych_decimal_roundtrip.triptych_int_pow]
    simp [Vermilion.iteP, hnot, hzero]

theorem decimal_value_equiv
    (signPart natural fraction : String) :
    Decimal.value signPart natural fraction =
      triptych_decimal_roundtrip.decimal_value
        (encodeString signPart) (encodeString natural)
        (encodeString fraction) := by
  unfold Decimal.value triptych_decimal_roundtrip.decimal_value
  rw [signOf_equiv, natOf_equiv, natOf_equiv, intPow_four,
    encodeString_length, intPow_four_sub_length]
  rfl

theorem decimal_constraints_equiv
    (signPart natural fraction : String) :
    Decimal.Constraints signPart natural fraction ↔
      triptych_decimal_roundtrip.decimal_constraints
        (encodeString signPart) (encodeString natural)
        (encodeString fraction) := by
  unfold Decimal.Constraints triptych_decimal_roundtrip.decimal_constraints
  rw [← decimal_value_equiv signPart natural fraction]
  norm_num

theorem matches_view_equiv
    (input signPart natural fraction : String) :
    triptych_decimal_roundtrip.decimal_matches_view
        (encodeString input)
        (.DecimalView (encodeString input) (encodeString signPart)
          (encodeString natural) (encodeString fraction)) ↔
      input = signPart ++ natural ++ "." ++ fraction ∧
        Decimal.IsWf.Sign signPart ∧ Decimal.IsWf.Natural natural ∧
          Decimal.IsWf.Fraction fraction := by
  constructor
  · rintro ⟨_, signSequence, naturalSequence, fractionSequence,
      ⟨⟨⟨hinput, ⟨hsign, hsignMatch⟩⟩,
        ⟨hnatural, hnaturalMatch⟩⟩,
        ⟨hfraction, hfractionMatch⟩⟩⟩
    subst signSequence
    subst naturalSequence
    subst fractionSequence
    have hsource :
        input = signPart ++ natural ++ "." ++ fraction := by
      apply encodeString_injective
      simpa [encodeString_append, encodeString, Vermilion.Seq.add,
        Vermilion.Seq.push, Vermilion.Seq.empty] using hinput
    refine ⟨hsource, ?_, ?_, ?_⟩
    · apply (sign_equiv signPart).2
      exact hsignMatch
    · apply (natural_equiv natural).2
      exact hnaturalMatch
    · apply (fraction_equiv fraction).2
      exact hfractionMatch
  · rintro ⟨hinput, hsign, hnatural, hfraction⟩
    refine ⟨rfl, encodeString signPart, encodeString natural,
      encodeString fraction, ?_⟩
    refine ⟨⟨⟨?_, ⟨rfl, ?_⟩⟩, ⟨rfl, ?_⟩⟩, ⟨rfl, ?_⟩⟩
    · simpa [encodeString_append, encodeString, Vermilion.Seq.add,
        Vermilion.Seq.push, Vermilion.Seq.empty] using
          congrArg encodeString hinput
    · change triptych_decimal_roundtrip.decimal_is_wf_Sign
        (encodeString signPart)
      exact (sign_equiv signPart).1 hsign
    · change triptych_decimal_roundtrip.decimal_is_wf_Natural
        (encodeString natural)
      exact (natural_equiv natural).1 hnatural
    · change triptych_decimal_roundtrip.decimal_is_wf_Fraction
        (encodeString fraction)
      exact (fraction_equiv fraction).1 hfraction

theorem normalize_matching_view (input : String)
    (condition : triptych_decimal_roundtrip.DecimalView → Prop) :
    (∃ view : triptych_decimal_roundtrip.DecimalView,
      triptych_decimal_roundtrip.decimal_matches_view
          (encodeString input) view ∧
        condition view) ↔
      ∃ signPart natural fraction : String,
        triptych_decimal_roundtrip.decimal_matches_view
            (encodeString input)
            (.DecimalView (encodeString input) (encodeString signPart)
              (encodeString natural) (encodeString fraction)) ∧
          condition
            (.DecimalView (encodeString input) (encodeString signPart)
              (encodeString natural) (encodeString fraction)) := by
  constructor
  · rintro ⟨view, hmatch, hcondition⟩
    cases view with
    | DecimalView viewInput signSequence naturalSequence fractionSequence =>
      have hmatchCopy := hmatch
      rcases hmatch with
        ⟨hviewInput, signWitness, naturalWitness, fractionWitness,
          ⟨⟨⟨_, ⟨hsignWitness, hsignWf⟩⟩,
            ⟨hnaturalWitness, hnaturalWf⟩⟩,
            ⟨hfractionWitness, hfractionWf⟩⟩⟩
      simp only [
        triptych_decimal_roundtrip.DecimalView.get_DecimalView_input]
          at hviewInput
      simp only [
        triptych_decimal_roundtrip.DecimalView.get_DecimalView_sign]
          at hsignWitness
      simp only [
        triptych_decimal_roundtrip.DecimalView.get_DecimalView_natural]
          at hnaturalWitness
      simp only [
        triptych_decimal_roundtrip.DecimalView.get_DecimalView_fraction]
          at hfractionWitness
      subst viewInput
      subst signWitness
      subst naturalWitness
      subst fractionWitness
      have hsignSpec :
          triptych_decimal_roundtrip.decimal_is_wf_Sign signSequence := by
        simpa [triptych_decimal_roundtrip.decimal_is_wf_Sign,
          triptych_decimal_roundtrip.decimal_matches_Sign] using hsignWf
      have hnaturalSpec :
          triptych_decimal_roundtrip.decimal_is_wf_Natural
            naturalSequence := by
        simpa [triptych_decimal_roundtrip.decimal_is_wf_Natural,
          triptych_decimal_roundtrip.decimal_matches_Natural] using hnaturalWf
      have hfractionSpec :
          triptych_decimal_roundtrip.decimal_is_wf_Fraction
            fractionSequence := by
        simpa [triptych_decimal_roundtrip.decimal_is_wf_Fraction,
          triptych_decimal_roundtrip.decimal_matches_Fraction] using hfractionWf
      let signPart := decodeSequence signSequence
      let natural := decodeSequence naturalSequence
      let fraction := decodeSequence fractionSequence
      have hsignEncode : encodeString signPart = signSequence :=
        encode_decode_sequence signSequence
          (sign_sequence_range signSequence hsignSpec)
      have hnaturalEncode : encodeString natural = naturalSequence :=
        encode_decode_sequence naturalSequence
          (natural_sequence_range naturalSequence hnaturalSpec)
      have hfractionEncode : encodeString fraction = fractionSequence :=
        encode_decode_sequence fractionSequence
          (fraction_sequence_range fractionSequence hfractionSpec)
      refine ⟨signPart, natural, fraction, ?_, ?_⟩
      · simpa only [hsignEncode, hnaturalEncode, hfractionEncode] using
          hmatchCopy
      · simpa only [hsignEncode, hnaturalEncode, hfractionEncode] using
          hcondition
  · rintro ⟨signPart, natural, fraction, hmatch, hcondition⟩
    exact ⟨.DecimalView (encodeString input) (encodeString signPart)
      (encodeString natural) (encodeString fraction), hmatch, hcondition⟩

theorem matching_view_exists_equiv (input : String) :
    Decimal.IsWf input ↔
      ∃ signPart natural fraction : String,
        triptych_decimal_roundtrip.decimal_matches_view
          (encodeString input)
          (.DecimalView (encodeString input) (encodeString signPart)
            (encodeString natural) (encodeString fraction)) := by
  constructor
  · rintro ⟨signPart, natural, fraction,
      ⟨⟨hinput, hsign⟩, hnatural⟩, hfraction⟩
    exact ⟨signPart, natural, fraction,
      (matches_view_equiv input signPart natural fraction).2
        ⟨hinput, hsign, hnatural, hfraction⟩⟩
  · rintro ⟨signPart, natural, fraction, hmatch⟩
    obtain ⟨hinput, hsign, hnatural, hfraction⟩ :=
      (matches_view_equiv input signPart natural fraction).1 hmatch
    exact ⟨signPart, natural, fraction,
      ⟨⟨hinput, hsign⟩, hnatural⟩, hfraction⟩

theorem decode_of_parts
    (input signPart natural fraction : String)
    (hinput : input = signPart ++ natural ++ "." ++ fraction)
    (hsign : Decimal.IsWf.Sign signPart)
    (hnatural : Decimal.IsWf.Natural natural)
    (hfraction : Decimal.IsWf.Fraction fraction) :
    decode Decimal.grammar input =
      some [("Sign", signPart), ("Natural", natural),
        ("Fraction", fraction)] := by
  rcases hsign with hminus | hempty
  · subst signPart
    let derivation : Decimal.Derivation.Decimal :=
      .alt0 (.alt0 (some ())) (.alt0 natural) (.alt0 fraction)
    have hvalid : Decimal.Derivation.Decimal.Valid derivation := by
      simpa [derivation, Decimal.Derivation.Decimal.Valid,
        Decimal.Derivation.Sign.Valid, Decimal.Derivation.Natural.Valid,
        Decimal.Derivation.Fraction.Valid, Decimal.IsWf.Natural,
        Decimal.IsWf.Fraction, Triptych.IsDigits_matchesTerm,
        Triptych.IsDigitsBetween_matchesTerm] using
          ⟨trivial, hnatural, hfraction⟩
    have hrender :
        Decimal.Derivation.Decimal.render derivation = input := by
      rw [hinput]
      simp [derivation, Decimal.Derivation.Decimal.render,
        Decimal.Derivation.Sign.render, Decimal.Derivation.Natural.render,
        Decimal.Derivation.Fraction.render, Triptych.renderOptional,
        String.append_assoc]
    have hcaptures :
        Decimal.Derivation.Decimal.capturesWith "" derivation =
          [("Sign", "-"), ("Natural", natural), ("Fraction", fraction)] := by
      simp [derivation, Decimal.Derivation.Decimal.capturesWith,
        Decimal.Derivation.Sign.capturesWith,
        Decimal.Derivation.Natural.capturesWith,
        Decimal.Derivation.Fraction.capturesWith,
        Decimal.Derivation.Sign.render, Decimal.Derivation.Natural.render,
        Decimal.Derivation.Fraction.render, Triptych.referenceCaptures,
        Triptych.capturesOptional, Triptych.renderOptional]
    have hdecode :=
      Decimal.Derivation.Decimal.decode_render derivation hvalid
    simpa [hrender, hcaptures] using hdecode
  · subst signPart
    let derivation : Decimal.Derivation.Decimal :=
      .alt0 (.alt0 none) (.alt0 natural) (.alt0 fraction)
    have hvalid : Decimal.Derivation.Decimal.Valid derivation := by
      simpa [derivation, Decimal.Derivation.Decimal.Valid,
        Decimal.Derivation.Sign.Valid, Decimal.Derivation.Natural.Valid,
        Decimal.Derivation.Fraction.Valid, Decimal.IsWf.Natural,
        Decimal.IsWf.Fraction, Triptych.IsDigits_matchesTerm,
        Triptych.IsDigitsBetween_matchesTerm] using
          ⟨trivial, hnatural, hfraction⟩
    have hrender :
        Decimal.Derivation.Decimal.render derivation = input := by
      rw [hinput]
      simp [derivation, Decimal.Derivation.Decimal.render,
        Decimal.Derivation.Sign.render, Decimal.Derivation.Natural.render,
        Decimal.Derivation.Fraction.render, Triptych.renderOptional,
        String.append_assoc]
    have hcaptures :
        Decimal.Derivation.Decimal.capturesWith "" derivation =
          [("Sign", ""), ("Natural", natural), ("Fraction", fraction)] := by
      simp [derivation, Decimal.Derivation.Decimal.capturesWith,
        Decimal.Derivation.Sign.capturesWith,
        Decimal.Derivation.Natural.capturesWith,
        Decimal.Derivation.Fraction.capturesWith,
        Decimal.Derivation.Sign.render, Decimal.Derivation.Natural.render,
        Decimal.Derivation.Fraction.render, Triptych.referenceCaptures,
        Triptych.capturesOptional, Triptych.renderOptional]
    have hdecode :=
      Decimal.Derivation.Decimal.decode_render derivation hvalid
    simpa [hrender, hcaptures] using hdecode

set_option maxRecDepth 10000 in
theorem satisfies_constraints_of_parts
    (input signPart natural fraction : String)
    (hinput : input = signPart ++ natural ++ "." ++ fraction)
    (hsign : Decimal.IsWf.Sign signPart)
    (hnatural : Decimal.IsWf.Natural natural)
    (hfraction : Decimal.IsWf.Fraction fraction) :
    Decimal.SatisfiesConstraints input ↔
      Decimal.Constraints signPart natural fraction := by
  rcases hsign with hminus | hempty
  · subst signPart
    let derivation : Decimal.Derivation.Decimal :=
      .alt0 (.alt0 (some ())) (.alt0 natural) (.alt0 fraction)
    have hvalid : Decimal.Derivation.Decimal.Valid derivation := by
      simpa [derivation, Decimal.Derivation.Decimal.Valid,
        Decimal.Derivation.Sign.Valid, Decimal.Derivation.Natural.Valid,
        Decimal.Derivation.Fraction.Valid, Decimal.IsWf.Natural,
        Decimal.IsWf.Fraction, Triptych.IsDigits_matchesTerm,
        Triptych.IsDigitsBetween_matchesTerm] using
          ⟨trivial, hnatural, hfraction⟩
    have hrender :
        Decimal.Derivation.Decimal.render derivation = input := by
      rw [hinput]
      simp [derivation, Decimal.Derivation.Decimal.render,
        Decimal.Derivation.Sign.render, Decimal.Derivation.Natural.render,
        Decimal.Derivation.Fraction.render, Triptych.renderOptional,
        String.append_assoc]
    have hcaptures :
        Decimal.Derivation.Decimal.capturesWith "" derivation =
          [("Sign", "-"), ("Natural", natural), ("Fraction", fraction)] := by
      simp [derivation, Decimal.Derivation.Decimal.capturesWith,
        Decimal.Derivation.Sign.capturesWith,
        Decimal.Derivation.Natural.capturesWith,
        Decimal.Derivation.Fraction.capturesWith,
        Decimal.Derivation.Sign.render, Decimal.Derivation.Natural.render,
        Decimal.Derivation.Fraction.render, Triptych.referenceCaptures,
        Triptych.capturesOptional, Triptych.renderOptional]
    have hdecode :=
      Decimal.Derivation.Decimal.decode_render derivation hvalid
    rw [hrender] at hdecode
    rw [hcaptures] at hdecode
    rw [Decimal.SatisfiesConstraints_of_decode hdecode]
    rfl
  · subst signPart
    let derivation : Decimal.Derivation.Decimal :=
      .alt0 (.alt0 none) (.alt0 natural) (.alt0 fraction)
    have hvalid : Decimal.Derivation.Decimal.Valid derivation := by
      simpa [derivation, Decimal.Derivation.Decimal.Valid,
        Decimal.Derivation.Sign.Valid, Decimal.Derivation.Natural.Valid,
        Decimal.Derivation.Fraction.Valid, Decimal.IsWf.Natural,
        Decimal.IsWf.Fraction, Triptych.IsDigits_matchesTerm,
        Triptych.IsDigitsBetween_matchesTerm] using
          ⟨trivial, hnatural, hfraction⟩
    have hrender :
        Decimal.Derivation.Decimal.render derivation = input := by
      rw [hinput]
      simp [derivation, Decimal.Derivation.Decimal.render,
        Decimal.Derivation.Sign.render, Decimal.Derivation.Natural.render,
        Decimal.Derivation.Fraction.render, Triptych.renderOptional,
        String.append_assoc]
    have hcaptures :
        Decimal.Derivation.Decimal.capturesWith "" derivation =
          [("Sign", ""), ("Natural", natural), ("Fraction", fraction)] := by
      simp [derivation, Decimal.Derivation.Decimal.capturesWith,
        Decimal.Derivation.Sign.capturesWith,
        Decimal.Derivation.Natural.capturesWith,
        Decimal.Derivation.Fraction.capturesWith,
        Decimal.Derivation.Sign.render, Decimal.Derivation.Natural.render,
        Decimal.Derivation.Fraction.render, Triptych.referenceCaptures,
        Triptych.capturesOptional, Triptych.renderOptional]
    have hdecode :=
      Decimal.Derivation.Decimal.decode_render derivation hvalid
    rw [hrender] at hdecode
    rw [hcaptures] at hdecode
    rw [Decimal.SatisfiesConstraints_of_decode hdecode]
    rfl

theorem satisfies_constraints_equiv (source : String)
    (hwf : Decimal.IsWf.Decimal source) :
    Decimal.SatisfiesConstraints source ↔
      triptych_decimal_roundtrip.decimal_satisfies_constraints
        (encodeString source) := by
  constructor
  · intro hconstraints
    rcases hwf with ⟨signPart, natural, fraction,
      ⟨⟨hinput, hsign⟩, hnatural⟩, hfraction⟩
    have hparts :
        Decimal.Constraints signPart natural fraction :=
      (satisfies_constraints_of_parts source signPart natural fraction
        hinput hsign hnatural hfraction).1 hconstraints
    refine ⟨.DecimalView (encodeString source) (encodeString signPart)
      (encodeString natural) (encodeString fraction), ?_⟩
    refine ⟨?_, ?_⟩
    · exact (matches_view_equiv source signPart natural fraction).2
        ⟨hinput, hsign, hnatural, hfraction⟩
    · unfold triptych_decimal_roundtrip.decimal_view_constraints
      exact (decimal_constraints_equiv signPart natural fraction).1 hparts
  · rintro ⟨view, hmatch, hconstraints⟩
    cases view with
    | DecimalView viewInput signSequence naturalSequence fractionSequence =>
        rcases hmatch with
          ⟨hviewInput, signWitness, naturalWitness, fractionWitness,
            ⟨⟨⟨hinput, ⟨hsignWitness, hsignWf⟩⟩,
              ⟨hnaturalWitness, hnaturalWf⟩⟩,
              ⟨hfractionWitness, hfractionWf⟩⟩⟩
        simp only [
          triptych_decimal_roundtrip.DecimalView.get_DecimalView_input] at hviewInput
        simp only [
          triptych_decimal_roundtrip.DecimalView.get_DecimalView_sign] at hsignWitness
        simp only [
          triptych_decimal_roundtrip.DecimalView.get_DecimalView_natural] at hnaturalWitness
        simp only [
          triptych_decimal_roundtrip.DecimalView.get_DecimalView_fraction] at hfractionWitness
        subst viewInput
        subst signWitness
        subst naturalWitness
        subst fractionWitness
        have hsignSpec :
            triptych_decimal_roundtrip.decimal_is_wf_Sign signSequence := by
          simpa [triptych_decimal_roundtrip.decimal_is_wf_Sign,
            triptych_decimal_roundtrip.decimal_matches_Sign] using hsignWf
        have hnaturalSpec :
            triptych_decimal_roundtrip.decimal_is_wf_Natural
              naturalSequence := by
          simpa [triptych_decimal_roundtrip.decimal_is_wf_Natural,
            triptych_decimal_roundtrip.decimal_matches_Natural] using
              hnaturalWf
        have hfractionSpec :
            triptych_decimal_roundtrip.decimal_is_wf_Fraction
              fractionSequence := by
          simpa [triptych_decimal_roundtrip.decimal_is_wf_Fraction,
            triptych_decimal_roundtrip.decimal_matches_Fraction] using
              hfractionWf
        have hsignRange := sign_sequence_range signSequence hsignSpec
        have hnaturalRange :=
          natural_sequence_range naturalSequence hnaturalSpec
        have hfractionRange :=
          fraction_sequence_range fractionSequence hfractionSpec
        let signPart := decodeSequence signSequence
        let natural := decodeSequence naturalSequence
        let fraction := decodeSequence fractionSequence
        have hsignEncode : encodeString signPart = signSequence :=
          encode_decode_sequence signSequence hsignRange
        have hnaturalEncode : encodeString natural = naturalSequence :=
          encode_decode_sequence naturalSequence hnaturalRange
        have hfractionEncode : encodeString fraction = fractionSequence :=
          encode_decode_sequence fractionSequence hfractionRange
        have hsource :
            source = signPart ++ natural ++ "." ++ fraction := by
          apply encodeString_injective
          rw [encodeString_append, encodeString_append, encodeString_append,
            hsignEncode, hnaturalEncode, hfractionEncode]
          simpa [encodeString, Vermilion.Seq.add, Vermilion.Seq.push,
            Vermilion.Seq.empty] using hinput
        have hsign : Decimal.IsWf.Sign signPart := by
          apply (sign_equiv signPart).2
          simpa [hsignEncode] using hsignSpec
        have hnatural : Decimal.IsWf.Natural natural := by
          apply (natural_equiv natural).2
          simpa [hnaturalEncode] using hnaturalSpec
        have hfraction : Decimal.IsWf.Fraction fraction := by
          apply (fraction_equiv fraction).2
          simpa [hfractionEncode] using hfractionSpec
        apply (satisfies_constraints_of_parts source signPart natural
          fraction hsource hsign hnatural hfraction).2
        apply (decimal_constraints_equiv signPart natural fraction).2
        rw [← hsignEncode, ← hnaturalEncode, ← hfractionEncode] at hconstraints
        simpa [triptych_decimal_roundtrip.decimal_view_constraints] using
          hconstraints

theorem is_valid_equiv (source : String) :
    Decimal.IsValid source ↔
      triptych_decimal_roundtrip.decimal_is_valid
        (encodeString source) := by
  constructor
  · rintro ⟨hwf, hconstraints⟩
    exact ⟨(decimal_equiv source).1 hwf,
      (satisfies_constraints_equiv source hwf).1 hconstraints⟩
  · rintro ⟨hwfRecovered, hconstraintsRecovered⟩
    have hwf : Decimal.IsWf.Decimal source :=
      (decimal_equiv source).2 hwfRecovered
    exact ⟨hwf,
      (satisfies_constraints_equiv source hwf).2 hconstraintsRecovered⟩

theorem view_denotation_equiv :
    ∀ input signPart natural fraction : String,
      Recovered.decimal_view_denotation
          (Recovered.mkDecimalView (encodeString input)
            (encodeString signPart) (encodeString natural)
            (encodeString fraction)) =
        Decimal.value signPart natural fraction := by
  intro input signPart natural fraction
  exact (decimal_value_equiv signPart natural fraction).symm

theorem view_valid_equiv :
    ∀ input signPart natural fraction : String,
      Recovered.decimal_view_valid
          (Recovered.mkDecimalView (encodeString input)
            (encodeString signPart) (encodeString natural)
            (encodeString fraction)) ↔
        Decimal.Constraints signPart natural fraction := by
  intro input signPart natural fraction
  simpa [triptych_decimal_roundtrip.decimal_view_valid,
    triptych_decimal_roundtrip.decimal_view_constraints] using
      (decimal_constraints_equiv signPart natural fraction).symm

theorem matching_view_normalizes_equiv :
    ∀ input : String, ∀ view : Recovered.DecimalView,
      Recovered.decimal_matches_view (encodeString input) view →
        ∃ signPart natural fraction : String,
          view =
            Recovered.mkDecimalView (encodeString input)
              (encodeString signPart) (encodeString natural)
              (encodeString fraction) := by
  intro input view hmatch
  obtain ⟨signPart, natural, fraction, _, heq⟩ :=
    (normalize_matching_view input (fun candidate => candidate = view)).1
      ⟨view, hmatch, rfl⟩
  exact ⟨signPart, natural, fraction, heq.symm⟩

theorem matches_view_exact_equiv :
    ∀ input signPart natural fraction : String,
      Recovered.decimal_matches_view (encodeString input)
          (Recovered.mkDecimalView (encodeString input)
            (encodeString signPart) (encodeString natural)
            (encodeString fraction)) ↔
        (((Decimal.IsWf.Decimal input ∧
              Triptych.component Decimal.grammar input "Sign" = signPart) ∧
            Triptych.component Decimal.grammar input "Natural" = natural) ∧
          Triptych.component Decimal.grammar input "Fraction" = fraction) := by
  intro input signPart natural fraction
  change
    triptych_decimal_roundtrip.decimal_matches_view (encodeString input)
        (.DecimalView (encodeString input) (encodeString signPart)
          (encodeString natural) (encodeString fraction)) ↔ _
  rw [matches_view_equiv]
  constructor
  · rintro ⟨hinput, hsign, hnatural, hfraction⟩
    have hdecode :=
      decode_of_parts input signPart natural fraction hinput hsign hnatural
        hfraction
    refine ⟨⟨⟨⟨signPart, natural, fraction,
      ⟨⟨hinput, hsign⟩, hnatural⟩, hfraction⟩, ?_⟩, ?_⟩, ?_⟩
    · simpa [CaptureMap.toEnv] using
        (Triptych.component_eq_of_decode hdecode "Sign")
    · simpa [CaptureMap.toEnv] using
        (Triptych.component_eq_of_decode hdecode "Natural")
    · simpa [CaptureMap.toEnv] using
        (Triptych.component_eq_of_decode hdecode "Fraction")
  · rintro ⟨⟨⟨hgrammar, hsignComponent⟩, hnaturalComponent⟩,
      hfractionComponent⟩
    obtain ⟨decodedSign, decodedNatural, decodedFraction, hdecode,
      hsign, hinput, hnatural, hfraction⟩ :=
      Decimal.RuleRegistryProof.decode_parts_of_isWf hgrammar
    have hdecodedSign :
        Triptych.component Decimal.grammar input "Sign" = decodedSign := by
      simpa [CaptureMap.toEnv] using
        (Triptych.component_eq_of_decode hdecode "Sign")
    have hdecodedNatural :
        Triptych.component Decimal.grammar input "Natural" =
          decodedNatural := by
      simpa [CaptureMap.toEnv] using
        (Triptych.component_eq_of_decode hdecode "Natural")
    have hdecodedFraction :
        Triptych.component Decimal.grammar input "Fraction" =
          decodedFraction := by
      simpa [CaptureMap.toEnv] using
        (Triptych.component_eq_of_decode hdecode "Fraction")
    have hsignEq : decodedSign = signPart :=
      hdecodedSign.symm.trans hsignComponent
    have hnaturalEq : decodedNatural = natural :=
      hdecodedNatural.symm.trans hnaturalComponent
    have hfractionEq : decodedFraction = fraction :=
      hdecodedFraction.symm.trans hfractionComponent
    simp only [hsignEq, hnaturalEq, hfractionEq] at hinput hsign hnatural hfraction
    exact ⟨hinput, hsign, hnatural, hfraction⟩

theorem matches_result_equiv :
    ∀ input : String, ∀ result : Int,
      (Decimal.IsValid input ∧
          Decimal.computeValue input = some result) ↔
        Recovered.decimal_matches_result (encodeString input) result := by
  intro input result
  change
    (Decimal.IsValid input ∧ Decimal.computeValue input = some result) ↔
      triptych_decimal_roundtrip.decimal_matches_result
        (encodeString input) result
  unfold triptych_decimal_roundtrip.decimal_matches_result
  constructor
  · rintro ⟨hvalid, hcompute⟩
    obtain ⟨signPart, natural, fraction, hdecode, hsign, hinput, hnatural,
      hfraction⟩ :=
      Decimal.RuleRegistryProof.decode_parts_of_isWf hvalid.1
    have hmatch :
        triptych_decimal_roundtrip.decimal_matches_view
          (encodeString input)
          (.DecimalView (encodeString input) (encodeString signPart)
            (encodeString natural) (encodeString fraction)) :=
      (matches_view_equiv input signPart natural fraction).2
        ⟨hinput, hsign, hnatural, hfraction⟩
    have hconstraints :
        Decimal.Constraints signPart natural fraction := by
      have hconstraints' :=
        (Decimal.SatisfiesConstraints_of_decode hdecode).1 hvalid.2
      simpa [CaptureMap.toEnv] using hconstraints'
    have hviewValid :
        triptych_decimal_roundtrip.decimal_view_valid
          (.DecimalView (encodeString input) (encodeString signPart)
            (encodeString natural) (encodeString fraction)) :=
      (view_valid_equiv input signPart natural fraction).2 hconstraints
    have hvalue : Decimal.value signPart natural fraction = result := by
      rw [Decimal.computeValue_of_decode hdecode] at hcompute
      simpa [CaptureMap.toEnv] using Option.some.inj hcompute
    have hdenotation :
        triptych_decimal_roundtrip.decimal_view_denotation
            (.DecimalView (encodeString input) (encodeString signPart)
              (encodeString natural) (encodeString fraction)) =
          result :=
      (view_denotation_equiv input signPart natural fraction).trans hvalue
    exact ⟨.DecimalView (encodeString input) (encodeString signPart)
      (encodeString natural) (encodeString fraction),
      ⟨⟨hmatch, hviewValid⟩, hdenotation⟩⟩
  · rintro ⟨view, ⟨⟨hmatch, hviewValid⟩, hdenotation⟩⟩
    obtain ⟨signPart, natural, fraction, heq⟩ :=
      matching_view_normalizes_equiv input view hmatch
    subst view
    have hparts :=
      (matches_view_equiv input signPart natural fraction).1 hmatch
    rcases hparts with ⟨hinput, hsign, hnatural, hfraction⟩
    have hconstraints : Decimal.Constraints signPart natural fraction :=
      (view_valid_equiv input signPart natural fraction).1 hviewValid
    have hsatisfies : Decimal.SatisfiesConstraints input :=
      (satisfies_constraints_of_parts input signPart natural fraction hinput
        hsign hnatural hfraction).2 hconstraints
    have hdecode :=
      decode_of_parts input signPart natural fraction hinput hsign hnatural
        hfraction
    have hvalue : Decimal.value signPart natural fraction = result :=
      (view_denotation_equiv input signPart natural fraction).symm.trans hdenotation
    refine ⟨⟨⟨signPart, natural, fraction,
      ⟨⟨hinput, hsign⟩, hnatural⟩, hfraction⟩, hsatisfies⟩, ?_⟩
    rw [Decimal.computeValue_of_decode hdecode]
    simpa [CaptureMap.toEnv] using congrArg some hvalue

end Triptych.Vermilion.Proofs.Decimal
