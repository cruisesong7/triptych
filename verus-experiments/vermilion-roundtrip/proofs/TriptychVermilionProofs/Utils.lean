import Batteries.Data.Char.Basic
import Triptych.Architecture.Denote
import Triptych.Backend.Verus.AstSemantics
import Vermilion

namespace Triptych.Vermilion.String

def encodeString (source : String) : Vermilion.Seq Int :=
  source.toList.map (fun character => Int.ofNat character.toNat)

def decodeSequence (sequence : Vermilion.Seq Int) : String :=
  String.ofList (sequence.map fun code => Char.ofNat code.toNat)

theorem encodedChar_isUnicodeScalar (character : Char) :
    Vermilion.isUnicodeScalar (Int.ofNat character.toNat) := by
  simp only [Vermilion.isUnicodeScalar]
  have hmax := Char.toNat_le_max character
  have hsurrogate := Char.toNat_not_surrogate character
  by_cases hlow : character.toNat < Char.minSurrogate
  · left
    constructor
    · exact Int.ofNat_nonneg character.toNat
    · exact (Int.ofNat_le (m := character.toNat) (n := 55295)).2 (by
        have : character.toNat < 55296 := by
          simpa [Char.minSurrogate] using hlow
        omega)
  · right
    constructor
    · have hhigh : Char.maxSurrogate < character.toNat := by omega
      exact (Int.ofNat_le (m := 57344) (n := character.toNat)).2 (by
        have : 57343 < character.toNat := by
          simpa [Char.maxSurrogate] using hhigh
        omega)
    · exact (Int.ofNat_le (m := character.toNat) (n := 1114111)).2 (by
        simpa [Char.max] using hmax)

theorem encodeString_range (source : String) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len (encodeString source) →
        Vermilion.isUnicodeScalar
          (Vermilion.Seq.index (encodeString source) index) := by
  intro index hindex
  have hbound : index.toNat < source.toList.length := by
    simp only [encodeString, Vermilion.Seq.len, List.length_map] at hindex
    omega
  simp only [encodeString, Vermilion.Seq.index, if_pos hindex.1,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hbound,
    Option.map_some, Option.getD_some]
  exact encodedChar_isUnicodeScalar source.toList[index.toNat]

@[simp] theorem decode_encode_string (source : String) :
    decodeSequence (encodeString source) = source := by
  apply String.ext
  simp [decodeSequence, encodeString, Function.comp_def, Char.ofNat_toNat]

theorem encodeString_injective {left right : String}
    (h : encodeString left = encodeString right) :
    left = right := by
  have := congrArg decodeSequence h
  simpa using this

@[simp] theorem encodeString_inj_iff (left right : String) :
    encodeString left = encodeString right ↔ left = right :=
  ⟨encodeString_injective, congrArg encodeString⟩

@[simp] theorem encodeString_eq_empty_iff (source : String) :
    encodeString source = (Vermilion.Seq.empty : Vermilion.Seq Int) ↔
      source = "" := by
  simp [encodeString, Vermilion.Seq.empty]

@[simp] theorem encodeString_append (left right : String) :
    encodeString (left ++ right) = encodeString left ++ encodeString right := by
  simp [encodeString, String.toList_append]

private theorem map_intercalate {α β : Type}
    (transform : α → β) (separator : List α) (parts : List (List α)) :
    (separator.intercalate parts).map transform =
      (separator.map transform).intercalate
        (parts.map (List.map transform)) := by
  induction parts with
  | nil => simp
  | cons part rest ih =>
      cases rest with
      | nil => simp
      | cons next tail =>
          simp only [List.intercalate_cons_cons, List.map_append,
            List.map_cons]
          rw [ih]
          rfl

theorem encodeString_intercalate (separator : String) (parts : List String) :
    encodeString (String.intercalate separator parts) =
      (encodeString separator).intercalate (parts.map encodeString) := by
  unfold encodeString
  rw [String.toList_intercalate, map_intercalate, List.map_map]
  rfl

@[simp] theorem encodeString_length (source : String) :
    Vermilion.Seq.len (encodeString source) = Int.ofNat source.length := by
  simp [Vermilion.Seq.len, encodeString, String.length_toList]

theorem index_encoded_characters (characters : List Char) (index : Nat)
    (hindex : index < characters.length) :
    Vermilion.Seq.index
        (characters.map (fun character => Int.ofNat character.toNat))
        (Int.ofNat index) =
      Int.ofNat characters[index].toNat := by
  simp [Vermilion.Seq.index, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_eq_getElem hindex]

theorem noLeadingZero_iff_encoded (source : String) :
    (source.startsWith "0" → source = "0") ↔
      Vermilion.Seq.len (encodeString source) = 0 ∨
        ¬Vermilion.Seq.index (encodeString source) 0 = 48 ∨
          encodeString source =
            Vermilion.Seq.push (Vermilion.Seq.empty : Vermilion.Seq Int) 48 := by
  by_cases hempty : source = ""
  · subst source
    simp [encodeString, Vermilion.Seq.len, Vermilion.Seq.index,
      Vermilion.Seq.push, Vermilion.Seq.empty]
  · by_cases hzero : source = "0"
    · subst source
      simp [encodeString, Vermilion.Seq.len, Vermilion.Seq.index,
        Vermilion.Seq.push, Vermilion.Seq.empty]
    · obtain ⟨character, rest, hsource⟩ :
        ∃ character rest, source.toList = character :: rest := by
        cases hcharacters : source.toList with
        | nil =>
            exact absurd (String.toList_inj.mp (by simpa [hcharacters])) hempty
        | cons character rest => exact ⟨character, rest, rfl⟩
      by_cases hcharacter : character = '0'
      · subst character
        have hrest : rest ≠ [] := by
          intro hrest
          apply hzero
          apply String.toList_inj.mp
          simpa [hsource, hrest]
        simp [String.startsWith_string_iff, encodeString, hsource, hrest,
          Vermilion.Seq.len, Vermilion.Seq.index, Vermilion.Seq.push,
          Vermilion.Seq.empty, hzero]
        omega
      · have hcode : Int.ofNat character.toNat ≠ 48 := by
          intro hcode
          apply hcharacter
          apply Char.toNat_inj.mp
          exact Int.ofNat_inj.mp hcode
        have hcharacter' : ¬'0' = character := fun h => hcharacter h.symm
        simp [String.startsWith_string_iff, encodeString, hsource,
          hcharacter', Vermilion.Seq.len, Vermilion.Seq.index,
          Vermilion.Seq.push, Vermilion.Seq.empty]
        exact Or.inr (Or.inl hcode)

def IsDigitCode (code : Int) : Prop :=
  48 ≤ code ∧ code ≤ 57

theorem digit_iff_encoded (character : Char) :
    TokClass.digit.mem character ↔ IsDigitCode (Int.ofNat character.toNat) := by
  simp only [TokClass.mem, IsDigitCode, Char.le_def, UInt32.le_iff_toNat_le, Char.toNat]
  constructor
  · rintro ⟨hlower, hupper⟩
    exact ⟨(Int.ofNat_le).2 hlower, (Int.ofNat_le).2 hupper⟩
  · rintro ⟨hlower, hupper⟩
    exact ⟨(Int.ofNat_le).1 hlower, (Int.ofNat_le).1 hupper⟩

def IsHexDigitCode (code : Int) : Prop :=
  (48 ≤ code ∧ code ≤ 57) ∨
    (97 ≤ code ∧ code ≤ 102) ∨
      (65 ≤ code ∧ code ≤ 70)

theorem hexDigit_iff_encoded (character : Char) :
    TokClass.hexDigit.mem character ↔
      IsHexDigitCode (Int.ofNat character.toNat) := by
  simp only [TokClass.mem, IsHexDigitCode, Char.le_def,
    UInt32.le_iff_toNat_le, Char.toNat]
  norm_num

theorem hexDigits_all_iff_encoded (source : String) :
    TokClass.hexDigit.all source ↔
      ∀ index : Int,
        0 ≤ index ∧ index < Vermilion.Seq.len (encodeString source) →
          IsHexDigitCode
            (Vermilion.Seq.index (encodeString source) index) := by
  constructor
  · intro hall index hindex
    have hbound : index.toNat < source.toList.length := by
      apply (Int.toNat_lt hindex.1).2
      simpa [encodeString, Vermilion.Seq.len] using hindex.2
    have hdigit := hall source.toList[index.toNat] (List.getElem_mem hbound)
    apply (hexDigit_iff_encoded source.toList[index.toNat]).1 at hdigit
    simpa [encodeString, Vermilion.Seq.index, hindex.1,
      List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hbound] using hdigit
  · intro hall character hcharacter
    rw [List.mem_iff_getElem] at hcharacter
    rcases hcharacter with ⟨index, hbound, hcharacter⟩
    subst character
    have hnonnegative : (0 : Int) ≤ Int.ofNat index :=
      Int.ofNat_nonneg index
    have hencodedBound :
        Int.ofNat index < Vermilion.Seq.len (encodeString source) := by
      rw [encodeString_length]
      apply (Int.ofNat_lt).2
      simpa [String.length_toList] using hbound
    have hdigit := hall (Int.ofNat index) ⟨hnonnegative, hencodedBound⟩
    apply (hexDigit_iff_encoded source.toList[index]).2
    simpa [encodeString, Vermilion.Seq.index, hnonnegative,
      List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hbound] using hdigit

theorem digits_all_iff_encoded (source : String) :
    TokClass.digit.all source ↔
      ∀ index : Int,
        0 ≤ index ∧ index < Vermilion.Seq.len (encodeString source) →
          IsDigitCode (Vermilion.Seq.index (encodeString source) index) := by
  constructor
  · intro hall index hindex
    have hbound : index.toNat < source.toList.length := by
      apply (Int.toNat_lt hindex.1).2
      simpa [encodeString, Vermilion.Seq.len] using hindex.2
    have hdigit := hall source.toList[index.toNat] (List.getElem_mem hbound)
    apply (digit_iff_encoded source.toList[index.toNat]).1 at hdigit
    simpa [encodeString, Vermilion.Seq.index, hindex.1,
      List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hbound] using hdigit
  · intro hall character hcharacter
    rw [List.mem_iff_getElem] at hcharacter
    rcases hcharacter with ⟨index, hbound, hcharacter⟩
    subst character
    have hnonnegative : (0 : Int) ≤ Int.ofNat index :=
      Int.ofNat_nonneg index
    have hencodedBound :
        Int.ofNat index < Vermilion.Seq.len (encodeString source) := by
      rw [encodeString_length]
      apply (Int.ofNat_lt).2
      simpa [String.length_toList] using hbound
    have hdigit := hall (Int.ofNat index) ⟨hnonnegative, hencodedBound⟩
    apply (digit_iff_encoded source.toList[index]).2
    simpa [encodeString, Vermilion.Seq.index, hnonnegative,
      List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hbound] using hdigit

theorem digits_iff_encoded (source : String) :
    Triptych.IsDigits source ↔
      ∃ digits : Vermilion.Seq Int,
        encodeString source = digits ∧
          1 ≤ Vermilion.Seq.len digits ∧
          ∀ index : Int,
            0 ≤ index ∧ index < Vermilion.Seq.len digits →
              IsDigitCode (Vermilion.Seq.index digits index) := by
  unfold Triptych.IsDigits
  constructor
  · rintro ⟨hdigits, hlength⟩
    refine ⟨encodeString source, rfl, ?_, (digits_all_iff_encoded source).1 hdigits⟩
    rw [encodeString_length]
    exact (Int.ofNat_le).2 hlength
  · rintro ⟨digits, hsource, hlength, hdigits⟩
    subst digits
    constructor
    · exact (digits_all_iff_encoded source).2 hdigits
    · rw [encodeString_length] at hlength
      exact (Int.ofNat_le).1 hlength

theorem digitsBetween_iff_encoded (lower upper : Nat) (source : String) :
    Triptych.IsDigitsBetween lower upper source ↔
      ∃ digits : Vermilion.Seq Int,
        encodeString source = digits ∧
          ((Int.ofNat lower ≤ Vermilion.Seq.len digits ∧
              Vermilion.Seq.len digits ≤ Int.ofNat upper) ∧
            ∀ index : Int,
              0 ≤ index ∧ index < Vermilion.Seq.len digits →
                IsDigitCode (Vermilion.Seq.index digits index)) := by
  unfold Triptych.IsDigitsBetween
  constructor
  · rintro ⟨hdigits, hlower, hupper⟩
    refine ⟨encodeString source, rfl, ?_, (digits_all_iff_encoded source).1 hdigits⟩
    rw [encodeString_length]
    exact ⟨(Int.ofNat_le).2 hlower, (Int.ofNat_le).2 hupper⟩
  · rintro ⟨digits, hsource, ⟨hlower, hupper⟩, hdigits⟩
    subst digits
    constructor
    · exact (digits_all_iff_encoded source).2 hdigits
    · rw [encodeString_length] at hlower hupper
      exact ⟨(Int.ofNat_le).1 hlower, (Int.ofNat_le).1 hupper⟩

theorem fixedDigits_iff_encoded (width : Nat) (source : String) :
    Triptych.IsFixedDigits width source ↔
      ∃ digits : Vermilion.Seq Int,
        encodeString source = digits ∧
          Vermilion.Seq.len digits = Int.ofNat width ∧
          ∀ index : Int,
            0 ≤ index ∧ index < Vermilion.Seq.len digits →
              IsDigitCode (Vermilion.Seq.index digits index) := by
  unfold Triptych.IsFixedDigits
  constructor
  · rintro ⟨hdigits, hlength⟩
    refine ⟨encodeString source, rfl, ?_, (digits_all_iff_encoded source).1 hdigits⟩
    rw [encodeString_length, hlength]
  · rintro ⟨digits, hsource, hlength, hdigits⟩
    subst digits
    constructor
    · exact (digits_all_iff_encoded source).2 hdigits
    · rw [encodeString_length] at hlength
      exact Int.ofNat_injective hlength

theorem hexDigitsBetween_iff_encoded (lower upper : Nat) (source : String) :
    Triptych.IsHexDigitsBetween lower upper source ↔
      ∃ digits : Vermilion.Seq Int,
        encodeString source = digits ∧
          ((Int.ofNat lower ≤ Vermilion.Seq.len digits ∧
              Vermilion.Seq.len digits ≤ Int.ofNat upper) ∧
            ∀ index : Int,
              0 ≤ index ∧ index < Vermilion.Seq.len digits →
                IsHexDigitCode (Vermilion.Seq.index digits index)) := by
  unfold Triptych.IsHexDigitsBetween
  constructor
  · rintro ⟨hdigits, hlower, hupper⟩
    refine ⟨encodeString source, rfl, ?_, (hexDigits_all_iff_encoded source).1 hdigits⟩
    rw [encodeString_length]
    exact ⟨(Int.ofNat_le).2 hlower, (Int.ofNat_le).2 hupper⟩
  · rintro ⟨digits, hsource, ⟨hlower, hupper⟩, hdigits⟩
    subst digits
    constructor
    · exact (hexDigits_all_iff_encoded source).2 hdigits
    · rw [encodeString_length] at hlower hupper
      exact ⟨(Int.ofNat_le).1 hlower, (Int.ofNat_le).1 hupper⟩

theorem digit_sequence_range (sequence : Vermilion.Seq Int)
    (hdigits : ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        IsDigitCode (Vermilion.Seq.index sequence index)) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  intro index hindex
  have hdigit := hdigits index hindex
  unfold IsDigitCode at hdigit
  unfold Vermilion.isUnicodeScalar
  omega

theorem digit_witness_sequence_range
    (sequence : Vermilion.Seq Int) (condition : Vermilion.Seq Int → Prop)
    (hwf :
      ∃ digits : Vermilion.Seq Int,
        sequence = digits ∧ condition digits ∧
          ∀ index : Int,
            0 ≤ index ∧ index < Vermilion.Seq.len digits →
              IsDigitCode (Vermilion.Seq.index digits index)) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  rcases hwf with ⟨digits, rfl, _, hdigits⟩
  exact digit_sequence_range sequence hdigits

theorem hex_sequence_range (sequence : Vermilion.Seq Int)
    (hdigits : ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        IsHexDigitCode (Vermilion.Seq.index sequence index)) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  intro index hindex
  have hdigit := hdigits index hindex
  unfold IsHexDigitCode at hdigit
  unfold Vermilion.isUnicodeScalar
  omega

theorem hex_witness_sequence_range
    (sequence : Vermilion.Seq Int) (condition : Vermilion.Seq Int → Prop)
    (hwf :
      ∃ digits : Vermilion.Seq Int,
        sequence = digits ∧ condition digits ∧
          ∀ index : Int,
            0 ≤ index ∧ index < Vermilion.Seq.len digits →
              IsHexDigitCode (Vermilion.Seq.index digits index)) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  rcases hwf with ⟨digits, rfl, _, hdigits⟩
  exact hex_sequence_range sequence hdigits

theorem encode_decode_character {code : Int}
    (hcode : Vermilion.isUnicodeScalar code) :
    Int.ofNat (Char.ofNat code.toNat).toNat = code := by
  have hnonnegative : 0 ≤ code := by
    rcases hcode with hcode | hcode <;> omega
  have hvalid : code.toNat.isValidChar := by
    rcases hcode with hcode | hcode
    · left
      apply (Int.toNat_lt hnonnegative).2
      omega
    · right
      constructor
      · apply Int.lt_toNat.mpr
        omega
      · apply (Int.toNat_lt hnonnegative).2
        omega
  rw [Char.toNat_ofNat, if_pos hvalid]
  exact Int.toNat_of_nonneg hnonnegative

theorem encode_decode_sequence (sequence : Vermilion.Seq Int)
    (hsequence : ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index)) :
    encodeString (decodeSequence sequence) = sequence := by
  apply List.ext_getElem
  · simp [encodeString, decodeSequence]
  · intro index hleft hright
    have hnonnegative : (0 : Int) ≤ Int.ofNat index := Int.ofNat_nonneg index
    have hbound : Int.ofNat index < Vermilion.Seq.len sequence := by
      simp only [Vermilion.Seq.len]
      exact (Int.ofNat_lt (n := index) (m := sequence.length)).2 hright
    have hscalar := hsequence (Int.ofNat index) ⟨hnonnegative, hbound⟩
    have hscalar' : Vermilion.isUnicodeScalar sequence[index] := by
      simpa [Vermilion.Seq.index, hnonnegative,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hright] using hscalar
    simpa [encodeString, decodeSequence] using encode_decode_character hscalar'

theorem decode_fixed_digits
    (sequence : Vermilion.Seq Int) (width : Nat)
    (hwf :
      ∃ digits : Vermilion.Seq Int,
        sequence = digits ∧
          Vermilion.Seq.len digits = Int.ofNat width ∧
          ∀ index : Int,
            0 ≤ index ∧ index < Vermilion.Seq.len digits →
              IsDigitCode (Vermilion.Seq.index digits index)) :
    ∃ text : String,
      sequence = encodeString text ∧ Triptych.IsFixedDigits width text := by
  rcases hwf with ⟨digits, rfl, hlength, hdigits⟩
  let text := decodeSequence sequence
  have hencode : encodeString text = sequence :=
    encode_decode_sequence sequence (digit_sequence_range sequence hdigits)
  refine ⟨text, hencode.symm, ?_⟩
  apply (fixedDigits_iff_encoded width text).2
  exact ⟨sequence, hencode, hlength, hdigits⟩

theorem decode_optional_fixed_digits
    (sequence : Vermilion.Seq Int) (width : Nat)
    (hwf :
      sequence = Vermilion.Seq.empty ∨
        ∃ digits : Vermilion.Seq Int,
          sequence = digits ∧
            Vermilion.Seq.len digits = Int.ofNat width ∧
            ∀ index : Int,
              0 ≤ index ∧ index < Vermilion.Seq.len digits →
                IsDigitCode (Vermilion.Seq.index digits index)) :
    ∃ text : String, sequence = encodeString text := by
  rcases hwf with hempty | hfixed
  · subst sequence
    exact ⟨"", by simp [encodeString, Vermilion.Seq.empty]⟩
  · obtain ⟨text, hencode, _⟩ := decode_fixed_digits sequence width hfixed
    exact ⟨text, hencode⟩

theorem sequence_add_range (left right : Vermilion.Seq Int)
    (hleft : ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len left →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index left index))
    (hright : ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len right →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index right index)) :
    ∀ index : Int,
      0 ≤ index ∧
          index < Vermilion.Seq.len (Vermilion.Seq.add left right) →
        Vermilion.isUnicodeScalar
          (Vermilion.Seq.index (Vermilion.Seq.add left right) index) := by
  intro index hindex
  by_cases hinLeft : index < Vermilion.Seq.len left
  · rw [Vermilion.Seq.index_add_left left right index hindex.1 hinLeft]
    exact hleft index ⟨hindex.1, hinLeft⟩
  · have hleftBound : Vermilion.Seq.len left ≤ index := by omega
    have hrightIndex : 0 ≤ index - Vermilion.Seq.len left := by omega
    have hrightBound :
        index - Vermilion.Seq.len left < Vermilion.Seq.len right := by
      rw [Vermilion.Seq.len_add] at hindex
      omega
    rw [Vermilion.Seq.index_add_right left right index hleftBound]
    exact hright _ ⟨hrightIndex, hrightBound⟩

theorem sequence_eq_empty_of_length_zero (sequence : Vermilion.Seq Int)
    (hlength : Vermilion.Seq.len sequence = 0) :
    sequence = Vermilion.Seq.empty := by
  apply List.eq_nil_of_length_eq_zero
  simpa [Vermilion.Seq.len] using hlength

theorem empty_sequence_range (sequence : Vermilion.Seq Int)
    (hlength : Vermilion.Seq.len sequence = 0) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  intro index hindex
  omega

theorem subrange_zero_eq_take {α : Type} (sequence : Vermilion.Seq α)
    (stop : Int) (hstop : 0 ≤ stop) :
    sequence.subrange 0 stop = sequence.take stop.toNat := by
  simp [Vermilion.Seq.subrange]

theorem subrange_to_len_eq_drop {α : Type} (sequence : Vermilion.Seq α)
    (start : Int) (hstart : 0 ≤ start)
    (hbound : start ≤ sequence.len) :
    sequence.subrange start sequence.len = sequence.drop start.toNat := by
  unfold Vermilion.Seq.subrange
  have hlength :
      (sequence.len - start).toNat =
        (sequence.drop start.toNat).length := by
    simp only [Vermilion.Seq.len, List.length_drop] at hbound ⊢
    omega
  rw [hlength]
  simp

theorem subrange_three_way {α : Type} (sequence : Vermilion.Seq α)
    (split : Int) (hsplit : 0 ≤ split)
    (hbound : split + 1 ≤ sequence.len) :
    sequence =
      sequence.subrange 0 split ++
        sequence.subrange split (split + 1) ++
          sequence.subrange (split + 1) sequence.len := by
  have hprefix :
      sequence.subrange 0 split = sequence.take split.toNat :=
    subrange_zero_eq_take sequence split hsplit
  have hmiddle :
      sequence.subrange split (split + 1) =
        (sequence.drop split.toNat).take 1 := by
    simp [Vermilion.Seq.subrange]
  have hsuffix :
      sequence.subrange (split + 1) sequence.len =
        sequence.drop (split + 1).toNat :=
    subrange_to_len_eq_drop sequence (split + 1) (by omega) hbound
  rw [hprefix, hmiddle, hsuffix]
  have hsucc : (split + 1).toNat = split.toNat + 1 := by omega
  rw [hsucc, ← List.drop_drop]
  calc
    sequence =
        sequence.take split.toNat ++ sequence.drop split.toNat :=
      (List.take_append_drop split.toNat sequence).symm
    _ =
        sequence.take split.toNat ++
          ((sequence.drop split.toNat).take 1 ++
            (sequence.drop split.toNat).drop 1) := by
      exact congrArg (sequence.take split.toNat ++ ·)
        (List.take_append_drop 1 (sequence.drop split.toNat)).symm
    _ =
        sequence.take split.toNat ++
          (sequence.drop split.toNat).take 1 ++
            (sequence.drop split.toNat).drop 1 := by
      simp [List.append_assoc]

theorem intercalate_cons_of_ne_nil {α : Type} (separator head : List α)
    (tail : List (List α)) (htail : tail ≠ []) :
    separator.intercalate (head :: tail) =
      head ++ separator ++ separator.intercalate tail := by
  cases tail with
  | nil => exact absurd rfl htail
  | cons next rest => simp [List.intercalate, List.append_assoc]

theorem empty_or_singleton_sequence_range
    (sequence literal : Vermilion.Seq Int) (code : Int)
    (hsequence : sequence = literal)
    (hliteral :
      Vermilion.Seq.len literal = 0 ∨
        literal = Vermilion.Seq.push Vermilion.Seq.empty code)
    (hcode : Vermilion.isUnicodeScalar code) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  intro index hindex
  rcases hliteral with hempty | hsingleton
  · rw [hsequence, hempty] at hindex
    omega
  · rw [hsequence, hsingleton] at hindex ⊢
    simp [Vermilion.Seq.len, Vermilion.Seq.push, Vermilion.Seq.empty] at hindex
    have hzero : index = 0 := by omega
    subst index
    simpa [Vermilion.Seq.index, Vermilion.Seq.push, Vermilion.Seq.empty] using hcode

theorem optional_minus_sequence_range
    (sequence : Vermilion.Seq Int)
    (hwf :
      ∃ literal : Vermilion.Seq Int,
        sequence = literal ∧
          (Vermilion.Seq.len literal = 0 ∨
            literal = Vermilion.Seq.push Vermilion.Seq.empty 45)) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  rcases hwf with ⟨literal, hsequence, hliteral⟩
  exact empty_or_singleton_sequence_range sequence literal 45 hsequence hliteral
    (by simp [Vermilion.isUnicodeScalar])

theorem suffixed_sequence_range
    (sequence digits : Vermilion.Seq Int) (suffix : String)
    (hsequence : sequence = Vermilion.Seq.add digits (encodeString suffix))
    (hdigits : ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len digits →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index digits index)) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  subst sequence
  exact sequence_add_range digits (encodeString suffix) hdigits (encodeString_range suffix)

theorem optional_suffixed_sequence_range
    (sequence : Vermilion.Seq Int) (suffix : String)
    (hwf : Vermilion.Seq.len sequence = 0 ∨
      ∃ digits : Vermilion.Seq Int,
        sequence = Vermilion.Seq.add digits (encodeString suffix) ∧
          (∀ index : Int,
            0 ≤ index ∧ index < Vermilion.Seq.len digits →
              Vermilion.isUnicodeScalar (Vermilion.Seq.index digits index))) :
    ∀ index : Int,
      0 ≤ index ∧ index < Vermilion.Seq.len sequence →
        Vermilion.isUnicodeScalar (Vermilion.Seq.index sequence index) := by
  rcases hwf with hempty | ⟨digits, hsequence, hdigits⟩
  · intro index hindex
    rw [hempty] at hindex
    omega
  · exact suffixed_sequence_range sequence digits suffix hsequence hdigits

def recoveredDigit (byte : Int) : Int :=
  if byte < 48 then 0 else byte - 48

theorem natFrom_eq_fold
    (natFrom : List Int → Int → Int → Int)
    (hstep : ∀ bytes index accumulator,
      0 ≤ Vermilion.Seq.len bytes - index →
        natFrom bytes index accumulator =
          if index < Vermilion.Seq.len bytes then
            natFrom bytes (index + 1)
              (accumulator * 10 +
                recoveredDigit (Vermilion.Seq.index bytes index))
          else accumulator)
    (bytes : List Int) (index : Nat) (accumulator : Int)
    (hindex : index ≤ bytes.length) :
    natFrom bytes (Int.ofNat index) accumulator =
      (bytes.drop index).foldl
        (fun current byte => current * 10 + recoveredDigit byte)
        accumulator := by
  have hrange :
      (0 : Int) ≤ Vermilion.Seq.len bytes - Int.ofNat index := by
    simp only [Vermilion.Seq.len]
    exact Int.sub_nonneg.mpr ((Int.ofNat_le).2 hindex)
  rw [hstep bytes (Int.ofNat index) accumulator hrange]
  by_cases hlt : index < bytes.length
  · have hltInt : Int.ofNat index < Vermilion.Seq.len bytes := by
      simp only [Vermilion.Seq.len]
      exact (Int.ofNat_lt).2 hlt
    rw [if_pos hltInt]
    have hnext : index + 1 ≤ bytes.length := by omega
    have hindexStep : Int.ofNat index + 1 = Int.ofNat (index + 1) := by simp
    rw [hindexStep, natFrom_eq_fold natFrom hstep bytes (index + 1) _ hnext]
    rw [List.drop_eq_getElem_cons hlt]
    simp only [List.foldl_cons]
    simp [Vermilion.Seq.index, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hlt]
  · have hltInt : ¬Int.ofNat index < Vermilion.Seq.len bytes := by
      intro h
      apply hlt
      exact (Int.ofNat_lt).1 (by simpa [Vermilion.Seq.len] using h)
    rw [if_neg hltInt]
    have heq : index = bytes.length :=
      Nat.le_antisymm hindex (Nat.le_of_not_gt hlt)
    simp [heq]
termination_by bytes.length - index
decreasing_by omega

theorem foldEncoded_eq_digitBytes
    (characters : List Char) (accumulator : Int) :
    (characters.map (fun character => Int.ofNat character.toNat)).foldl
        (fun current byte => current * 10 + recoveredDigit byte)
        accumulator =
      Triptych.Backend.Verus.foldDigitBytes
        (characters.map Char.toNat) accumulator := by
  induction characters generalizing accumulator with
  | nil => rfl
  | cons character rest ih =>
      simp only [List.map_cons, List.foldl_cons,
        Triptych.Backend.Verus.foldDigitBytes]
      rw [ih]
      rfl

theorem encodedDigitFold_eq_natOf (source : String) :
    (encodeString source).foldl
        (fun current byte => current * 10 + recoveredDigit byte) 0 =
      Triptych.natOf source := by
  unfold encodeString
  rw [foldEncoded_eq_digitBytes]
  simpa [Triptych.Backend.Verus.natOfBytes,
    Triptych.Backend.Verus.natOfBytesFrom,
    Triptych.Backend.Verus.Ast.encodeString] using
      Triptych.Backend.Verus.natOfBytes_encodeString source

def recoveredSignOf (bytes : Vermilion.Seq Int) : Int :=
  Vermilion.iteP
    (Vermilion.Seq.len bytes > 0 ∧ Vermilion.Seq.index bytes 0 = 45)
    (0 - 1) 1

theorem recoveredSignOf_encodeString (source : String) :
    recoveredSignOf (encodeString source) = Triptych.signOf source := by
  rw [← Triptych.Backend.Verus.signOfBytes_encodeString source]
  cases hsource : source.toList with
  | nil =>
      simp [recoveredSignOf, encodeString, Triptych.Backend.Verus.Ast.encodeString,
        Triptych.Backend.Verus.signOfBytes, hsource, Vermilion.Seq.len,
        Vermilion.Seq.index, Vermilion.iteP]
  | cons character rest =>
      by_cases hminus : character = '-'
      · subst character
        simp [recoveredSignOf, encodeString, Triptych.Backend.Verus.Ast.encodeString,
          Triptych.Backend.Verus.signOfBytes, hsource, Vermilion.Seq.len,
          Vermilion.Seq.index, Vermilion.iteP]
      · have hcode : Int.ofNat character.toNat ≠ 45 := by
          intro h
          apply hminus
          apply Char.toNat_inj.mp
          exact Int.ofNat_inj.mp h
        have hcodeNat : character.toNat ≠ 45 := by
          intro h
          apply hminus
          exact Char.toNat_inj.mp h
        have hcast : (character.toNat : Int) ≠ 45 := hcode
        simp [recoveredSignOf, encodeString, Triptych.Backend.Verus.Ast.encodeString,
          Triptych.Backend.Verus.signOfBytes, hsource, hcast, hcodeNat,
          Vermilion.Seq.len, Vermilion.Seq.index, Vermilion.iteP]

theorem natOf_emod_eq_tmod (source : String) (modulus : Nat) :
    Triptych.natOf source % Int.ofNat modulus =
      Int.tmod (Triptych.natOf source) (Int.ofNat modulus) := by
  unfold Triptych.natOf
  simp [Int.tmod]

end Triptych.Vermilion.String
