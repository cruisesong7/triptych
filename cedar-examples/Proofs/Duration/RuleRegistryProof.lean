import Proofs.Duration.GrammarView
import CedarSupport.DurationParserInternals
import CedarSupport.ParserRules
import Triptych.Automation.ExternalParser

/-!
# Duration executable-parser rules

This module proves successful-path summaries directly from Cedar's executable Duration parser.
It imports Cedar's private executable helpers with `import all`, but no theorem from
`Cedar.Thm.Ext.Duration.Lemmas` or `Cedar.Thm.Ext.Duration`.
-/

open Cedar.Spec.Ext
open Cedar.Spec.Ext.Datetime
open CedarSupport.DurationParserInternals
open CedarSupport.ParserRules
open Triptych

namespace Duration.RuleRegistryProof

set_option maxHeartbeats 800000
set_option maxRecDepth 2000

def signedNat (isNegative : Bool) (digits : String) : Int :=
  if isNegative then -(Triptych.natOf digits) else Triptych.natOf digits

def unitValue (isNegative : Bool) (suffix : String) : Option String → Int
  | none => 0
  | some digits =>
      let quantity := signedNat isNegative digits
      match suffix with
      | "ms" => quantity
      | "s" => quantity * 1000
      | "m" => quantity * 60000
      | "h" => quantity * 3600000
      | "d" => quantity * 86400000
      | _ => 0

def digitString (str suffix : String) : Option String :=
  if str.endsWith suffix then
    let rest := (str.dropEnd suffix.length).toString
    let digits := (rest.toList.reverse.takeWhile Char.isDigit).reverse
    if digits.isEmpty then none else some (String.ofList digits)
  else
    none

private theorem durationUnits_eq_unitValue (isNegative : Bool) (digits suffix : String)
    (hsuffix :
      suffix = "ms" ∨ suffix = "s" ∨ suffix = "m" ∨ suffix = "h" ∨ suffix = "d")
    (hbounds :
      Int64.«MIN» ≤ signedNat isNegative digits ∧
        signedNat isNegative digits ≤ Int64.«MAX») :
    durationUnits?
        (if isNegative then Int.negOfNat (Triptych.readNat digits)
          else Int.ofNat (Triptych.readNat digits)) suffix =
      some (unitValue isNegative suffix (some digits)) := by
  have hsigned :
      (if isNegative then Int.negOfNat (Triptych.readNat digits)
        else Int.ofNat (Triptych.readNat digits)) =
        signedNat isNegative digits := by
    cases isNegative <;> simp [signedNat, Triptych.natOf, Int.negOfNat_eq]
  rw [hsigned]
  have hofInt :
      Int64.ofInt? (signedNat isNegative digits) =
        some (Int64.ofInt (signedNat isNegative digits)) :=
    (Int64.ofInt?_some_iff (i := signedNat isNegative digits)).mp hbounds
  unfold durationUnits?
  rw [hofInt]
  have htoInt :
      (Int64.ofInt (signedNat isNegative digits)).toInt =
        signedNat isNegative digits :=
    Int64.ofInt?_some_toInt hofInt
  rcases hsuffix with rfl | rfl | rfl | rfl | rfl <;>
    simp [unitValue, htoInt, Cedar.Spec.Ext.Datetime.MILLISECONDS_PER_SECOND,
      Cedar.Spec.Ext.Datetime.MILLISECONDS_PER_MINUTE,
      Cedar.Spec.Ext.Datetime.MILLISECONDS_PER_HOUR,
      Cedar.Spec.Ext.Datetime.MILLISECONDS_PER_DAY]

private theorem parseUnit_present_value (isNegative : Bool) (pfx digits suffix : String)
    (hsuffix :
      suffix = "ms" ∨ suffix = "s" ∨ suffix = "m" ∨ suffix = "h" ∨ suffix = "d")
    (hdigits : Triptych.IsDigits digits)
    (hpfxStop :
      pfx = "" ∨
        ∃ c cs, pfx.toList.reverse = c :: cs ∧ c.isDigit = false)
    (hbounds :
      Int64.«MIN» ≤ signedNat isNegative digits ∧
        signedNat isNegative digits ≤ Int64.«MAX») :
    parseUnit? isNegative (pfx ++ digits ++ suffix) suffix =
      some (unitValue isNegative suffix (some digits), pfx) := by
  have hcedarDigits := (CedarSupport.String.digits_iff digits).mp hdigits
  have hlistNonempty : digits.toList ≠ [] := by
    intro hnil
    have hpositive := hcedarDigits.1
    rw [← String.length_toList, hnil] at hpositive
    simp at hpositive
  have hnat :
      toNat?' digits = some (Triptych.readNat digits) :=
    (toNat?_eq_some_iff).mpr ⟨hdigits, rfl⟩
  exact CedarSupport.DurationParserInternals.parseUnit_present isNegative pfx digits
    suffix (Triptych.readNat digits) (unitValue isNegative suffix (some digits))
    hlistNonempty hcedarDigits.2 hnat hpfxStop
    (durationUnits_eq_unitValue isNegative digits suffix hsuffix hbounds)

def OptionalSignedBounds (isNegative : Bool) : Option String → Prop
  | none => True
  | some digits =>
      Int64.«MIN» ≤ signedNat isNegative digits ∧
        signedNat isNegative digits ≤ Int64.«MAX»

private theorem parseOptionalUnit (isNegative : Bool) (pfx suffix : String)
    (digits : Option String)
    (hsuffix :
      suffix = "ms" ∨ suffix = "s" ∨ suffix = "m" ∨ suffix = "h" ∨ suffix = "d")
    (hwf : Duration.GrammarView.OptionalDigitsWf digits)
    (hpfxStop :
      pfx = "" ∨
        ∃ c cs, pfx.toList.reverse = c :: cs ∧ c.isDigit = false)
    (hpfxNoSuffix : pfx.endsWith suffix = false)
    (hbounds : OptionalSignedBounds isNegative digits) :
    parseUnit? isNegative
        (pfx ++ Cedar.Thm.Duration.durationChunk digits suffix) suffix =
      some (unitValue isNegative suffix digits, pfx) := by
  cases digits with
  | none =>
      simpa [Cedar.Thm.Duration.durationChunk, unitValue] using
        CedarSupport.DurationParserInternals.parseUnit_absent
          isNegative pfx suffix hpfxNoSuffix
  | some digits =>
      simpa [Cedar.Thm.Duration.durationChunk, String.append_assoc] using
        parseUnit_present_value isNegative pfx digits suffix hsuffix hwf hpfxStop hbounds

private theorem chunks4_stop
    (days hours minutes seconds : Option String) :
    let pfx :=
      Cedar.Thm.Duration.durationChunk days "d" ++
        Cedar.Thm.Duration.durationChunk hours "h" ++
        Cedar.Thm.Duration.durationChunk minutes "m" ++
        Cedar.Thm.Duration.durationChunk seconds "s"
    pfx = "" ∨
      ∃ c cs, pfx.toList.reverse = c :: cs ∧ c.isDigit = false := by
  rcases days with _ | days <;> rcases hours with _ | hours <;>
    rcases minutes with _ | minutes <;> rcases seconds with _ | seconds <;>
    simp [Cedar.Thm.Duration.durationChunk, String.toList_append]

private theorem chunks3_stop
    (days hours minutes : Option String) :
    let pfx :=
      Cedar.Thm.Duration.durationChunk days "d" ++
        Cedar.Thm.Duration.durationChunk hours "h" ++
        Cedar.Thm.Duration.durationChunk minutes "m"
    pfx = "" ∨
      ∃ c cs, pfx.toList.reverse = c :: cs ∧ c.isDigit = false := by
  simpa [Cedar.Thm.Duration.durationChunk] using
    chunks4_stop days hours minutes none

private theorem chunks2_stop (days hours : Option String) :
    let pfx :=
      Cedar.Thm.Duration.durationChunk days "d" ++
        Cedar.Thm.Duration.durationChunk hours "h"
    pfx = "" ∨
      ∃ c cs, pfx.toList.reverse = c :: cs ∧ c.isDigit = false := by
  simpa [Cedar.Thm.Duration.durationChunk] using
    chunks3_stop days hours none

private theorem chunks1_stop (days : Option String) :
    let pfx := Cedar.Thm.Duration.durationChunk days "d"
    pfx = "" ∨
      ∃ c cs, pfx.toList.reverse = c :: cs ∧ c.isDigit = false := by
  simpa [Cedar.Thm.Duration.durationChunk] using chunks2_stop days none

private theorem not_endsWith_ms_of_digits_s (pfx digits : String)
    (hdigits : Triptych.IsDigits digits) :
    (pfx ++ digits ++ "s").endsWith "ms" = false := by
  have hcedarDigits := (CedarSupport.String.digits_iff digits).mp hdigits
  simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice,
    String.toList_append]
  intro ⟨pre, hpre⟩
  have hne : digits.toList ≠ [] := by
    intro hnil
    have hpositive := hcedarDigits.1
    rw [← String.length_toList, hnil] at hpositive
    simp at hpositive
  have hlength :
      pre.length + 2 = pfx.toList.length + digits.toList.length + 1 := by
    have h := congrArg List.length hpre
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    omega
  have hge : pre.length ≥ pfx.toList.length := by
    have : digits.toList.length ≥ 1 := by
      cases h : digits.toList with
      | nil => exact absurd h hne
      | cons _ _ => simp
    omega
  have hlt : pre.length - pfx.toList.length < digits.toList.length := by
    omega
  have hindex :
      (pre ++ ['m', 's'])[pre.length]? =
        (pfx.toList ++ (digits.toList ++ ['s']))[pre.length]? := by
    rw [hpre]
  have hlhs : (pre ++ ['m', 's'])[pre.length]? = some 'm' := by
    simp
  have hrhs :
      (pfx.toList ++ (digits.toList ++ ['s']))[pre.length]? =
        some (digits.toList[pre.length - pfx.toList.length]'hlt) := by
    rw [List.getElem?_append_right hge, List.getElem?_append_left hlt,
      List.getElem?_eq_getElem]
  rw [hlhs, hrhs] at hindex
  have hm : 'm' = digits.toList[pre.length - pfx.toList.length] :=
    Option.some.inj hindex
  have hmem : digits.toList[pre.length - pfx.toList.length]'hlt ∈ digits.toList :=
    List.getElem_mem hlt
  have hdigit := hcedarDigits.2 _ hmem
  rw [← hm] at hdigit
  exact absurd hdigit (by decide)

private theorem chunks4_not_ms
    (days hours minutes seconds : Option String)
    (hwfSeconds : Duration.GrammarView.OptionalDigitsWf seconds) :
    (Cedar.Thm.Duration.durationChunk days "d" ++
      Cedar.Thm.Duration.durationChunk hours "h" ++
      Cedar.Thm.Duration.durationChunk minutes "m" ++
      Cedar.Thm.Duration.durationChunk seconds "s").endsWith "ms" = false := by
  cases seconds with
  | none =>
      rcases minutes with _ | minutes <;> rcases hours with _ | hours <;>
        rcases days with _ | days <;>
        simp [Cedar.Thm.Duration.durationChunk,
          String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice,
          String.toList_append] <;>
        (intro ⟨pfx, hpfx⟩
         have h := congrArg List.getLast? hpfx
         simp [List.getLast?_append, List.getLast?_cons] at h)
  | some seconds =>
      simpa [Cedar.Thm.Duration.durationChunk, String.append_assoc] using
        not_endsWith_ms_of_digits_s
          (Cedar.Thm.Duration.durationChunk days "d" ++
            Cedar.Thm.Duration.durationChunk hours "h" ++
            Cedar.Thm.Duration.durationChunk minutes "m")
          seconds hwfSeconds

private theorem chunks3_not_s (days hours minutes : Option String) :
    (Cedar.Thm.Duration.durationChunk days "d" ++
      Cedar.Thm.Duration.durationChunk hours "h" ++
      Cedar.Thm.Duration.durationChunk minutes "m").endsWith "s" = false := by
  rcases minutes with _ | minutes <;> rcases hours with _ | hours <;>
    rcases days with _ | days <;>
    simp [Cedar.Thm.Duration.durationChunk,
      String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice,
      String.toList_append] <;>
    (intro ⟨pfx, hpfx⟩
     have h := congrArg List.getLast? hpfx
     simp [List.getLast?_append, List.getLast?_cons] at h)

private theorem chunks2_not_m (days hours : Option String) :
    (Cedar.Thm.Duration.durationChunk days "d" ++
      Cedar.Thm.Duration.durationChunk hours "h").endsWith "m" = false := by
  rcases hours with _ | hours <;> rcases days with _ | days <;>
    simp [Cedar.Thm.Duration.durationChunk,
      String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice,
      String.toList_append] <;>
    (intro ⟨pfx, hpfx⟩
     have h := congrArg List.getLast? hpfx
     simp [List.getLast?_append, List.getLast?_cons] at h)

private theorem chunks1_not_h (days : Option String) :
    (Cedar.Thm.Duration.durationChunk days "d").endsWith "h" = false := by
  rcases days with _ | days
  · decide
  · simp [Cedar.Thm.Duration.durationChunk,
      String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice,
      String.toList_append]

private theorem digitString_optional (pfx suffix : String)
    (digits : Option String)
    (hwf : Duration.GrammarView.OptionalDigitsWf digits)
    (hpfxStop :
      pfx = "" ∨
        ∃ c cs, pfx.toList.reverse = c :: cs ∧ c.isDigit = false)
    (hpfxNoSuffix : pfx.endsWith suffix = false) :
    digitString
        (pfx ++ Cedar.Thm.Duration.durationChunk digits suffix) suffix =
      digits := by
  cases digits with
  | none =>
      unfold digitString
      simp [Cedar.Thm.Duration.durationChunk, hpfxNoSuffix]
  | some digits =>
      have hcedarDigits := (CedarSupport.String.digits_iff digits).mp hwf
      have hlistNonempty : digits.toList ≠ [] := by
        intro hnil
        have hpositive := hcedarDigits.1
        rw [← String.length_toList, hnil] at hpositive
        simp at hpositive
      simpa only [Cedar.Thm.Duration.durationChunk, String.append_assoc,
        digitString, CedarSupport.DurationParserInternals.digitString] using
        (CedarSupport.DurationParserInternals.digitString_present
          pfx digits suffix hlistNonempty hcedarDigits.2 hpfxStop)

private theorem string_append_cancel_right {a b suffix : String}
    (h : a ++ suffix = b ++ suffix) :
    a = b := by
  have hlist :
      a.toList ++ suffix.toList = b.toList ++ suffix.toList := by
    simpa [String.toList_append] using congrArg String.toList h
  exact String.toList_inj.mp (List.append_cancel_right hlist)

private theorem components_asString_injective
    (left right : Cedar.Thm.Duration.Components)
    (hwfLeft : Duration.GrammarView.ComponentsWf left)
    (hwfRight : Duration.GrammarView.ComponentsWf right)
    (hrender : left.asString = right.asString) :
    left = right := by
  rcases left with ⟨d₁, h₁, m₁, s₁, ms₁⟩
  rcases right with ⟨d₂, h₂, m₂, s₂, ms₂⟩
  rcases hwfLeft with ⟨hwd₁, hwh₁, hwm₁, hws₁, hwms₁⟩
  rcases hwfRight with ⟨hwd₂, hwh₂, hwm₂, hws₂, hwms₂⟩
  change Duration.GrammarView.OptionalDigitsWf d₁ at hwd₁
  change Duration.GrammarView.OptionalDigitsWf h₁ at hwh₁
  change Duration.GrammarView.OptionalDigitsWf m₁ at hwm₁
  change Duration.GrammarView.OptionalDigitsWf s₁ at hws₁
  change Duration.GrammarView.OptionalDigitsWf ms₁ at hwms₁
  change Duration.GrammarView.OptionalDigitsWf d₂ at hwd₂
  change Duration.GrammarView.OptionalDigitsWf h₂ at hwh₂
  change Duration.GrammarView.OptionalDigitsWf m₂ at hwm₂
  change Duration.GrammarView.OptionalDigitsWf s₂ at hws₂
  change Duration.GrammarView.OptionalDigitsWf ms₂ at hwms₂
  unfold Cedar.Thm.Duration.Components.asString at hrender
  let p₄₁ :=
    Cedar.Thm.Duration.durationChunk d₁ "d" ++
      Cedar.Thm.Duration.durationChunk h₁ "h" ++
      Cedar.Thm.Duration.durationChunk m₁ "m" ++
      Cedar.Thm.Duration.durationChunk s₁ "s"
  let p₄₂ :=
    Cedar.Thm.Duration.durationChunk d₂ "d" ++
      Cedar.Thm.Duration.durationChunk h₂ "h" ++
      Cedar.Thm.Duration.durationChunk m₂ "m" ++
      Cedar.Thm.Duration.durationChunk s₂ "s"
  have hms₁ :
      digitString
          (p₄₁ ++ Cedar.Thm.Duration.durationChunk ms₁ "ms") "ms" =
        ms₁ :=
    digitString_optional p₄₁ "ms" ms₁ hwms₁
      (chunks4_stop d₁ h₁ m₁ s₁)
      (chunks4_not_ms d₁ h₁ m₁ s₁ hws₁)
  have hms₂ :
      digitString
          (p₄₂ ++ Cedar.Thm.Duration.durationChunk ms₂ "ms") "ms" =
        ms₂ :=
    digitString_optional p₄₂ "ms" ms₂ hwms₂
      (chunks4_stop d₂ h₂ m₂ s₂)
      (chunks4_not_ms d₂ h₂ m₂ s₂ hws₂)
  have hmilliseconds : ms₁ = ms₂ := by
    rw [← hms₁, ← hms₂]
    exact congrArg (fun input => digitString input "ms") hrender
  subst ms₂
  have hp₄ : p₄₁ = p₄₂ :=
    string_append_cancel_right hrender
  let p₃₁ :=
    Cedar.Thm.Duration.durationChunk d₁ "d" ++
      Cedar.Thm.Duration.durationChunk h₁ "h" ++
      Cedar.Thm.Duration.durationChunk m₁ "m"
  let p₃₂ :=
    Cedar.Thm.Duration.durationChunk d₂ "d" ++
      Cedar.Thm.Duration.durationChunk h₂ "h" ++
      Cedar.Thm.Duration.durationChunk m₂ "m"
  have hs₁ :
      digitString
          (p₃₁ ++ Cedar.Thm.Duration.durationChunk s₁ "s") "s" =
        s₁ :=
    digitString_optional p₃₁ "s" s₁ hws₁
      (chunks3_stop d₁ h₁ m₁) (chunks3_not_s d₁ h₁ m₁)
  have hs₂ :
      digitString
          (p₃₂ ++ Cedar.Thm.Duration.durationChunk s₂ "s") "s" =
        s₂ :=
    digitString_optional p₃₂ "s" s₂ hws₂
      (chunks3_stop d₂ h₂ m₂) (chunks3_not_s d₂ h₂ m₂)
  have hseconds : s₁ = s₂ := by
    rw [← hs₁, ← hs₂]
    exact congrArg (fun input => digitString input "s") hp₄
  subst s₂
  have hp₃ : p₃₁ = p₃₂ :=
    string_append_cancel_right hp₄
  let p₂₁ :=
    Cedar.Thm.Duration.durationChunk d₁ "d" ++
      Cedar.Thm.Duration.durationChunk h₁ "h"
  let p₂₂ :=
    Cedar.Thm.Duration.durationChunk d₂ "d" ++
      Cedar.Thm.Duration.durationChunk h₂ "h"
  have hm₁ :
      digitString
          (p₂₁ ++ Cedar.Thm.Duration.durationChunk m₁ "m") "m" =
        m₁ :=
    digitString_optional p₂₁ "m" m₁ hwm₁
      (chunks2_stop d₁ h₁) (chunks2_not_m d₁ h₁)
  have hm₂ :
      digitString
          (p₂₂ ++ Cedar.Thm.Duration.durationChunk m₂ "m") "m" =
        m₂ :=
    digitString_optional p₂₂ "m" m₂ hwm₂
      (chunks2_stop d₂ h₂) (chunks2_not_m d₂ h₂)
  have hminutes : m₁ = m₂ := by
    rw [← hm₁, ← hm₂]
    exact congrArg (fun input => digitString input "m") hp₃
  subst m₂
  have hp₂ : p₂₁ = p₂₂ :=
    string_append_cancel_right hp₃
  let p₁₁ := Cedar.Thm.Duration.durationChunk d₁ "d"
  let p₁₂ := Cedar.Thm.Duration.durationChunk d₂ "d"
  have hh₁ :
      digitString
          (p₁₁ ++ Cedar.Thm.Duration.durationChunk h₁ "h") "h" =
        h₁ :=
    digitString_optional p₁₁ "h" h₁ hwh₁
      (chunks1_stop d₁) (chunks1_not_h d₁)
  have hh₂ :
      digitString
          (p₁₂ ++ Cedar.Thm.Duration.durationChunk h₂ "h") "h" =
        h₂ :=
    digitString_optional p₁₂ "h" h₂ hwh₂
      (chunks1_stop d₂) (chunks1_not_h d₂)
  have hhours : h₁ = h₂ := by
    rw [← hh₁, ← hh₂]
    exact congrArg (fun input => digitString input "h") hp₂
  subst h₂
  have hp₁ : p₁₁ = p₁₂ :=
    string_append_cancel_right hp₂
  have hd₁ :
      digitString (Cedar.Thm.Duration.durationChunk d₁ "d") "d" = d₁ :=
    digitString_optional "" "d" d₁ hwd₁ (Or.inl rfl) (by decide)
  have hd₂ :
      digitString (Cedar.Thm.Duration.durationChunk d₂ "d") "d" = d₂ :=
    digitString_optional "" "d" d₂ hwd₂ (Or.inl rfl) (by decide)
  have hdays : d₁ = d₂ := by
    rw [← hd₁, ← hd₂]
    exact congrArg (fun input => digitString input "d") hp₁
  subst d₂
  rfl

private theorem parseUnit_reconstruct (isNegative : Bool) (s suffix : String)
    (v : Int) (rest : String)
    (hparse : parseUnit? isNegative s suffix = some (v, rest)) :
    s = rest ++ Cedar.Thm.Duration.durationChunk (digitString s suffix) suffix := by
  change
    s = rest ++
      (match CedarSupport.DurationParserInternals.digitString s suffix with
      | none => ""
      | some digits => digits ++ suffix)
  exact CedarSupport.DurationParserInternals.parseUnitReconstruct
    isNegative s suffix v rest hparse

private theorem digitString_wf (isNegative : Bool) (s suffix : String)
    (v : Int) (rest : String)
    (hparse : parseUnit? isNegative s suffix = some (v, rest)) :
    Duration.GrammarView.OptionalDigitsWf (digitString s suffix) := by
  unfold digitString
  by_cases hends : s.endsWith suffix = true
  · simp only [hends, if_true]
    have hparse' := hparse
    rw [CedarSupport.DurationParserInternals.parseUnit_eq_norm] at hparse'
    unfold CedarSupport.DurationParserInternals.parseUnitNorm? at hparse'
    simp only [hends, if_true] at hparse'
    generalize hdigits :
        ((s.dropEnd suffix.length).toString.toList.reverse.takeWhile
          Char.isDigit).reverse = digits at hparse'
    cases hempty : digits.isEmpty
    · simp only [hempty, Bool.false_eq_true, if_false, bind, Option.bind] at hparse'
      cases hnat : toNat?' (String.ofList digits) with
      | none => simp [hnat] at hparse'
      | some n =>
        exact (toNat?_eq_some_iff.mp hnat).1
    · simp [hempty] at hparse'
  · have hendsFalse : s.endsWith suffix = false := by
      cases h : s.endsWith suffix <;> simp_all
    simp [hendsFalse, Duration.GrammarView.OptionalDigitsWf]

private theorem parseUnit_value (isNegative : Bool) (s suffix : String)
    (v : Int) (rest : String)
    (hsuffix :
      suffix = "ms" ∨ suffix = "s" ∨ suffix = "m" ∨ suffix = "h" ∨ suffix = "d")
    (hparse : parseUnit? isNegative s suffix = some (v, rest)) :
    v = unitValue isNegative suffix (digitString s suffix) := by
  unfold digitString
  by_cases hends : s.endsWith suffix = true
  · simp only [hends, if_true]
    have hparse' := hparse
    rw [CedarSupport.DurationParserInternals.parseUnit_eq_norm] at hparse'
    unfold CedarSupport.DurationParserInternals.parseUnitNorm? at hparse'
    simp only [hends, if_true] at hparse'
    generalize hdigits :
        ((s.dropEnd suffix.length).toString.toList.reverse.takeWhile
          Char.isDigit).reverse = digits at hparse'
    cases hempty : digits.isEmpty
    · simp only [hempty, Bool.false_eq_true, if_false, bind, Option.bind] at hparse'
      cases hnat : toNat?' (String.ofList digits) with
      | none => simp [hnat] at hparse'
      | some n =>
        have hn := (toNat?_eq_some_iff.mp hnat).2
        have hofNat : Int.ofNat n = (n : Int) := rfl
        have hnegNat : Int.negOfNat n = -(n : Int) := by
          rw [Int.negOfNat_eq, hofNat]
        rw [hnat] at hparse'
        simp only [show (false = true) = False by simp, if_false]
        rcases hsuffix with rfl | rfl | rfl | rfl | rfl <;>
          simp only [unitValue, signedNat] at hparse' ⊢
        all_goals
          unfold Triptych.natOf at *
          rw [← hn] at *
          cases isNegative <;>
            simp only [Bool.false_eq_true, if_false, if_true] at hparse' ⊢
        all_goals
          unfold durationUnits? at hparse'
          cases hi : Int64.ofInt? _ with
          | none =>
            rw [hi] at hparse'
            simp at hparse'
          | some i =>
            rw [hi] at hparse'
            simp only [Option.some.injEq, Prod.mk.injEq] at hparse'
            have htoInt := Int64.ofInt?_some_toInt hi
            try simp only [Cedar.Spec.Ext.Datetime.MILLISECONDS_PER_SECOND,
              Cedar.Spec.Ext.Datetime.MILLISECONDS_PER_MINUTE,
              Cedar.Spec.Ext.Datetime.MILLISECONDS_PER_HOUR,
              Cedar.Spec.Ext.Datetime.MILLISECONDS_PER_DAY] at hparse' ⊢
            try rw [hofNat] at hparse'
            try rw [hnegNat] at hparse'
            omega
    · simp [hempty] at hparse'
  · have hendsFalse : s.endsWith suffix = false := by
      cases h : s.endsWith suffix <;> simp_all
    unfold parseUnit? at hparse
    simp only [hendsFalse, Bool.false_eq_true, if_false, Option.some.injEq,
      Prod.mk.injEq] at hparse
    simp [hendsFalse, unitValue, hparse.1]

/-- A successful unit peel exposes its optional digits, reconstruction, and contribution. -/
@[triptych_parser, triptych_parser_search .]
theorem parseUnit_result_of_eq_some {isNegative : Bool} {s suffix : String}
    {v : Int} {rest : String}
    (hsuffix :
      suffix = "ms" ∨ suffix = "s" ∨ suffix = "m" ∨ suffix = "h" ∨ suffix = "d")
    (hparse : parseUnit? isNegative s suffix = some (v, rest)) :
    ∃ digits,
      Duration.GrammarView.OptionalDigitsWf digits ∧
      s = rest ++ Cedar.Thm.Duration.durationChunk digits suffix ∧
      v = unitValue isNegative suffix digits := by
  refine ⟨digitString s suffix, digitString_wf _ _ _ _ _ hparse, ?_, ?_⟩
  · exact parseUnit_reconstruct _ _ _ _ _ hparse
  · exact parseUnit_value _ _ _ _ _ hsuffix hparse

def componentsValue (isNegative : Bool)
    (components : Cedar.Thm.Duration.Components) : Int :=
  unitValue isNegative "d" components.days +
    unitValue isNegative "h" components.hours +
    unitValue isNegative "m" components.minutes +
    unitValue isNegative "s" components.seconds +
    unitValue isNegative "ms" components.milliseconds

private theorem parse_milliseconds_step (isNegative : Bool)
    (components : Cedar.Thm.Duration.Components)
    (hwf : Duration.GrammarView.ComponentsWf components)
    (hbounds : OptionalSignedBounds isNegative components.milliseconds) :
    parseUnit? isNegative components.asString "ms" =
      some
        (unitValue isNegative "ms" components.milliseconds,
          Cedar.Thm.Duration.durationChunk components.days "d" ++
            Cedar.Thm.Duration.durationChunk components.hours "h" ++
            Cedar.Thm.Duration.durationChunk components.minutes "m" ++
            Cedar.Thm.Duration.durationChunk components.seconds "s") := by
  rcases components with ⟨days, hours, minutes, seconds, milliseconds⟩
  rcases hwf with ⟨hwfDays, hwfHours, hwfMinutes, hwfSeconds, hwfMilliseconds⟩
  simpa [Cedar.Thm.Duration.Components.asString] using
    parseOptionalUnit isNegative
      (Cedar.Thm.Duration.durationChunk days "d" ++
        Cedar.Thm.Duration.durationChunk hours "h" ++
        Cedar.Thm.Duration.durationChunk minutes "m" ++
        Cedar.Thm.Duration.durationChunk seconds "s")
      "ms" milliseconds (Or.inl rfl) hwfMilliseconds
      (chunks4_stop days hours minutes seconds)
      (chunks4_not_ms days hours minutes seconds hwfSeconds) hbounds

private theorem parse_seconds_step (isNegative : Bool)
    (components : Cedar.Thm.Duration.Components)
    (hwf : Duration.GrammarView.ComponentsWf components)
    (hbounds : OptionalSignedBounds isNegative components.seconds) :
    parseUnit? isNegative
        (Cedar.Thm.Duration.durationChunk components.days "d" ++
          Cedar.Thm.Duration.durationChunk components.hours "h" ++
          Cedar.Thm.Duration.durationChunk components.minutes "m" ++
          Cedar.Thm.Duration.durationChunk components.seconds "s") "s" =
      some
        (unitValue isNegative "s" components.seconds,
          Cedar.Thm.Duration.durationChunk components.days "d" ++
            Cedar.Thm.Duration.durationChunk components.hours "h" ++
            Cedar.Thm.Duration.durationChunk components.minutes "m") := by
  rcases components with ⟨days, hours, minutes, seconds, milliseconds⟩
  rcases hwf with ⟨hwfDays, hwfHours, hwfMinutes, hwfSeconds, hwfMilliseconds⟩
  exact
    parseOptionalUnit isNegative
      (Cedar.Thm.Duration.durationChunk days "d" ++
        Cedar.Thm.Duration.durationChunk hours "h" ++
        Cedar.Thm.Duration.durationChunk minutes "m")
      "s" seconds (Or.inr (Or.inl rfl)) hwfSeconds
      (chunks3_stop days hours minutes)
      (chunks3_not_s days hours minutes) hbounds

private theorem parse_minutes_step (isNegative : Bool)
    (components : Cedar.Thm.Duration.Components)
    (hwf : Duration.GrammarView.ComponentsWf components)
    (hbounds : OptionalSignedBounds isNegative components.minutes) :
    parseUnit? isNegative
        (Cedar.Thm.Duration.durationChunk components.days "d" ++
          Cedar.Thm.Duration.durationChunk components.hours "h" ++
          Cedar.Thm.Duration.durationChunk components.minutes "m") "m" =
      some
        (unitValue isNegative "m" components.minutes,
          Cedar.Thm.Duration.durationChunk components.days "d" ++
            Cedar.Thm.Duration.durationChunk components.hours "h") := by
  rcases components with ⟨days, hours, minutes, seconds, milliseconds⟩
  rcases hwf with ⟨hwfDays, hwfHours, hwfMinutes, hwfSeconds, hwfMilliseconds⟩
  exact
    parseOptionalUnit isNegative
      (Cedar.Thm.Duration.durationChunk days "d" ++
        Cedar.Thm.Duration.durationChunk hours "h")
      "m" minutes (Or.inr (Or.inr (Or.inl rfl))) hwfMinutes
      (chunks2_stop days hours) (chunks2_not_m days hours) hbounds

private theorem parse_hours_step (isNegative : Bool)
    (components : Cedar.Thm.Duration.Components)
    (hwf : Duration.GrammarView.ComponentsWf components)
    (hbounds : OptionalSignedBounds isNegative components.hours) :
    parseUnit? isNegative
        (Cedar.Thm.Duration.durationChunk components.days "d" ++
          Cedar.Thm.Duration.durationChunk components.hours "h") "h" =
      some
        (unitValue isNegative "h" components.hours,
          Cedar.Thm.Duration.durationChunk components.days "d") := by
  rcases components with ⟨days, hours, minutes, seconds, milliseconds⟩
  rcases hwf with ⟨hwfDays, hwfHours, hwfMinutes, hwfSeconds, hwfMilliseconds⟩
  exact
    parseOptionalUnit isNegative
      (Cedar.Thm.Duration.durationChunk days "d")
      "h" hours (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hwfHours
      (chunks1_stop days) (chunks1_not_h days) hbounds

private theorem parse_days_step (isNegative : Bool)
    (components : Cedar.Thm.Duration.Components)
    (hwf : Duration.GrammarView.ComponentsWf components)
    (hbounds : OptionalSignedBounds isNegative components.days) :
    parseUnit? isNegative
        (Cedar.Thm.Duration.durationChunk components.days "d") "d" =
      some (unitValue isNegative "d" components.days, "") := by
  rcases components with ⟨days, hours, minutes, seconds, milliseconds⟩
  rcases hwf with ⟨hwfDays, hwfHours, hwfMinutes, hwfSeconds, hwfMilliseconds⟩
  exact
    parseOptionalUnit isNegative "" "d" days
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hwfDays (Or.inl rfl)
      (by decide) hbounds

private theorem parseDuration_of_components (isNegative : Bool)
    (components : Cedar.Thm.Duration.Components)
    (hwf : Duration.GrammarView.ComponentsWf components)
    (hnonempty : components.nonempty)
    (hbounds :
      OptionalSignedBounds isNegative components.days ∧
        OptionalSignedBounds isNegative components.hours ∧
        OptionalSignedBounds isNegative components.minutes ∧
        OptionalSignedBounds isNegative components.seconds ∧
        OptionalSignedBounds isNegative components.milliseconds) :
    parseDuration? isNegative components.asString =
      Cedar.Spec.Ext.Datetime.duration? (componentsValue isNegative components) := by
  rcases hbounds with ⟨hDays, hHours, hMinutes, hSeconds, hMilliseconds⟩
  have hbody : components.asString.isEmpty = false := by
    rw [Bool.eq_false_iff]
    intro hempty
    exact (Duration.GrammarView.components_nonempty_iff components).mpr hnonempty
      (String.isEmpty_iff.mp hempty)
  unfold parseDuration?
  simp only [hbody, Bool.false_eq_true, if_false, bind, Option.bind, Option.pure_def]
  rw [parse_milliseconds_step isNegative components hwf hMilliseconds]
  simp only
  rw [parse_seconds_step isNegative components hwf hSeconds]
  simp only
  rw [parse_minutes_step isNegative components hwf hMinutes]
  simp only
  rw [parse_hours_step isNegative components hwf hHours]
  simp only
  rw [parse_days_step isNegative components hwf hDays]
  simp [componentsValue, Cedar.Spec.Ext.Datetime.duration?]
  rfl

private theorem component_bounds_of_total (isNegative : Bool)
    (components : Cedar.Thm.Duration.Components)
    (hbounds :
      Int64.«MIN» ≤ componentsValue isNegative components ∧
        componentsValue isNegative components ≤ Int64.«MAX») :
    OptionalSignedBounds isNegative components.days ∧
      OptionalSignedBounds isNegative components.hours ∧
      OptionalSignedBounds isNegative components.minutes ∧
      OptionalSignedBounds isNegative components.seconds ∧
      OptionalSignedBounds isNegative components.milliseconds := by
  rcases components with ⟨days, hours, minutes, seconds, milliseconds⟩
  cases isNegative <;> rcases days with _ | days <;> rcases hours with _ | hours <;>
    rcases minutes with _ | minutes <;> rcases seconds with _ | seconds <;>
    rcases milliseconds with _ | milliseconds <;>
    simp [componentsValue, OptionalSignedBounds, unitValue, signedNat,
      Triptych.natOf, Int64.«MIN», Int64.«MAX»] at hbounds ⊢ <;>
    omega

/-- A successful body parse yields ordered grammar components and their exact result value. -/
@[triptych_parser, triptych_parser_search .]
theorem parts_of_parseDuration_eq_some {isNegative : Bool} {body : String}
    {duration : Cedar.Spec.Ext.Datetime.Duration}
    (hparse : parseDuration? isNegative body = some duration) :
    ∃ components : Cedar.Thm.Duration.Components,
      body = components.asString ∧
      Duration.GrammarView.ComponentsWf components ∧
      components.nonempty ∧
      Cedar.Spec.Ext.Datetime.duration? (componentsValue isNegative components) =
        some duration := by
  unfold parseDuration? at hparse
  simp only [bind, Option.bind] at hparse
  split at hparse
  · simp at hparse
  · rename_i hbody
    simp only [Option.pure_def] at hparse
    cases hms : parseUnit? isNegative body "ms" with
    | none => simp [hms] at hparse
    | some pms =>
      obtain ⟨vms, restMs⟩ := pms
      simp only [hms] at hparse
      cases hs : parseUnit? isNegative restMs "s" with
      | none => simp [hs] at hparse
      | some ps =>
        obtain ⟨vs, restS⟩ := ps
        simp only [hs] at hparse
        cases hm : parseUnit? isNegative restS "m" with
        | none => simp [hm] at hparse
        | some pm =>
          obtain ⟨vm, restM⟩ := pm
          simp only [hm] at hparse
          cases hh : parseUnit? isNegative restM "h" with
          | none => simp [hh] at hparse
          | some ph =>
            obtain ⟨vh, restH⟩ := ph
            simp only [hh] at hparse
            cases hd : parseUnit? isNegative restH "d" with
            | none => simp [hd] at hparse
            | some pd =>
              obtain ⟨vd, restD⟩ := pd
              simp only [hd] at hparse
              split at hparse
              · rename_i hrest
                have hrestD : restD = "" := String.isEmpty_iff.mp hrest
                obtain ⟨dms, hwfMs, hbodyEq, hvMs⟩ :=
                  parseUnit_result_of_eq_some (Or.inl rfl) hms
                obtain ⟨ds, hwfS, hrestMsEq, hvS⟩ :=
                  parseUnit_result_of_eq_some (Or.inr (Or.inl rfl)) hs
                obtain ⟨dm, hwfM, hrestSEq, hvM⟩ :=
                  parseUnit_result_of_eq_some (Or.inr (Or.inr (Or.inl rfl))) hm
                obtain ⟨dh, hwfH, hrestMEq, hvH⟩ :=
                  parseUnit_result_of_eq_some
                    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hh
                obtain ⟨dd, hwfD, hrestHEq, hvD⟩ :=
                  parseUnit_result_of_eq_some
                    (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hd
                let components : Cedar.Thm.Duration.Components :=
                  ⟨dd, dh, dm, ds, dms⟩
                have hrender : body = components.asString := by
                  rw [hbodyEq, hrestMsEq, hrestSEq, hrestMEq, hrestHEq, hrestD]
                  simp [components, Cedar.Thm.Duration.Components.asString,
                    String.append_assoc]
                have hwf : Duration.GrammarView.ComponentsWf components :=
                  ⟨hwfD, hwfH, hwfM, hwfS, hwfMs⟩
                have hnonempty : components.nonempty := by
                  by_contra hempty
                  simp only [Cedar.Thm.Duration.Components.nonempty, not_or,
                    ne_eq, Decidable.not_not] at hempty
                  rcases hempty with ⟨hdd, hdh, hdm, hds, hdms⟩
                  have hcomponents : components.asString = "" := by
                    dsimp [components] at hdd hdh hdm hds hdms ⊢
                    simp [Cedar.Thm.Duration.Components.asString,
                      Cedar.Thm.Duration.durationChunk, hdd, hdh, hdm, hds, hdms]
                  exact hbody (String.isEmpty_iff.mpr (hrender.trans hcomponents))
                refine ⟨components, hrender, hwf, hnonempty, ?_⟩
                rw [← hparse]
                congr 1
                simp only [componentsValue]
                rw [← hvD, ← hvH, ← hvM, ← hvS, ← hvMs]
              · simp at hparse

private theorem string_eq_dash_append_drop_one_of_front_eq_dash (str : String)
    (hfront : str.front = '-') :
    str = "-" ++ (str.drop 1).copy := by
  apply String.ext
  simp [String.front_eq, String.front?_eq] at hfront
  cases hs : str.toList with
  | nil => simp [hs] at hfront
  | cons c cs =>
    simp [hs] at hfront
    subst c
    simp [String.toList_append, hs]

private theorem sign_split (s : String) :
    ∃ isNegative body sgn,
      isNegativeDuration s = (isNegative, body) ∧
      (sgn = "-" ∨ sgn = "") ∧
      s = sgn ++ body ∧
      Triptych.signOf sgn = if isNegative then -1 else 1 := by
  by_cases hfront : s.front = '-'
  · refine ⟨true, (s.drop 1).copy, "-", ?_, Or.inl rfl, ?_, by simp [Triptych.signOf]⟩
    · unfold isNegativeDuration
      rw [hfront]
      rfl
    · exact string_eq_dash_append_drop_one_of_front_eq_dash s hfront
  · refine ⟨false, s, "", ?_, Or.inr rfl, by simp, by simp [Triptych.signOf]⟩
    unfold isNegativeDuration
    split
    · rename_i h
      exact (hfront h).elim
    · rfl

/-- A successful Cedar Duration parse exposes grammar-shaped components and denotation. -/
@[triptych_parser, triptych_parser_search .]
theorem parts_of_parse_eq_some {s : String}
    {duration : Cedar.Spec.Ext.Datetime.Duration}
    (hparse : Cedar.Spec.Ext.Datetime.Duration.parse s = some duration) :
    ∃ sgn components,
      (sgn = "-" ∨ sgn = "") ∧
      s = sgn ++ components.asString ∧
      Duration.GrammarView.ComponentsWf components ∧
      components.nonempty ∧
      Cedar.Spec.Ext.Datetime.duration?
          (Duration.GrammarView.formatValue sgn components) =
        some duration := by
  obtain ⟨isNegative, body, sgn, hsplit, hsign, hs, hsignValue⟩ := sign_split s
  rw [CedarSupport.DurationParserInternals.duration_parse_eq_parse] at hparse
  unfold CedarSupport.DurationParserInternals.parse at hparse
  rw [hsplit] at hparse
  obtain ⟨components, hbody, hwf, hnonempty, hvalue⟩ :=
    parts_of_parseDuration_eq_some hparse
  refine ⟨sgn, components, hsign, hs.trans (congrArg (sgn ++ ·) hbody), hwf,
    hnonempty, ?_⟩
  rw [← hvalue]
  congr 1
  unfold Duration.GrammarView.formatValue componentsValue
    Duration.GrammarView.formatQuantity unitValue signedNat
  rcases components with ⟨days, hours, minutes, seconds, milliseconds⟩
  rcases days with _ | days <;> rcases hours with _ | hours <;>
    rcases minutes with _ | minutes <;> rcases seconds with _ | seconds <;>
    rcases milliseconds with _ | milliseconds <;>
    cases isNegative <;>
    simp [hsignValue, Int.neg_add, Int.neg_mul]

private theorem digits_front_ne_dash (digits : String)
    (hdigits : Triptych.IsDigits digits) :
    digits.front ≠ '-' := by
  have hcedarDigits := (CedarSupport.String.digits_iff digits).mp hdigits
  intro hfront
  simp [String.front_eq, String.front?_eq] at hfront
  cases hlist : digits.toList with
  | nil => simp [hlist] at hfront
  | cons c cs =>
      simp [hlist] at hfront
      subst c
      have hdigit := hcedarDigits.2 '-' (by simp [hlist])
      simp at hdigit

private theorem digits_ne_empty (digits : String)
    (hdigits : Triptych.IsDigits digits) :
    digits ≠ "" := by
  intro h
  subst digits
  simp [Triptych.IsDigits] at hdigits

private theorem front_append_of_ne_empty (s t : String) (h : s ≠ "") :
    (s ++ t).front = s.front := by
  simp [String.front_eq, String.front?_eq, String.toList_append]
  cases hs : s.toList with
  | nil =>
      exfalso
      apply h
      apply String.toList_inj.mp
      simpa using hs
  | cons _ _ => simp

private theorem components_front_ne_dash
    (components : Cedar.Thm.Duration.Components)
    (hwf : Duration.GrammarView.ComponentsWf components) :
    components.asString.front ≠ '-' := by
  rcases components with ⟨days, hours, minutes, seconds, milliseconds⟩
  rcases hwf with ⟨hwfDays, hwfHours, hwfMinutes, hwfSeconds, hwfMilliseconds⟩
  change Duration.GrammarView.OptionalDigitsWf days at hwfDays
  change Duration.GrammarView.OptionalDigitsWf hours at hwfHours
  change Duration.GrammarView.OptionalDigitsWf minutes at hwfMinutes
  change Duration.GrammarView.OptionalDigitsWf seconds at hwfSeconds
  change Duration.GrammarView.OptionalDigitsWf milliseconds at hwfMilliseconds
  simp only [Cedar.Thm.Duration.Components.asString] at *
  rcases days with _ | days
  · rcases hours with _ | hours
    · rcases minutes with _ | minutes
      · rcases seconds with _ | seconds
        · rcases milliseconds with _ | milliseconds
          · simp [Cedar.Thm.Duration.durationChunk, String.front_eq,
              String.front?_eq]
          · simp only [Cedar.Thm.Duration.durationChunk, String.empty_append]
            rw [front_append_of_ne_empty milliseconds _
              (digits_ne_empty milliseconds hwfMilliseconds)]
            exact digits_front_ne_dash milliseconds hwfMilliseconds
        · simp only [Cedar.Thm.Duration.durationChunk, String.empty_append,
            String.append_assoc]
          rw [front_append_of_ne_empty seconds _
            (digits_ne_empty seconds hwfSeconds)]
          exact digits_front_ne_dash seconds hwfSeconds
      · simp only [Cedar.Thm.Duration.durationChunk, String.empty_append,
          String.append_assoc]
        rw [front_append_of_ne_empty minutes _
          (digits_ne_empty minutes hwfMinutes)]
        exact digits_front_ne_dash minutes hwfMinutes
    · simp only [Cedar.Thm.Duration.durationChunk, String.empty_append,
        String.append_assoc]
      rw [front_append_of_ne_empty hours _
        (digits_ne_empty hours hwfHours)]
      exact digits_front_ne_dash hours hwfHours
  · simp only [Cedar.Thm.Duration.durationChunk, String.append_assoc]
    rw [front_append_of_ne_empty days _ (digits_ne_empty days hwfDays)]
    exact digits_front_ne_dash days hwfDays

private theorem componentsValue_eq_formatValue_false
    (components : Cedar.Thm.Duration.Components) :
    componentsValue false components =
      Duration.GrammarView.formatValue "" components := by
  rcases components with ⟨days, hours, minutes, seconds, milliseconds⟩
  rcases days with _ | days <;> rcases hours with _ | hours <;>
    rcases minutes with _ | minutes <;> rcases seconds with _ | seconds <;>
    rcases milliseconds with _ | milliseconds <;>
    simp [componentsValue, unitValue, signedNat, Duration.GrammarView.formatValue,
      Duration.GrammarView.formatQuantity, Triptych.signOf]

private theorem componentsValue_eq_formatValue_true
    (components : Cedar.Thm.Duration.Components) :
    componentsValue true components =
      Duration.GrammarView.formatValue "-" components := by
  rcases components with ⟨days, hours, minutes, seconds, milliseconds⟩
  rcases days with _ | days <;> rcases hours with _ | hours <;>
    rcases minutes with _ | minutes <;> rcases seconds with _ | seconds <;>
    rcases milliseconds with _ | milliseconds <;>
    simp [componentsValue, unitValue, signedNat, Duration.GrammarView.formatValue,
      Duration.GrammarView.formatQuantity, Triptych.signOf, Int.neg_add, Int.neg_mul]

/-- The ordered Duration surface representation has a unique sign and component tuple. -/
theorem rendered_parts_unique {s leftSign rightSign : String}
    {left right : Cedar.Thm.Duration.Components}
    (hleftSign : leftSign = "-" ∨ leftSign = "")
    (hrightSign : rightSign = "-" ∨ rightSign = "")
    (hleft : s = leftSign ++ left.asString)
    (hright : s = rightSign ++ right.asString)
    (hwfLeft : Duration.GrammarView.ComponentsWf left)
    (hwfRight : Duration.GrammarView.ComponentsWf right) :
    leftSign = rightSign ∧ left = right := by
  have hrender :
      leftSign ++ left.asString = rightSign ++ right.asString :=
    hleft.symm.trans hright
  rcases hleftSign with rfl | rfl <;> rcases hrightSign with rfl | rfl
  · have hbody : left.asString = right.asString :=
      (String.append_right_inj "-").mp hrender
    exact ⟨rfl, components_asString_injective left right hwfLeft hwfRight hbody⟩
  · exfalso
    simp only [String.empty_append] at hrender
    have hfront :
        right.asString.front = '-' := by
      rw [← hrender]
      simp [String.front_eq, String.front?_eq, String.toList_append]
    exact components_front_ne_dash right hwfRight hfront
  · exfalso
    simp only [String.empty_append] at hrender
    have hfront :
        left.asString.front = '-' := by
      rw [hrender]
      simp [String.front_eq, String.front?_eq, String.toList_append]
    exact components_front_ne_dash left hwfLeft hfront
  · simp only [String.empty_append] at hrender
    exact ⟨rfl, components_asString_injective left right hwfLeft hwfRight hrender⟩

/--
Ordered, well-formed Triptych components make Cedar's executable parser return exactly the
Triptych denotation. This is the completeness-direction counterpart to `parts_of_parse_eq_some`.
-/
@[triptych_parser]
theorem parse_of_parts (s sgn : String)
    (components : Cedar.Thm.Duration.Components)
    (hsign : sgn = "-" ∨ sgn = "")
    (hs : s = sgn ++ components.asString)
    (hwf : Duration.GrammarView.ComponentsWf components)
    (hnonempty : components.nonempty)
    (hbounds :
      (-9223372036854775808 : Int) ≤ Duration.GrammarView.formatValue sgn components ∧
        Duration.GrammarView.formatValue sgn components ≤ (9223372036854775807 : Int)) :
    Cedar.Spec.Ext.Datetime.Duration.parse s =
      Cedar.Spec.Ext.Datetime.duration?
        (Duration.GrammarView.formatValue sgn components) := by
  subst s
  rw [CedarSupport.DurationParserInternals.duration_parse_eq_parse]
  unfold CedarSupport.DurationParserInternals.parse
  rcases hsign with rfl | rfl
  · have hsplit :
        isNegativeDuration ("-" ++ components.asString) =
          (true, components.asString) := by
      unfold isNegativeDuration
      have hfront : ("-" ++ components.asString).front = '-' := by
        simp [String.front_eq, String.front?_eq, String.toList_append]
      rw [hfront]
      simp only
      congr 1
      apply String.ext
      simp
    rw [hsplit]
    simp only
    have htotal :
        Int64.«MIN» ≤ componentsValue true components ∧
          componentsValue true components ≤ Int64.«MAX» := by
      rw [componentsValue_eq_formatValue_true]
      simpa only [Int64.«MIN», Int64.«MAX»] using hbounds
    rw [parseDuration_of_components true components hwf hnonempty
      (component_bounds_of_total true components htotal)]
    rw [componentsValue_eq_formatValue_true]
  · simp only [String.empty_append]
    have hsplit :
        isNegativeDuration components.asString = (false, components.asString) := by
      unfold isNegativeDuration
      split
      · rename_i hfront
        exact (components_front_ne_dash components hwf hfront).elim
      · rfl
    rw [hsplit]
    simp only
    have htotal :
        Int64.«MIN» ≤ componentsValue false components ∧
          componentsValue false components ≤ Int64.«MAX» := by
      rw [componentsValue_eq_formatValue_false]
      simpa only [Int64.«MIN», Int64.«MAX»] using hbounds
    rw [parseDuration_of_components false components hwf hnonempty
      (component_bounds_of_total false components htotal)]
    rw [componentsValue_eq_formatValue_false]

end Duration.RuleRegistryProof
