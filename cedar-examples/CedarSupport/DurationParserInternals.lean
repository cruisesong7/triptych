import Cedar.Spec.Ext.Datetime

/-!
# Cedar Duration parser compatibility boundary

Cedar keeps the helper stages of `Duration.parse` private. This module republishes the same
executable definitions and proves the public parser is definitionally equal to the exposed copy.
-/

open Cedar.Spec.Ext
open Cedar.Spec.Ext.Datetime

namespace CedarSupport.DurationParserInternals

def durationUnits? (n : Int) (suffix : String) : Option Int :=
  match Int64.ofInt? n with
  | none => none
  | some i =>
    match suffix with
    | "ms" => some i
    | "s" => some (i * MILLISECONDS_PER_SECOND)
    | "m" => some (i * MILLISECONDS_PER_MINUTE)
    | "h" => some (i * MILLISECONDS_PER_HOUR)
    | "d" => some (i * MILLISECONDS_PER_DAY)
    | _ => none

def isNegativeDuration (str : String) : Bool × String :=
  match str.front with
  | '-' => (true, (str.drop 1).copy)
  | _ => (false, str)

def parseUnit? (isNegative : Bool) (str suffix : String) : Option (Int × String) :=
  if str.endsWith suffix then
    let newStr := str.dropEnd suffix.length
    let newStrList := newStr.copy.toList
    let digits := (newStrList.reverse.takeWhile Char.isDigit).reverse
    if digits.isEmpty then
      none
    else do
      let nUnsignedUnits ← toNat?' (String.ofList digits)
      let units ←
        if isNegative then
          durationUnits? (Int.negOfNat nUnsignedUnits) suffix
        else
          durationUnits? (Int.ofNat nUnsignedUnits) suffix
      some (units, (newStr.dropEnd digits.length).copy)
  else
    some (0, str)

def parseUnitNorm? (isNegative : Bool) (str suffix : String) : Option (Int × String) :=
  if str.endsWith suffix then
    let rest := (str.dropEnd suffix.length).toString
    let digits := (rest.toList.reverse.takeWhile Char.isDigit).reverse
    if digits.isEmpty then
      none
    else do
      let nUnsignedUnits ← toNat?' (String.ofList digits)
      let units ←
        if isNegative then
          durationUnits? (Int.negOfNat nUnsignedUnits) suffix
        else
          durationUnits? (Int.ofNat nUnsignedUnits) suffix
      some (units, (rest.dropEnd digits.length).toString)
  else
    some (0, str)

theorem parseUnit_eq_norm (isNegative : Bool) (str suffix : String) :
    parseUnit? isNegative str suffix = parseUnitNorm? isNegative str suffix := by
  unfold parseUnit? parseUnitNorm?
  split
  · have h₁ :
        (str.dropEnd suffix.length).copy.toList =
          (str.dropEnd suffix.length).toString.toList := by
      congr 1
    have h₂ :
        ∀ n : Nat,
          ((str.dropEnd suffix.length).dropEnd n).copy =
            ((str.dropEnd suffix.length).toString.dropEnd n).toString := by
      intro n
      apply String.ext
      simp
    simp only [h₁, h₂]
  · rfl

private theorem takeWhile_append_stop {l₁ l₂ : List α} {p : α → Bool}
    (h₁ : ∀ x ∈ l₁, p x = true)
    (h₂ : l₂ = [] ∨ ∃ y l₂', l₂ = y :: l₂' ∧ p y = false) :
    List.takeWhile p (l₁ ++ l₂) = l₁ := by
  have htake : List.takeWhile p l₁ = l₁ := by
    induction l₁ with
    | nil => simp
    | cons x xs ih =>
      simp [List.takeWhile, h₁ x (by simp)]
      exact ih (fun y hy => h₁ y (by simp [hy]))
  rw [List.takeWhile_append]
  simp only [htake]
  rcases h₂ with rfl | ⟨y, l₂, rfl, hy⟩
  · simp
  · simp [List.takeWhile, hy]

/--
If `digits` is a nonempty decimal run and the preceding prefix stops at a non-digit,
`parseUnit?` peels exactly `digits ++ suffix`.
-/
theorem parseUnit_present (isNegative : Bool) (pfx digits suffix : String)
    (n : Nat) (units : Int)
    (hdigitsNonempty : digits.toList ≠ [])
    (hdigits : ∀ c ∈ digits.toList, c.isDigit = true)
    (hnat : toNat?' digits = some n)
    (hpfxStop :
      pfx = "" ∨
        ∃ c cs, pfx.toList.reverse = c :: cs ∧ c.isDigit = false)
    (hunits :
      durationUnits?
          (if isNegative then Int.negOfNat n else Int.ofNat n) suffix =
        some units) :
    parseUnit? isNegative (pfx ++ digits ++ suffix) suffix = some (units, pfx) := by
  rw [parseUnit_eq_norm]
  unfold parseUnitNorm?
  have hends : (pfx ++ digits ++ suffix).endsWith suffix = true := by
    simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice,
      String.toList_append]
    exact ⟨pfx.toList ++ digits.toList, by simp [List.append_assoc]⟩
  simp only [hends, if_true]
  have hdrop :
      ((pfx ++ digits ++ suffix).dropEnd suffix.length).toString.toList =
        pfx.toList ++ digits.toList := by
    simp [String.toList_append, ← String.length_toList]
    have hlength :
        pfx.toList.length + (digits.toList.length + suffix.toList.length) -
            suffix.toList.length =
          (pfx.toList ++ digits.toList).length := by
      simp
      omega
    rw [hlength, show
      pfx.toList ++ (digits.toList ++ suffix.toList) =
        (pfx.toList ++ digits.toList) ++ suffix.toList by
          rw [List.append_assoc]]
    exact List.take_left
  have hallDigits :
      ∀ c ∈ digits.toList.reverse, Char.isDigit c = true := by
    intro c hc
    exact hdigits c (List.mem_reverse.mp hc)
  have hpfxStopList :
      pfx.toList.reverse = [] ∨
        ∃ c cs, pfx.toList.reverse = c :: cs ∧ c.isDigit = false := by
    rcases hpfxStop with rfl | hstop
    · simp
    · exact Or.inr hstop
  have htake :
      (((pfx ++ digits ++ suffix).dropEnd suffix.length).toString.toList.reverse.takeWhile
          Char.isDigit).reverse =
        digits.toList := by
    rw [hdrop, List.reverse_append,
      takeWhile_append_stop hallDigits hpfxStopList, List.reverse_reverse]
  rw [htake]
  simp only [List.isEmpty_iff, hdigitsNonempty, String.ofList_toList, if_false, hnat,
    bind, Option.bind]
  cases isNegative <;> simp only [Bool.false_eq_true, if_false, if_true] at hunits ⊢
  all_goals
    rw [hunits]
    simp only [Option.some.injEq, Prod.mk.injEq, true_and]
    apply String.ext
    simp [String.toList_append, ← String.length_toList]
    have hdropDigits :
        pfx.toList.length + (digits.toList.length + suffix.toList.length) -
              suffix.toList.length -
            digits.toList.length =
          pfx.toList.length := by
      omega
    have hdropSuffix :
        pfx.toList.length + (digits.toList.length + suffix.toList.length) -
            suffix.toList.length =
          (pfx.toList ++ digits.toList).length := by
      simp
      omega
    rw [hdropDigits, hdropSuffix, show
      pfx.toList ++ (digits.toList ++ suffix.toList) =
        (pfx.toList ++ digits.toList) ++ suffix.toList by
          rw [List.append_assoc]]
    rw [List.take_left, List.take_left]

/-- If the suffix is absent, `parseUnit?` leaves the input untouched with zero value. -/
theorem parseUnit_absent (isNegative : Bool) (str suffix : String)
    (hends : str.endsWith suffix = false) :
    parseUnit? isNegative str suffix = some (0, str) := by
  unfold parseUnit?
  simp [hends]

def digitString (str suffix : String) : Option String :=
  if str.endsWith suffix then
    let rest := (str.dropEnd suffix.length).toString
    let digits := (rest.toList.reverse.takeWhile Char.isDigit).reverse
    if digits.isEmpty then none else some (String.ofList digits)
  else
    none

/-- Trailing-digit extraction recovers an explicitly rendered component. -/
theorem digitString_present (pfx digits suffix : String)
    (hdigitsNonempty : digits.toList ≠ [])
    (hdigits : ∀ c ∈ digits.toList, c.isDigit = true)
    (hpfxStop :
      pfx = "" ∨
        ∃ c cs, pfx.toList.reverse = c :: cs ∧ c.isDigit = false) :
    digitString (pfx ++ digits ++ suffix) suffix = some digits := by
  unfold digitString
  have hends : (pfx ++ digits ++ suffix).endsWith suffix = true := by
    simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice,
      String.toList_append]
    exact ⟨pfx.toList ++ digits.toList, by simp [List.append_assoc]⟩
  simp only [hends, if_true]
  have hdrop :
      ((pfx ++ digits ++ suffix).dropEnd suffix.length).toString.toList =
        pfx.toList ++ digits.toList := by
    simp [String.toList_append, ← String.length_toList]
    have hlength :
        pfx.toList.length + (digits.toList.length + suffix.toList.length) -
            suffix.toList.length =
          (pfx.toList ++ digits.toList).length := by
      simp
      omega
    rw [hlength, show
      pfx.toList ++ (digits.toList ++ suffix.toList) =
        (pfx.toList ++ digits.toList) ++ suffix.toList by
          rw [List.append_assoc]]
    exact List.take_left
  have hallDigits :
      ∀ c ∈ digits.toList.reverse, Char.isDigit c = true := by
    intro c hc
    exact hdigits c (List.mem_reverse.mp hc)
  have hpfxStopList :
      pfx.toList.reverse = [] ∨
        ∃ c cs, pfx.toList.reverse = c :: cs ∧ c.isDigit = false := by
    rcases hpfxStop with rfl | hstop
    · simp
    · exact Or.inr hstop
  have htake :
      (((pfx ++ digits ++ suffix).dropEnd suffix.length).toString.toList.reverse.takeWhile
          Char.isDigit).reverse =
        digits.toList := by
    rw [hdrop, List.reverse_append,
      takeWhile_append_stop hallDigits hpfxStopList, List.reverse_reverse]
  rw [htake]
  simp [hdigitsNonempty]

/-- If a suffix is absent, trailing-digit extraction returns no component. -/
theorem digitString_absent (str suffix : String)
    (hends : str.endsWith suffix = false) :
    digitString str suffix = none := by
  unfold digitString
  simp [hends]

def parseDuration? (isNegative : Bool) (str : String) : Option Duration := do
  if str.isEmpty then failure
  let (milliseconds, restStr) ← parseUnit? isNegative str "ms"
  let (seconds, restStr) ← parseUnit? isNegative restStr "s"
  let (minutes, restStr) ← parseUnit? isNegative restStr "m"
  let (hours, restStr) ← parseUnit? isNegative restStr "h"
  let (days, restStr) ← parseUnit? isNegative restStr "d"
  if restStr.isEmpty then
    Int64.ofInt? (days + hours + minutes + seconds + milliseconds)
  else
    none

def parse (str : String) : Option Duration :=
  let (isNegative, restStr) := isNegativeDuration str
  parseDuration? isNegative restStr

theorem duration_parse_eq_parse (str : String) :
    Cedar.Spec.Ext.Datetime.Duration.parse str = parse str := by
  rfl

private theorem listTakeWhileDecompose (l : List α) (p : α → Bool) :
    l = (l.reverse.dropWhile p).reverse ++ (l.reverse.takeWhile p).reverse := by
  suffices h :
      (l.reverse.dropWhile p).reverse ++ (l.reverse.takeWhile p).reverse = l by
    exact h.symm
  rw [← List.reverse_append, List.takeWhile_append_dropWhile, List.reverse_reverse]

theorem reconstructTrailingDigits (s suffix : String) (digits : List Char)
    (hends : s.endsWith suffix = true)
    (hdigits :
      ((s.dropEnd suffix.length).toString.toList.reverse.takeWhile
        Char.isDigit).reverse = digits) :
    s =
      ((s.dropEnd suffix.length).toString.dropEnd digits.length).toString ++
        String.ofList digits ++ suffix := by
  apply String.ext
  have hsuffix : suffix.toList <:+ s.toList := by
    simpa [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice] using hends
  obtain ⟨pfx, hpfx⟩ := hsuffix
  have htakeSuffix :
      List.take (s.toList.length - suffix.toList.length) s.toList = pfx := by
    rw [← hpfx]
    simp
  have hdropSuffix : (s.dropEnd suffix.length).toString.toList = pfx := by
    simpa [← String.length_toList] using htakeSuffix
  have hdigitsPfx : (pfx.reverse.takeWhile Char.isDigit).reverse = digits := by
    rw [hdropSuffix] at hdigits
    exact hdigits
  let restChars := (pfx.reverse.dropWhile Char.isDigit).reverse
  have hpfxDecompose : pfx = restChars ++ digits := by
    simpa [restChars, hdigitsPfx] using listTakeWhileDecompose pfx Char.isDigit
  have hpfxLength : s.toList.length - suffix.toList.length = pfx.length := by
    have h := congrArg List.length hpfx
    simp only [List.length_append] at h
    omega
  have hrestLength : pfx.length - digits.length = restChars.length := by
    rw [hpfxDecompose]
    simp
  have hrest :
      ((s.dropEnd suffix.length).toString.dropEnd digits.length).toString.toList =
        restChars := by
    simp [← String.length_toList]
    rw [htakeSuffix, hpfxLength, hrestLength, hpfxDecompose]
    exact List.take_left
  simp only [String.toList_append, String.toList_ofList]
  calc
    s.toList = pfx ++ suffix.toList := hpfx.symm
    _ = (restChars ++ digits) ++ suffix.toList := by rw [hpfxDecompose]
    _ = restChars ++ digits ++ suffix.toList := by rw [List.append_assoc]
    _ =
        ((s.dropEnd suffix.length).toString.dropEnd digits.length).toString.toList ++
          digits ++ suffix.toList := by rw [hrest]

theorem parseUnitReconstruct (isNegative : Bool) (s suffix : String)
    (v : Int) (rest : String)
    (hparse : parseUnit? isNegative s suffix = some (v, rest)) :
    s = rest ++
      (match digitString s suffix with
      | none => ""
      | some digits => digits ++ suffix) := by
  unfold digitString
  by_cases hends : s.endsWith suffix = true
  · simp only [hends, if_true]
    have hparse' := hparse
    rw [parseUnit_eq_norm] at hparse'
    unfold parseUnitNorm? at hparse'
    simp only [hends, if_true] at hparse'
    generalize hdigits :
        ((s.dropEnd suffix.length).toString.toList.reverse.takeWhile
          Char.isDigit).reverse = digits at hparse'
    cases hempty : digits.isEmpty
    · simp only [hempty, Bool.false_eq_true, if_false, bind, Option.bind] at hparse'
      cases hnat : toNat?' (String.ofList digits) with
      | none => simp [hnat] at hparse'
      | some n =>
        rw [hnat] at hparse'
        simp only [show (false = true) = False by simp, if_false]
        have hrest :
            rest =
              ((s.dropEnd suffix.length).toString.dropEnd digits.length).toString := by
          cases isNegative with
          | false =>
            simp only [Bool.false_eq_true, if_false] at hparse'
            cases hunit : durationUnits? (Int.ofNat n) suffix with
            | none =>
              rw [hunit] at hparse'
              simp at hparse'
            | some u =>
              rw [hunit] at hparse'
              simp only [Option.some.injEq, Prod.mk.injEq] at hparse'
              exact hparse'.2.symm
          | true =>
            simp only [if_true] at hparse'
            cases hunit : durationUnits? (Int.negOfNat n) suffix with
            | none =>
              rw [hunit] at hparse'
              simp at hparse'
            | some u =>
              rw [hunit] at hparse'
              simp only [Option.some.injEq, Prod.mk.injEq] at hparse'
              exact hparse'.2.symm
        rw [hrest]
        simpa [String.append_assoc] using
          reconstructTrailingDigits s suffix digits hends hdigits
    · simp [hempty] at hparse'
  · have hendsFalse : s.endsWith suffix = false := by
      cases h : s.endsWith suffix <;> simp_all
    rw [parseUnit_eq_norm] at hparse
    unfold parseUnitNorm? at hparse
    simp only [hendsFalse, Bool.false_eq_true, if_false, Option.some.injEq,
      Prod.mk.injEq] at hparse
    have hrestEnds : rest.endsWith suffix = false := by
      rw [← hparse.2]
      exact hendsFalse
    rw [hparse.2]
    simp [hrestEnds]

end CedarSupport.DurationParserInternals
