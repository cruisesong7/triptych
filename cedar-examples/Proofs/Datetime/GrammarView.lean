import Outputs.Datetime.parser
import CedarSupport.Datetime
import CedarSupport.String

/-! Relates the generated Datetime view to parser-independent grammar components. -/

open Triptych
open CedarSupport.String
open CedarExamples.Datetime

namespace Datetime.GrammarView

def cedarDate (v : Datetime.View) : Cedar.Thm.Datetime.DateComponents :=
  { year := v.yyyy, month := v.mm, day := v.dd }

def cedarTime (hours minutes seconds : String) : Cedar.Thm.Datetime.TimeComponents :=
  { hours := hours, minutes := minutes, seconds := seconds }

def cedarOffset (offset hours minutes : String) :
    Cedar.Thm.Datetime.OffsetComponents :=
  { negative := offset.startsWith "-", hours := hours, minutes := minutes }

/-- Convert a generated view to Cedar's nested component representation. `none` identifies
    impossible mixtures of absent and present fields; decoded views never have those shapes. -/
def _root_.Datetime.View.toCedarComponents? (v : Datetime.View) :
    Option Cedar.Thm.Datetime.DatetimeComponents :=
  match v.time_hh, v.time_mm, v.ss, v.sss, v.offset_hh, v.offset_mm, v.offset with
  | none, none, none, none, none, none, none =>
      some { date := cedarDate v, time := none }
  | some hours, some minutes, some seconds, millis, none, none, none =>
      some {
        date := cedarDate v
        time := some {
          time := cedarTime hours minutes seconds
          millis
          zone := .utc
        }
      }
  | some hours, some minutes, some seconds, millis, some offsetHours,
      some offsetMinutes, some offset =>
      some {
        date := cedarDate v
        time := some {
          time := cedarTime hours minutes seconds
          millis
          zone := .offset (cedarOffset offset offsetHours offsetMinutes)
        }
      }
  | _, _, _, _, _, _, _ => none

theorem fixedDigits_iff (n : Nat) (hn : 0 < n) (s : String) :
    Triptych.IsFixedDigits n s ↔ String.IsFixedDigits n s := by
  unfold Triptych.IsFixedDigits String.IsFixedDigits
  constructor
  · rintro ⟨hdigits, hlen⟩
    exact ⟨(digits_iff s).mp ⟨hdigits, by omega⟩, hlen⟩
  · rintro ⟨hdigits, hlen⟩
    exact ⟨((digits_iff s).mpr hdigits).1, hlen⟩

theorem stringNatOf_eq_natOf {s : String} (h : String.IsDigits s) :
    (String.natOf s : Int) = Triptych.natOf s := by
  unfold String.natOf Triptych.natOf
  rw [readNat_eq s h]
  rfl

theorem stringNatOf_eq_natOf_of_fixed {n : Nat} {s : String}
    (h : String.IsFixedDigits n s) :
    (String.natOf s : Int) = Triptych.natOf s :=
  stringNatOf_eq_natOf h.1

theorem stringNatOf_eq_readNat {s : String} (h : String.IsDigits s) :
    String.natOf s = Triptych.readNat s := by
  unfold String.natOf
  rw [readNat_eq s h]
  rfl

def dslEpochDays (year month day : Nat) : Int :=
  let m : Int := month
  let d : Int := day
  let y : Int := if 2 < m then year else (year : Int) - 1
  let era : Int := if 0 ≤ y then y.tdiv 400 else (y - 399).tdiv 400
  let yoe : Int := y - era * 400
  let doy : Int := (153 * (m + if 2 < m then -3 else 9) + 2).tdiv 5 + (d - 1)
  let doe : Int := yoe * 365 + yoe.tdiv 4 - yoe.tdiv 100 + doy
  era * 146097 + doe - 719468

theorem dslEpochDays_eq_epochDays (year month day : Nat) :
    dslEpochDays year month day = Cedar.Thm.Datetime.epochDays year month day := by
  unfold dslEpochDays Cedar.Thm.Datetime.epochDays
  by_cases hmonth : (2 : Int) < month
  · simp [hmonth]
    omega
  · by_cases hyear : (1 : Int) ≤ year <;> simp [hmonth, hyear] <;> omega

theorem value_eq_epochMillis
    (mm yyyy dd timeHh timeMm seconds millis offset offsetHh offsetMm : String) :
    Datetime.value mm yyyy dd timeHh timeMm seconds millis offset offsetHh offsetMm =
      ((Cedar.Thm.Datetime.epochDays (readNat yyyy) (readNat mm) (readNat dd) * 86400 +
            (readNat timeHh : Int) * 3600 + (readNat timeMm : Int) * 60 +
            readNat seconds) *
          1000 +
        readNat millis) -
        signOf offset * ((readNat offsetHh : Int) * 3600000 + (readNat offsetMm : Int) * 60000) := by
  change
    ((dslEpochDays (readNat yyyy) (readNat mm) (readNat dd) * 86400 +
              (readNat timeHh : Int) * 3600 + (readNat timeMm : Int) * 60 +
              readNat seconds) *
            1000 +
          readNat millis) -
        signOf offset * ((readNat offsetHh : Int) * 3600000 + (readNat offsetMm : Int) * 60000) =
      _
  rw [dslEpochDays_eq_epochDays]

def dslLeapYearFlag (year : Nat) : Int :=
  if (year : Int).tmod 4 = 0 then
    if (year : Int).tmod 100 = 0 then
      if (year : Int).tmod 400 = 0 then 1 else 0
    else 1
  else 0

theorem dslLeapYearFlag_eq (year : Nat) :
    dslLeapYearFlag year = if Cedar.Thm.Datetime.isLeapYear year then 1 else 0 := by
  unfold dslLeapYearFlag Cedar.Thm.Datetime.isLeapYear
  have h4cast : (year : Int).tmod 4 = ((year % 4 : Nat) : Int) := by
    rw [Int.ofNat_tmod]
    rfl
  have h100cast : (year : Int).tmod 100 = ((year % 100 : Nat) : Int) := by
    rw [Int.ofNat_tmod]
    rfl
  have h400cast : (year : Int).tmod 400 = ((year % 400 : Nat) : Int) := by
    rw [Int.ofNat_tmod]
    rfl
  rw [h4cast, h100cast, h400cast]
  by_cases h4 : year % 4 = 0 <;>
    by_cases h100 : year % 100 = 0 <;>
      by_cases h400 : year % 400 = 0 <;>
        simp [h4, h100, h400] <;> omega

def dslDaysInMonth (year month : Nat) : Int :=
  if (month : Int) = 4 then 30
  else if (month : Int) = 6 then 30
  else if (month : Int) = 9 then 30
  else if (month : Int) = 11 then 30
  else if (month : Int) = 2 then
    if dslLeapYearFlag year = 1 then 29 else 28
  else 31

theorem dslDaysInMonth_eq_daysInMonth (year month : Nat) :
    dslDaysInMonth year month = Cedar.Thm.Datetime.daysInMonth year month := by
  unfold dslDaysInMonth Cedar.Thm.Datetime.daysInMonth
  rw [dslLeapYearFlag_eq]
  have h4cast : (month : Int) = 4 ↔ month = 4 := by omega
  have h6cast : (month : Int) = 6 ↔ month = 6 := by omega
  have h9cast : (month : Int) = 9 ↔ month = 9 := by omega
  have h11cast : (month : Int) = 11 ↔ month = 11 := by omega
  have h2cast : (month : Int) = 2 ↔ month = 2 := by omega
  simp only [h4cast, h6cast, h9cast, h11cast, h2cast]
  by_cases h4 : month = 4 <;>
    by_cases h6 : month = 6 <;>
      by_cases h9 : month = 9 <;>
        by_cases h11 : month = 11 <;>
          by_cases h2 : month = 2 <;>
            by_cases hleap : Cedar.Thm.Datetime.isLeapYear year = true <;>
              simp [h4, h6, h9, h11, h2, hleap]

theorem expandedDaysInMonth_eq (year month : Nat) :
    (if (month : Int) = 4 then (30 : Int)
      else if (month : Int) = 6 then 30
      else if (month : Int) = 9 then 30
      else if (month : Int) = 11 then 30
      else if (month : Int) = 2 then
        if
            (if (year : Int).tmod 4 = 0 then
              if (year : Int).tmod 100 = 0 then
                if (year : Int).tmod 400 = 0 then (1 : Int) else 0
              else 1
            else 0) =
            1 then
          29
        else 28
      else 31) =
      Cedar.Thm.Datetime.daysInMonth year month := by
  change dslDaysInMonth year month = Cedar.Thm.Datetime.daysInMonth year month
  exact dslDaysInMonth_eq_daysInMonth year month

def CedarNatValuesAgree (c : Cedar.Thm.Datetime.DatetimeComponents) : Prop :=
  String.natOf c.date.year = readNat c.date.year ∧
  String.natOf c.date.month = readNat c.date.month ∧
  String.natOf c.date.day = readNat c.date.day ∧
  match c.time with
  | none => True
  | some tp =>
      String.natOf tp.time.hours = readNat tp.time.hours ∧
      String.natOf tp.time.minutes = readNat tp.time.minutes ∧
      String.natOf tp.time.seconds = readNat tp.time.seconds ∧
      (match tp.millis with
        | none => True
        | some millis =>
            String.natOf millis = readNat millis) ∧
      match tp.zone with
      | .utc => True
      | .offset offset =>
          String.natOf offset.hours = readNat offset.hours ∧
          String.natOf offset.minutes = readNat offset.minutes

theorem cedarNatValuesAgree {c : Cedar.Thm.Datetime.DatetimeComponents}
    (h : c.syntaxWf) : CedarNatValuesAgree c := by
  rcases c with ⟨⟨year, month, day⟩, time⟩
  cases time with
  | none =>
      rcases h with ⟨⟨hy, hm, hd⟩, _⟩
      exact ⟨stringNatOf_eq_readNat hy.1, stringNatOf_eq_readNat hm.1,
        stringNatOf_eq_readNat hd.1, trivial⟩
  | some tp =>
      rcases tp with ⟨⟨hours, minutes, seconds⟩, millis, zone⟩
      rcases h with ⟨⟨hy, hm, hd⟩, ⟨⟨hh, hmin, hs⟩, hmillis, hzone⟩⟩
      have hbase :
          String.natOf year = readNat year ∧
          String.natOf month = readNat month ∧
          String.natOf day = readNat day ∧
          String.natOf hours = readNat hours ∧
          String.natOf minutes = readNat minutes ∧
          String.natOf seconds = readNat seconds :=
        ⟨stringNatOf_eq_readNat hy.1, stringNatOf_eq_readNat hm.1,
          stringNatOf_eq_readNat hd.1, stringNatOf_eq_readNat hh.1,
          stringNatOf_eq_readNat hmin.1, stringNatOf_eq_readNat hs.1⟩
      cases millis with
      | none =>
          cases zone with
          | utc => exact ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2.1,
              hbase.2.2.2.2.1, hbase.2.2.2.2.2, trivial, trivial⟩
          | offset offset =>
              exact ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2.1,
                hbase.2.2.2.2.1, hbase.2.2.2.2.2, trivial,
                stringNatOf_eq_readNat hzone.1.1, stringNatOf_eq_readNat hzone.2.1⟩
      | some millis =>
          have hmillisValue := stringNatOf_eq_readNat hmillis.1
          cases zone with
          | utc => exact ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2.1,
              hbase.2.2.2.2.1, hbase.2.2.2.2.2, hmillisValue, trivial⟩
          | offset offset =>
              exact ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2.1,
                hbase.2.2.2.2.1, hbase.2.2.2.2.2, hmillisValue,
                stringNatOf_eq_readNat hzone.1.1, stringNatOf_eq_readNat hzone.2.1⟩

theorem view_denotation_eq_toMillis {v : Datetime.View}
    {c : Cedar.Thm.Datetime.DatetimeComponents}
    (hc : v.toCedarComponents? = some c) (hsyn : c.syntaxWf) :
    v.denotation = c.toMillis := by
  rcases v with ⟨input, mm, yyyy, dd, timeHh, timeMm, ss, sss,
    offset, offsetHh, offsetMm⟩
  cases timeHh <;> cases timeMm <;> cases ss <;> cases sss <;> cases offsetHh <;>
    cases offsetMm <;> cases offset <;>
    simp [Datetime.View.toCedarComponents?] at hc
  all_goals subst c
  all_goals
    have hvalues := cedarNatValuesAgree hsyn
  all_goals
    simp only [Datetime.View.denotation, value_eq_epochMillis,
      Cedar.Thm.Datetime.DatetimeComponents.syntaxWf,
      Cedar.Thm.Datetime.DateComponents.syntaxWf,
      Cedar.Thm.Datetime.TimePart.syntaxWf,
      Cedar.Thm.Datetime.TimeComponents.syntaxWf,
      Cedar.Thm.Datetime.IsWfOptionalMillis,
      Cedar.Thm.Datetime.Zone.syntaxWf,
      Cedar.Thm.Datetime.OffsetComponents.syntaxWf,
      Cedar.Thm.Datetime.DatetimeComponents.toMillis,
      Cedar.Thm.Datetime.DateComponents.toMillis,
      Cedar.Thm.Datetime.TimePart.toMillis,
      Cedar.Thm.Datetime.Zone.offsetSeconds,
      Cedar.Thm.Datetime.OffsetComponents.seconds,
      cedarDate, cedarTime, cedarOffset] at hsyn ⊢
  all_goals
    simp [CedarNatValuesAgree, cedarDate, cedarTime, cedarOffset] at hvalues
  all_goals
    simp [hvalues, Triptych.signOf, Triptych.readNat] at hsyn ⊢
  all_goals (try split) <;> (try simp_all) <;> omega

theorem view_wfConstraints_iff_constraintsWf {v : Datetime.View}
    {c : Cedar.Thm.Datetime.DatetimeComponents}
    (hc : v.toCedarComponents? = some c) (hsyn : c.syntaxWf) :
    v.WfConstraints ↔ c.constraintsWf := by
  rcases v with ⟨input, mm, yyyy, dd, timeHh, timeMm, ss, sss,
    offset, offsetHh, offsetMm⟩
  cases timeHh <;> cases timeMm <;> cases ss <;> cases sss <;> cases offsetHh <;>
    cases offsetMm <;> cases offset <;>
    simp [Datetime.View.toCedarComponents?] at hc
  all_goals subst c
  all_goals
    have hvalues := cedarNatValuesAgree hsyn
  all_goals
    simp only [Datetime.View.WfConstraints, Datetime.WfConstraints,
      Cedar.Thm.Datetime.DatetimeComponents.constraintsWf,
      Cedar.Thm.Datetime.DateComponents.constraintsWf,
      Cedar.Thm.Datetime.TimePart.constraintsWf,
      Cedar.Thm.Datetime.TimeComponents.constraintsWf,
      Cedar.Thm.Datetime.Zone.constraintsWf,
      Cedar.Thm.Datetime.OffsetComponents.constraintsWf,
      cedarDate, cedarTime, cedarOffset]
  all_goals
    simp [CedarNatValuesAgree, cedarDate, cedarTime, cedarOffset] at hvalues
  all_goals
    simp [hvalues, expandedDaysInMonth_eq, Triptych.natOf, Triptych.readNat] at hsyn ⊢
  all_goals omega

theorem view_valid_iff_constraintsWf {v : Datetime.View}
    {c : Cedar.Thm.Datetime.DatetimeComponents}
    (hc : v.toCedarComponents? = some c) (hsyn : c.syntaxWf) :
    v.Valid ↔ c.constraintsWf := by
  have hwf := view_wfConstraints_iff_constraintsWf hc hsyn
  have hden := view_denotation_eq_toMillis hc hsyn
  constructor
  · intro hvalid
    exact hwf.mp hvalid.1
  · intro hconstraints
    refine ⟨hwf.mpr hconstraints, ?_⟩
    have hrange := CedarSupport.Datetime.toMillis_int64_range hsyn hconstraints
    change
      (-9223372036854775808 : Int) ≤ c.toMillis ∧
        c.toMillis ≤ (9223372036854775807 : Int) at hrange
    rw [← hden] at hrange
    change
      (-9223372036854775808 : Int) ≤ v.denotation ∧
        v.denotation ≤ (9223372036854775807 : Int)
    exact hrange

end Datetime.GrammarView
