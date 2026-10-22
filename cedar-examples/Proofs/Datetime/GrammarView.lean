import Outputs.Datetime.parser
import CedarSupport.Datetime
import CedarSupport.String
import Cedar.Thm.Ext.Datetime.Grammar

/-! Relates the generated Datetime view to parser-independent grammar components. -/

open Triptych
open CedarSupport.String
open CedarExamples.Datetime

namespace Datetime.GrammarView

/-- Transparent names for folding the expanded DSL arithmetic in the Cedar bridge proofs. -/
private def daysFromCivil (year month day : Nat) : Int :=
  let m : Int := month
  let d : Int := day
  let y : Int := if m > 2 then year else (year : Int) - 1
  let era : Int := if y ≥ 0 then y.tdiv 400 else (y - 399).tdiv 400
  let yoe : Int := y - era * 400
  let doy : Int := (153 * (m + (if m > 2 then -3 else 9)) + 2).tdiv 5 + (d - 1)
  let doe : Int := yoe * 365 + yoe.tdiv 4 - yoe.tdiv 100 + doy
  era * 146097 + doe - 719468

private def daysInMonth (year month : Nat) : Nat :=
  if month == 4 || month == 6 || month == 9 || month == 11 then 30
  else if month == 2 then
    if year % 4 == 0 && (year % 100 != 0 || year % 400 == 0) then 29 else 28
  else 31

private def daysInMonthValue (year month : Int) : Int :=
  if month = 4 then 30
  else if month = 6 then 30
  else if month = 9 then 30
  else if month = 11 then 30
  else if month = 2 then
    if
        (if year.tmod 4 = 0 then
          if year.tmod 100 = 0 then
            if year.tmod 400 = 0 then (1 : Int) else 0
          else (1 : Int)
        else (0 : Int)) =
        1 then
      29
    else 28
  else 31

private def dayBound (yyyy mm dd : String) : Bool :=
  1 ≤ readNat dd && readNat dd ≤ daysInMonth (readNat yyyy) (readNat mm)

private def basicWfConstraints
    (mm time_hh time_mm ss offset_hh offset_mm : String) : Prop :=
  ((((((1 : Int) ≤ natOf mm ∧ natOf mm ≤ 12) ∧
          ((0 : Int) ≤ natOf time_hh ∧ natOf time_hh ≤ 23)) ∧
        ((0 : Int) ≤ natOf time_mm ∧ natOf time_mm ≤ 59)) ∧
      ((0 : Int) ≤ natOf ss ∧ natOf ss ≤ 59)) ∧
    ((0 : Int) ≤ natOf offset_hh ∧ natOf offset_hh ≤ 23)) ∧
  ((0 : Int) ≤ natOf offset_mm ∧ natOf offset_mm ≤ 59)

private def epochMillis
    (yyyy mm dd time_hh time_mm ss sss offset_hh offset_mm offset : String) : Int :=
  let days := daysFromCivil (readNat yyyy) (readNat mm) (readNat dd)
  let localMs :=
    (days * 86400 + natOf time_hh * 3600 + natOf time_mm * 60 + natOf ss) * 1000 +
      natOf sss
  let offsetMs := signOf offset * (natOf offset_hh * 3600000 + natOf offset_mm * 60000)
  localMs - offsetMs

private theorem value_eq_epochMillis
    (mm yyyy dd time_hh time_mm ss sss offset offset_hh offset_mm : String) :
    Datetime.value mm yyyy dd time_hh time_mm ss sss offset offset_hh offset_mm =
      epochMillis yyyy mm dd time_hh time_mm ss sss offset_hh offset_mm offset := by
  rfl

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

theorem daysFromCivil_eq_epochDays (year month day : Nat) :
    daysFromCivil year month day = Cedar.Thm.Datetime.epochDays year month day := by
  have era_eq (y : Int) :
      (if 0 ≤ y then y.tdiv 400 else (y - 399).tdiv 400) =
        (if 0 ≤ y then y else y - 399).tdiv 400 := by
    by_cases h : 0 ≤ y <;> simp [h]
  simp [daysFromCivil, Cedar.Thm.Datetime.epochDays, era_eq]
  omega

theorem daysInMonth_eq (year month : Nat) :
    daysInMonth year month = Cedar.Thm.Datetime.daysInMonth year month :=
  rfl

theorem daysInMonthValue_eq_daysInMonth (year month : Nat) :
    daysInMonthValue year month = daysInMonth year month := by
  have h4 : (year : Int).tmod 4 = ((year % 4 : Nat) : Int) := by
    exact (Int.ofNat_tmod year 4).symm
  have h100 : (year : Int).tmod 100 = ((year % 100 : Nat) : Int) := by
    exact (Int.ofNat_tmod year 100).symm
  have h400 : (year : Int).tmod 400 = ((year % 400 : Nat) : Int) := by
    exact (Int.ofNat_tmod year 400).symm
  have h4i : ((year : Int).tmod 4 = 0) ↔ year % 4 = 0 := by
    rw [h4]
    exact Int.natCast_eq_zero
  have h100i : ((year : Int).tmod 100 = 0) ↔ year % 100 = 0 := by
    rw [h100]
    exact Int.natCast_eq_zero
  have h400i : ((year : Int).tmod 400 = 0) ↔ year % 400 = 0 := by
    rw [h400]
    exact Int.natCast_eq_zero
  have hm4 : ((month : Int) = 4) ↔ month = 4 := by omega
  have hm6 : ((month : Int) = 6) ↔ month = 6 := by omega
  have hm9 : ((month : Int) = 9) ↔ month = 9 := by omega
  have hm11 : ((month : Int) = 11) ↔ month = 11 := by omega
  have hm2 : ((month : Int) = 2) ↔ month = 2 := by omega
  by_cases m4 : month = 4 <;>
    by_cases m6 : month = 6 <;>
    by_cases m9 : month = 9 <;>
    by_cases m11 : month = 11 <;>
    by_cases m2 : month = 2 <;>
    by_cases y4 : year % 4 = 0 <;>
    by_cases y100 : year % 100 = 0 <;>
    by_cases y400 : year % 400 = 0 <;>
    simp [daysInMonthValue, daysInMonth, h4i, h100i, h400i,
      hm4, hm6, hm9, hm11, hm2, m4, m6, m9, m11, m2, y4, y100, y400]

private theorem wfConstraints_eq_basic
    (mm time_hh time_mm ss offset_hh offset_mm dd yyyy : String) :
    Datetime.WfConstraints mm time_hh time_mm ss offset_hh offset_mm dd yyyy ↔
      basicWfConstraints mm time_hh time_mm ss offset_hh offset_mm ∧
        (1 : Int) ≤ natOf dd ∧
          natOf dd ≤ daysInMonthValue (natOf yyyy) (natOf mm) := by
  unfold Datetime.WfConstraints basicWfConstraints daysInMonthValue
  simp only [and_assoc]

private theorem wfConstraints_iff_cedarBounds
    (mm time_hh time_mm ss offset_hh offset_mm dd yyyy : String) :
    Datetime.WfConstraints mm time_hh time_mm ss offset_hh offset_mm dd yyyy ↔
      basicWfConstraints mm time_hh time_mm ss offset_hh offset_mm ∧
      (1 : Int) ≤ natOf dd ∧
        natOf dd ≤ Cedar.Thm.Datetime.daysInMonth (readNat yyyy) (readNat mm) := by
  rw [wfConstraints_eq_basic]
  have hdays :
      daysInMonthValue (natOf yyyy) (natOf mm) =
        Cedar.Thm.Datetime.daysInMonth (readNat yyyy) (readNat mm) := by
    rw [show natOf yyyy = (readNat yyyy : Int) by rfl,
      show natOf mm = (readNat mm : Int) by rfl,
      daysInMonthValue_eq_daysInMonth, daysInMonth_eq]
  rw [hdays]

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
    simp only [Datetime.View.denotation, value_eq_epochMillis, epochMillis,
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
    simp [hvalues, daysFromCivil_eq_epochDays, Triptych.natOf, Triptych.signOf,
      Triptych.readNat] at hsyn ⊢
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
    simp only [Datetime.View.WfConstraints, wfConstraints_iff_cedarBounds,
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
    simp [basicWfConstraints, hvalues, Triptych.natOf, Triptych.readNat] at hsyn ⊢
  all_goals omega

theorem view_valid_iff_constraintsWf {v : Datetime.View}
    {c : Cedar.Thm.Datetime.DatetimeComponents}
    (hc : v.toCedarComponents? = some c) (hsyn : c.syntaxWf) :
    v.Valid ↔ c.constraintsWf := by
  rw [Datetime.View.Valid, view_wfConstraints_iff_constraintsWf hc hsyn]
  constructor
  · exact And.left
  · intro hconstraints
    refine ⟨hconstraints, ?_⟩
    have hrange := CedarSupport.Datetime.toMillis_int64_range hsyn hconstraints
    have hdenotation := view_denotation_eq_toMillis hc hsyn
    unfold Datetime.View.Constraints Datetime.Constraints
    rw [← Datetime.View.denotation, hdenotation]
    simpa only [Int64.«MIN», Int64.«MAX»] using hrange

end Datetime.GrammarView
