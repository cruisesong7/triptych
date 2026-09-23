import Outputs.Datetime.parser
import CedarSupport.String
import Cedar.Thm.Ext.Datetime.Grammar

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

theorem daysFromCivil_eq_epochDays (year month day : Nat) :
    daysFromCivil year month day = Cedar.Thm.Datetime.epochDays year month day :=
  rfl

theorem daysInMonth_eq (year month : Nat) :
    daysInMonth year month = Cedar.Thm.Datetime.daysInMonth year month :=
  rfl

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
  rcases v with ⟨input, yyyy, mm, dd, timeHh, timeMm, ss, sss,
    offsetHh, offsetMm, offset⟩
  cases timeHh <;> cases timeMm <;> cases ss <;> cases sss <;> cases offsetHh <;>
    cases offsetMm <;> cases offset <;>
    simp [Datetime.View.toCedarComponents?] at hc
  all_goals subst c
  all_goals
    have hvalues := cedarNatValuesAgree hsyn
  all_goals
    simp only [Datetime.View.denotation, Datetime.value, epochMillis,
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

theorem view_valid_iff_constraintsWf {v : Datetime.View}
    {c : Cedar.Thm.Datetime.DatetimeComponents}
    (hc : v.toCedarComponents? = some c) (hsyn : c.syntaxWf) :
    v.Valid ↔ c.constraintsWf := by
  rcases v with ⟨input, yyyy, mm, dd, timeHh, timeMm, ss, sss,
    offsetHh, offsetMm, offset⟩
  cases timeHh <;> cases timeMm <;> cases ss <;> cases sss <;> cases offsetHh <;>
    cases offsetMm <;> cases offset <;>
    simp [Datetime.View.toCedarComponents?] at hc
  all_goals subst c
  all_goals
    have hvalues := cedarNatValuesAgree hsyn
  all_goals
    simp only [Datetime.View.Valid, Datetime.View.WfConstraints, Datetime.WfConstraints,
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
    simp [dayBound, hvalues, daysInMonth_eq, Triptych.natOf, Triptych.readNat,
      Bool.and_eq_true, decide_eq_true_eq] at hsyn ⊢
  all_goals omega

end Datetime.GrammarView
