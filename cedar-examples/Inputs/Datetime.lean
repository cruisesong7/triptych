/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Triptych.Architecture.Syntax
import Triptych.Architecture.Decode
import Cedar.Spec.Ext.Datetime

/-!
# Datetime example — the hard case: 5-way alternation + calendar constraints

Transcribes the complete `doc/CedarDoc/Datetime.lean` spec — the generality stress test,
exercising top-level alternation, qualified captures (`Time.hh` vs `Offset.hh`), and both
escape sections (`constraints'` for the calendar day-bound, `value'` for epoch-millis via
calendar arithmetic). No `printer` — Cedar has no canonical `ToString Datetime`. See the docs
for the feature-by-feature walkthrough.
-/

namespace CedarExamples.Datetime
open Triptych

/-! ## Author-supplied calendar helpers, used by the `constraints'` / `value'` escapes. -/

/-- Is `y` a leap year? `(4 ∣ y) ∧ (¬(100 ∣ y) ∨ (400 ∣ y))`. -/
def isLeapYear (y : Nat) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

/-- Days in month `m` of year `y` (30 for Apr/Jun/Sep/Nov, 28/29 for Feb, else 31). -/
def daysInMonth (y m : Nat) : Nat :=
  if m == 4 || m == 6 || m == 9 || m == 11 then 30
  else if m == 2 then (if isLeapYear y then 29 else 28)
  else 31

/-- The calendar day-bound `01 ≤ DD ≤ daysInMonth(YYYY, MM)` — cross-field and non-affine, so
    it goes in the `constraints'` escape. Takes the captures as plain strings. -/
def dayBound (yyyy mm dd : String) : Bool :=
  1 ≤ readNat dd && readNat dd ≤ daysInMonth (readNat yyyy) (readNat mm)

/-- Days from the Unix epoch (1970-01-01) to civil date `y-m-d`, via Howard Hinnant's
    `days_from_civil` algorithm. Calendar fields remain `Nat`; conversion to `Int` happens
    only where signed pre-epoch results are required. -/
def daysFromCivil (year month day : Nat) : Int :=
  let m : Int := month
  let d : Int := day
  let y : Int := if m > 2 then year else (year : Int) - 1
  let era : Int := (if y ≥ 0 then y else y - 399).tdiv 400
  let yoe : Int := y - era * 400
  let doy : Int := (153 * (m + (if m > 2 then -3 else 9)) + 2).tdiv 5 + d - 1
  let doe : Int := yoe * 365 + yoe.tdiv 4 - yoe.tdiv 100 + doy
  era * 146097 + doe - 719468

/-- Epoch milliseconds, as a `value'` escape (calendar arithmetic + zone offset):
      ms = (daysFromCivil(Y,M,D)·86400 + hh·3600 + mm·60 + ss)·1000 + SSS  −  offset_ms.
    Absent optional components read as 0 / UTC (via `natOf ""` / `signOf ""`). -/
def epochMillis (yyyy mm dd time_hh time_mm ss sss offset_hh offset_mm offset : String) : Int :=
  let days := daysFromCivil (readNat yyyy) (readNat mm) (readNat dd)
  let localMs :=
    (days * 86400 + natOf time_hh * 3600 + natOf time_mm * 60 + natOf ss) * 1000 + natOf sss
  let offsetMs := signOf offset * (natOf offset_hh * 3600000 + natOf offset_mm * 60000)
  localMs - offsetMs

/-- The value/domain `toSpec` conversion: Cedar's `Datetime` stores epoch millis in
    `val : Int64`, matching our `epochMillis` value and letting an external parser be compared. -/
def datetimeMillis (d : Cedar.Spec.Ext.Datetime) : Int := d.val.toInt

triptych Datetime where
  grammar
    Datetime ::= Date
               | Date "T" Time "Z"
               | Date "T" Time "." SSS "Z"
               | Date "T" Time Offset
               | Date "T" Time "." SSS Offset
    Date     ::= YYYY "-" MM "-" DD
    Time     ::= hh ":" mm ":" ss
    Offset   ::= "+" hh mm
               | "-" hh mm
    SSS      ::= digit{3}
    YYYY     ::= digit{4}
    MM       ::= digit{2}
    DD       ::= digit{2}
    hh       ::= digit{2}
    mm       ::= digit{2}
    ss       ::= digit{2}
  -- value(Datetime) = epoch millis; non-affine, so via the `value'` escape (`epochMillis`).
  value'
    epochMillis YYYY MM DD Time.hh Time.mm ss SSS Offset.hh Offset.mm Offset
    toSpec datetimeMillis
  constraints
    -- Numeric field bounds. `hh`/`mm` are reused in `Time` and `Offset`, so they are addressed
    -- by qualified capture names (`Time.hh` vs `Offset.hh`).
    nat MM ∈ [1, 12]
    nat Time.hh ∈ [0, 23]
    nat Time.mm ∈ [0, 59]
    nat ss ∈ [0, 59]
    nat Offset.hh ∈ [0, 23]
    nat Offset.mm ∈ [0, 59]
  -- The cross-field, non-affine calendar day-bound, via the `constraints'` escape.
  constraints'
    dayBound YYYY MM DD
  parser Cedar.Spec.Ext.Datetime.parse
  to "Outputs/Datetime"

-- The generated parser (value = epoch milliseconds, matching Unix timestamps):
#eval Datetime.parse "1970-01-01T00:00:00Z"       -- some 0
#eval Datetime.parse "2024-01-15T10:30:45.123Z"   -- some 1705314645123
#eval Datetime.parse "2024-01-15T10:30:45+0530"   -- some 1705294845000  (UTC = local − 05:30)
#eval Datetime.parse "2024-02-30T00:00:00Z"       -- none (calendar day-bound)

end CedarExamples.Datetime
