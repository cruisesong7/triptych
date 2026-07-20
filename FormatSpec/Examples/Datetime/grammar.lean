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

import FormatSpec.Syntax
import FormatSpec.Decode
import Cedar.Spec.Ext.Datetime

/-!
# Datetime example — the hard case: 5-way alternation + calendar constraints

Transcribes `doc/CedarDoc/Datetime.lean` — the COMPLETE spec (grammar + all constraints +
value). The generality stress test, exercising every DSL feature incl. both escapes:
* top-level **alternation** (`Datetime ::= Date | Date "T" Time "Z" | …`) — the `|` support;
* inline `('+' | '-')` in `Offset` — desugared into two `Offset` alternatives;
* fixed-width terminals (`Digit{4}`, `Digit{2}`, `Digit{3}`);
* numeric field bounds (`nat MM ∈ [1,12]`, …) — the affine constraint DSL, incl. QUALIFIED
  captures (`Time.hh` vs `Offset.hh`, the reused nonterminal);
* the calendar day-bound (`01 ≤ DD ≤ daysInMonth`) — non-affine, via the `constraints'` escape;
* value = epoch-milliseconds via calendar arithmetic + zone offset — non-affine, via the
  `value'` escape. Both escapes use author-supplied helpers below (no `Cedar.Thm` import).
Writes `spec.lean` next to this file.
-/

namespace FormatSpec.Examples.Datetime
open FormatSpec

/-! ## Author-supplied calendar helpers (the escape sections' contract)

The `constraints'` / `value'` ESCAPE sections mean "the author provides the Lean for a
check/value outside the affine DSL vocabulary". So — as the author — we write the small,
standard calendar functions here. FormatSpec deliberately does NOT import a hand-written
`Cedar.Thm.Ext.Datetime` spec: this tool is the *upstream* generator meant to replace/
validate that artifact, so depending on it would be circular. These helpers use only
FormatSpec's own `natOf`/`signOf` readers on the captured component strings. -/

/-- Is `y` a leap year? `(4 ∣ y) ∧ (¬(100 ∣ y) ∨ (400 ∣ y))`. -/
def isLeapYear (y : Int) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

/-- Days in month `m` of year `y` (30 for Apr/Jun/Sep/Nov, 28/29 for Feb, else 31). -/
def daysInMonth (y m : Int) : Int :=
  if m == 4 || m == 6 || m == 9 || m == 11 then 30
  else if m == 2 then (if isLeapYear y then 29 else 28)
  else 31

/-- The calendar day-bound `01 ≤ DD ≤ daysInMonth(YYYY, MM)` — the non-affine, cross-field
    constraint the affine DSL cannot express, wired via the `constraints'` escape section.
    Takes the captured components as plain `String`s (in the order listed in the
    `constraints'` entry `dayBound YYYY MM DD`); `natOf` is FormatSpec's own unsigned-decimal
    reader. No `Env`/`Option` plumbing — the generator supplies that. -/
def dayBound (yyyy mm dd : String) : Bool :=
  1 ≤ natOf dd && natOf dd ≤ daysInMonth (natOf yyyy) (natOf mm)

/-- Days from the Unix epoch (1970-01-01) to civil date `y-m-d`, via Howard Hinnant's
    `days_from_civil` algorithm — chosen because it uses only truncating integer division
    (matching Lean `Int` `/`, `%`), is branch-light, and is correct for the full proleptic
    Gregorian range. Shifts the year so the leap day falls at the era's end, counts era
    (400-year) cycles, then the day-of-era. Result is negative for pre-epoch dates. -/
def daysFromCivil (y m d : Int) : Int :=
  let y := if m ≤ 2 then y - 1 else y            -- March-based year (Feb at the end)
  let era := (if y ≥ 0 then y else y - 399) / 400
  let yoe := y - era * 400                        -- year of era [0, 399]
  let doy := (153 * (if m > 2 then m - 3 else m + 9) + 2) / 5 + d - 1   -- day of year [0, 365]
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy                       -- day of era [0, 146096]
  era * 146097 + doe - 719468                     -- 719468 = days from 0000-03-01 to 1970-01-01

/-- Epoch milliseconds of a datetime, as a `value'` escape over the captured components. This
    is the NON-AFFINE value the DSL cannot express (calendar arithmetic + zone offset):
      ms = (daysFromCivil(Y,M,D)·86400 + hh·3600 + mm·60 + ss)·1000 + SSS  −  offset_ms
    where `offset_ms = signOf(Offset)·(Offset.hh·3600000 + Offset.mm·60000)` (a `+05:30`
    zone is ahead of UTC, so UTC = local − offset). Absent optional components read as 0 (via
    `natOf ""`); an absent `Offset`/sign reads as `+`/0 (via `signOf ""`/`natOf ""`), i.e.
    UTC — correct for the `Z` and date-only forms. Captures are passed as strings, in the
    order of the `value'` entry. -/
def epochMillis (yyyy mm dd time_hh time_mm ss sss offset_hh offset_mm offset : String) : Int :=
  let days := daysFromCivil (natOf yyyy) (natOf mm) (natOf dd)
  let localMs :=
    (days * 86400 + natOf time_hh * 3600 + natOf time_mm * 60 + natOf ss) * 1000 + natOf sss
  let offsetMs := signOf offset * (natOf offset_hh * 3600000 + natOf offset_mm * 60000)
  localMs - offsetMs

/-- The projection for the `parser` clause: Cedar's `Datetime` stores epoch milliseconds in
    `val : Int64`, matching our `epochMillis` value — read it out as `Int`. (No `printer`
    clause: Cedar has no canonical `ToString Datetime`, since a datetime has several accepted
    surface forms — the printer theorems need a single canonical serializer, which is absent.) -/
def datetimeMillis (d : Cedar.Spec.Ext.Datetime) : Int := d.val.toInt

format_spec Datetime where
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
  -- value(Datetime) = epoch milliseconds, via calendar arithmetic + zone offset. Fully
  -- non-affine (leap years, days-from-civil, offset application), so it goes in the `value'`
  -- ESCAPE section: the author-supplied `epochMillis` applied to the captures it reads.
  -- `Offset` (the whole "+05:30"/"" capture) supplies the sign via `signOf`.
  value' epochMillis YYYY MM DD Time.hh Time.mm ss SSS Offset.hh Offset.mm Offset
  constraints
    -- The doc's simple numeric field bounds. These fit the DSL directly (decidable).
    -- `hh`/`mm` are reused in BOTH `Time` and `Offset`, so we address them by their
    -- QUALIFIED capture names (`Time.hh` vs `Offset.hh`) — a plain `nat hh` would only see
    -- the first (Time) occurrence. `MM`/`DD`/`ss` are unique, so a bare name suffices.
    nat MM ∈ [1, 12]
    nat Time.hh ∈ [0, 23]
    nat Time.mm ∈ [0, 59]
    nat ss ∈ [0, 59]
    nat Offset.hh ∈ [0, 23]
    nat Offset.mm ∈ [0, 59]
  -- The calendar day-bound `01 ≤ DD ≤ daysInMonth(YYYY, MM)` is cross-field and non-affine
  -- (leap years, month table), so it is NOT in the DSL vocabulary. It goes in the
  -- `constraints'` ESCAPE section: each line is an ordinary Lean call of an author-supplied
  -- function on the captures it reads (the generator feeds each its decoded string).
  constraints'
    dayBound YYYY MM DD
    -- (value(Datetime) = epoch milliseconds would go in a `value'` escape section, but Cedar's
    -- parser delegates it to `Std.Time` with no standalone arithmetic fn, so it is omitted.)
  parser Cedar.Spec.Ext.Datetime.parse projection datetimeMillis
  -- Write the generated modules `spec.lean` / `parser.lean` / `soundness.lean` into this dir.
  to "FormatSpec/Examples/Datetime"

-- The 5 top-level forms + the 2-alt Offset exercise alternation end to end.
#check (Datetime.IsWf.Datetime : String → Prop)
#check (Datetime.IsWf.Offset   : String → Prop)

-- Reconciliation + decidability of the 5-way alternation (mixed child depths; std axioms).
#check (Datetime.IsWf_equiv : ∀ s, IsWf Datetime.grammar s ↔ Datetime.IsWf.Datetime s)
example : DecidablePred Datetime.IsWf.Datetime := inferInstance

-- The `value'` epoch-millis fn, evaluated on decoded inputs (matches Unix timestamps):
private def epochMs (s : String) : Int := Datetime.valueFn (FormatSpec.envOf Datetime.grammar s)
#eval epochMs "1970-01-01T00:00:00Z"       -- 0
#eval epochMs "2024-01-15T10:30:45Z"       -- 1705314645000
#eval epochMs "2024-01-15T10:30:45.123Z"   -- 1705314645123
#eval epochMs "2024-01-15T10:30:45+0530"   -- 1705294845000  (UTC = local − 05:30)
#eval epochMs "1969-12-31T00:00:00Z"       -- -86400000       (pre-epoch)

-- The generated verified parser + the external-parser obligations against Cedar's real
-- `Datetime.parse` (epoch-millis projection). No `printer` clause — Cedar has no canonical
-- `ToString Datetime` (several accepted surface forms), so no roundtrip/injective/normalize.
#check (Datetime.parse : String → Option Int)
#check @Datetime.parse_sound
#check @Datetime.extparse_sound     -- vs Cedar.Spec.Ext.Datetime.parse, projection datetimeMillis
#check @Datetime.extparse_complete
#check @Datetime.extparse_reject

end FormatSpec.Examples.Datetime
