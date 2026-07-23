/-
Conformance tests: the GENERATED parsers vs Cedar's REAL parsers, over Cedar's OWN test corpus.

This is a one-time confidence check (NOT auto-generated, NOT part of the proof story): it runs the
verified parsers `triptych` emits against the exact strings Cedar's own unit tests use
(`cedar-lean/UnitTest/{Decimal,Datetime}.lean`), so we gain empirical assurance that our
`IsValid`/`computeValue` capture every requirement Cedar's parser enforces — the range checks, the
overflow bounds, the reject cases — not just the ones we happened to think of.

Why direct equality against Cedar works as the oracle: for Decimal and Duration the `lift` clause
makes our `parse` return the SAME type as Cedar's parser (`Option Decimal` / `Option Duration`), so
`ourParse s = cedarParse s` checks BOTH acceptance and value in one shot, uniformly for valid AND
invalid strings (a rejected string makes both sides `none`). Datetime has no `lift` (Cedar has no
canonical `ToString`), so our parse yields `Option Int` (epoch millis) and we compare against
`(cedarParse s).map datetimeMillis`.

Run: `lake env lean Triptych/Examples/ConformanceTests.lean` (or build the module — the `#eval`
at the bottom fails the build with a nonzero count if any case diverges). No `native_decide`, no new
axioms: this is plain evaluation, entirely outside the verified core.
-/

import Triptych.Examples.Decimal.parser
import Triptych.Examples.Duration.parser
import Triptych.Examples.Datetime.parser
import Triptych.Examples.Decimal.grammar
import Triptych.Examples.Duration.grammar
import Triptych.Examples.Datetime.grammar
import Cedar.Spec.Ext.Decimal
import Cedar.Spec.Ext.Datetime

open Triptych
-- Bring the generated example decls into scope so we write `Decimal.parse` (the EXECUTABLE parser
-- — `gatedParseLift isValid computeValue …`, i.e. the decode-based engine, NOT the readable
-- surface `IsValid` Prop) rather than the doubly-qualified `Triptych.Examples.Decimal.Decimal.parse`.
-- Cedar's parsers stay fully qualified (they live under `Cedar.Spec.Ext.*`, no clash).
open Triptych.Examples.Decimal
open Triptych.Examples.Duration
open Triptych.Examples.Datetime

namespace Triptych.ConformanceTests

/-- A single string-keyed check: does `actual` match `expected`? Returns `none` on pass, or a
    failure message on mismatch. Both sides are `Repr`-printable. -/
def check {α} [DecidableEq α] [Repr α] (name : String) (actual expected : α) : Option String :=
  if actual = expected then none
  else some s!"FAILED [{name}]\n  actual:   {repr actual}\n  expected: {repr expected}"

/-- Run a list of checks, print each failure, and return the failure count. -/
def runChecks (suite : String) (checks : List (Option String)) : IO Nat := do
  let failures := checks.filterMap id
  IO.println s!"── {suite}: {checks.length - failures.length}/{checks.length} passed"
  for msg in failures do
    IO.println msg
  pure failures.length

/-! ## Decimal — direct equality vs `Cedar.Spec.Ext.Decimal.parse` (same `Option Decimal` type).

Strings taken verbatim from `cedar-lean/UnitTest/Decimal.lean` (valid + invalid). Cedar is the
oracle: we assert `Decimal.parse s = Cedar…Decimal.parse s`, so we don't even hard-code the expected
decimal values — any divergence in acceptance OR value shows up. -/

/-- Every string Cedar's Decimal unit tests exercise (valid roundtrip/parse cases + invalid cases). -/
def decimalStrings : List String :=
  [ -- valid (roundtrip + parse-value tests)
    "3.14", "11.0003", "11.003", "11.3000", "123.0", "-123.0", "-3.14", "-11.0003",
    "0.0", "0.0000", "12.34", "1.2345", "-1.0", "-4.2", "-9.876",
    "-922337203685477.5808", "922337203685477.5807",
    "0.23", "-0.23", "-0.0023", "-0.0001", "-1.0000", "-0.9999",
    -- invalid
    "1.x", "1.-2", "12", ".12", "-.12", "12.", "1.23456",
    "922337203685477.5808", "-922337203685477.5809" ]

def decimalChecks : List (Option String) :=
  decimalStrings.map (fun s =>
    check s (Decimal.parse s) (Cedar.Spec.Ext.Decimal.parse s))

/-! ## Duration — direct equality vs `Cedar.Spec.Ext.Datetime.Duration.parse` (same `Option
    Duration` type). Strings from `cedar-lean/UnitTest/Datetime.lean`. -/

def durationStrings : List String :=
  [ -- valid
    "0ms", "0d0s", "1ms", "1s", "1m", "1h", "1d", "12s340ms", "1s234ms",
    "-1ms", "-1s", "-4s200ms", "-9s876ms", "106751d23h47m16s854ms", "-106751d23h47m16s854ms",
    "-9223372036854775808ms", "9223372036854775807ms", "1d2h3m4s5ms", "2d12h", "3m30s",
    "1h30m45s", "2d5h20m", "-1d12h", "-3h45m", "1d1ms", "59m59s999ms", "23h59m59s999ms", "0d0h0m0s0ms",
    -- invalid
    "", "d", "1d-1s", "1d2h3m4s5ms6", "1x2m3s", "1.23s", "1s1d", "1s1s",
    "1d2h3m4s5ms ", " 1d2h3m4s5ms", "1d9223372036854775807ms", "1d92233720368547758071ms",
    "9223372036854776s1ms", "-12142442932071h" ]

def durationChecks : List (Option String) :=
  durationStrings.map (fun s =>
    check s (Duration.parse s) (Cedar.Spec.Ext.Datetime.Duration.parse s))

/-! ## Datetime — no `lift`, so our parse yields `Option Int` (epoch millis). Compare against
    `(Cedar…Datetime.parse s).map datetimeMillis`. Strings from `cedar-lean/UnitTest/Datetime.lean`. -/

def datetimeStrings : List String :=
  [ -- valid
    "2022-10-10", "1969-12-31", "1969-12-31T23:59:59Z", "1969-12-31T23:59:59.001Z",
    "1969-12-31T23:59:59.999Z", "2024-10-15", "2024-10-15T11:38:02Z", "2024-10-15T11:38:02.101Z",
    "2024-10-15T11:38:02.101-1134", "2024-10-15T11:38:02.101+1134", "2024-10-15T11:38:02+1134",
    "2024-10-15T11:38:02-1134",
    -- invalid
    "", "a", "-", "-1", " 2022-10-10", "2022-10-10 ", "2022-10- 10", "11-12-13", "011-12-13",
    "00011-12-13", "0001-2-13", "0001-012-13", "0001-02-3", "0001-02-003", "0001-01-01T1:01:01Z",
    "0001-01-01T001:01:01Z", "0001-01-01T01:1:01Z", "0001-01-01T01:001:01Z", "0001-01-01T01:01:1Z",
    "0001-01-01T01:01:001Z", "0001-01-01T01:01:01.01Z", "0001-01-01T01:01:01.0001Z",
    "0001-01-01T01:01:01.001+01", "0001-01-01T01:01:01.001+001", "0001-01-01T01:01:01.001+00001",
    "0001-01-01T01:01:01.001+00:01", "0001-01-01T01:01:01.001+00:00:01", "-0001-01-01", "1111-1x-20",
    "1111-Jul-20", "1111-July-20", "1111-J-20", "2024-10-15Z", "2024-10-15T11:38:02ZZ", "2024-01-01T",
    "2024-01-01Ta", "2024-01-01T01:", "2024-01-01T01:02", "2024-01-01T01:02:0b", "2024-01-01T01::02:03",
    "2024-01-01T01::02::03", "2024-01-01T31:02:03Z", "2024-01-01T01:60:03Z", "2016-12-31T23:59:60Z",
    "2016-12-31T23:59:61Z", "2024-01-01T00:00:00", "2024-01-01T00:00:00T", "2024-01-01T00:00:00ZZ",
    "2024-01-01T00:00:00x001Z", "2024-01-01T00:00:00.001ZZ", "2016-12-31T23:59:60.000Z",
    "2016-12-31T23:59:60.000+0200", "2024-01-01T00:00:00.0001Z", "2024-01-01T00:00:00.001+00000",
    "2024-01-01T00:00:00.001-00000", "2016-01-01T00:00:00+2400", "2016-01-01T00:00:00+0060",
    "2016-01-01T00:00:00+9999",
    -- non-ASCII sign glyphs (U+2795/U+2796 emoji) in the offset — must be rejected
    "2024-01-01T00:00:00➕0000", "2024-01-01T00:00:00➖0000",
    "2024-01-01T00:00:00.001➕0000", "2024-01-01T00:00:00.001➖0000" ]

def datetimeChecks : List (Option String) :=
  datetimeStrings.map (fun s =>
    check s (Datetime.parse s)
      ((Cedar.Spec.Ext.Datetime.parse s).map datetimeMillis))

/-- Run all three suites; print totals; return the total failure count. -/
def runAll : IO Nat := do
  IO.println "════════ Triptych ↔ Cedar parser conformance ════════"
  let d ← runChecks "Decimal"  decimalChecks
  let u ← runChecks "Duration" durationChecks
  let t ← runChecks "Datetime" datetimeChecks
  let total := d + u + t
  IO.println s!"════════ total failures: {total} ════════"
  pure total

end Triptych.ConformanceTests

-- Build-gating: evaluates the suites; a nonzero failure count aborts elaboration, so a broken
-- spec fails `lake build`. (Prints per-suite pass counts + any diverging case.)
#eval do
  let failures ← Triptych.ConformanceTests.runAll
  if failures != 0 then
    throw (IO.userError s!"{failures} conformance test(s) failed")
