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

import Triptych.Architecture.Scanner
import Triptych.Theorems.ScanPlan

namespace Triptych.ScanPlanTests

private def item (symbol : Sym) (optional := false) : SymItem :=
  { sym := symbol, optional }

private def decimalGrammar : Grammar :=
  { start := "Decimal"
    prods :=
      [ { name := "Decimal"
          alts := [[item (.ref "Sign"), item (.ref "Natural"), item (.lit "."),
            item (.ref "Fraction")]] },
        { name := "Sign", alts := [[item (.lit "-") true]] },
        { name := "Natural", alts := [[item (.term .digit .atLeastOne)]] },
        { name := "Fraction", alts := [[item (.term .digit (.between 1 4))]] } ] }

#guard
  match compileScanPlan decimalGrammar with
  | .error _ => false
  | .ok plan =>
      plan.certifiedFor decimalGrammar &&
      plan.operations ==
        [ .beginCapture "Sign" ["Sign"],
          .optionalLiteral '-',
          .endCapture "Sign",
          .beginCapture "Natural" ["Natural"],
          .tokenRun .digit .atLeastOne,
          .endCapture "Natural",
          .literal '.',
          .beginCapture "Fraction" ["Fraction"],
          .tokenRun .digit (.between 1 4),
          .endCapture "Fraction" ]

#guard
  (compileScanPlan decimalGrammar).toOption.bind (·.decode "-12.34") =
    some [("Sign", "-"), ("Natural", "12"), ("Fraction", "34")]

#guard
  (compileScanPlan decimalGrammar).toOption.bind (·.decode "12.34567") = none

private def decimalSamples :=
  ["-12.34", "12.3", "0.0000", "-0.1", "", "-", "12", "12.", "12.34567", "x.1"]

#guard
  match compileScanPlan decimalGrammar with
  | .error _ => false
  | .ok plan => decimalSamples.all fun input => plan.decode input == scan decimalGrammar input

#guard
  match compileScanPlan decimalGrammar with
  | .error _ => false
  | .ok plan =>
      decimalSamples.all fun input =>
        plan.decodeCertified decimalGrammar input == decode decimalGrammar input

private def adjacentFixedGrammar : Grammar :=
  { start := "Root"
    prods :=
      [{ name := "Root"
         alts :=
           [[item (.ref "Left"), item (.ref "Right")]] },
       { name := "Left", alts := [[item (.term .digit (.exactly 2))]] },
       { name := "Right", alts := [[item (.term .digit (.exactly 2))]] }] }

/- Exact-width runs advance by their declared widths instead of greedily consuming the entire
   character-class run. -/
#guard
  (compileScanPlan adjacentFixedGrammar).toOption.bind (·.decode "1234") =
    some [("Left", "12"), ("Right", "34")]

#guard
  match compileScanPlan adjacentFixedGrammar with
  | .error _ => false
  | .ok plan =>
      ["1234", "123", "12345", "12ab"].all fun input =>
        plan.decode input == scan adjacentFixedGrammar input

private def ambiguousBoundaryGrammar : Grammar :=
  { start := "Root"
    prods :=
      [ { name := "Root", alts := [[item (.ref "Left"), item (.ref "Right")]] },
        { name := "Left", alts := [[item (.term .digit .atLeastOne)]] },
        { name := "Right", alts := [[item (.term .digit .atLeastOne)]] } ] }

#guard
  match compileScanPlan ambiguousBoundaryGrammar with
  | .error _ => true
  | .ok _ => false

private def nestedCaptureGrammar : Grammar :=
  { start := "Root"
    prods :=
      [ { name := "Root", alts := [[item (.ref "Outer")]] },
        { name := "Outer", alts := [[item (.ref "Inner"), item (.lit "!")]] },
        { name := "Inner", alts := [[item (.term .digit (.exactly 2))]] } ] }

#guard
  match compileScanPlan nestedCaptureGrammar with
  | .error _ => false
  | .ok plan =>
      plan.captureKeys =
        [("Outer", ["Outer"]), ("Inner", ["Inner", "Outer.Inner"])] &&
      plan.decode "12!" = scan nestedCaptureGrammar "12!"

example {plan : ScanPlan} (hcompile : compileScanPlan decimalGrammar = .ok plan) :
    plan.captureNamesUnique = true ∧ plan.deterministicBoundaries = true ∧
      plan.matchesGrammar decimalGrammar = true :=
  ⟨compileScanPlan_captureNamesUnique hcompile,
    compileScanPlan_deterministicBoundaries hcompile,
    compileScanPlan_matchesGrammar hcompile⟩

example {plan : ScanPlan} (hcompile : compileScanPlan decimalGrammar = .ok plan)
    {source : String} {captures : CaptureMap}
    (hdecode : (lowerScanPlan plan).decode source = some captures) :
    decode decimalGrammar source = some captures :=
  compileCursorProgram_decode_sound hcompile hdecode

example {plan : ScanPlan} (hcompile : compileScanPlan decimalGrammar = .ok plan)
    (source : String) :
    (lowerScanPlan plan).decodeCertified decimalGrammar source =
      decode decimalGrammar source :=
  compileCursorProgram_decodeCertified_eq_decode hcompile source

example {plan : ScanPlan} (hcertified : plan.certifiedFor decimalGrammar = true)
    (source : String) :
    (lowerScanPlan plan).decodeCertified decimalGrammar source =
      decode decimalGrammar source :=
  CursorProgram.decodeCertified_eq_decode hcertified source

end Triptych.ScanPlanTests
