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

import Triptych.Architecture.CursorProgram

namespace Triptych.CursorProgramTests

private def decimalPlan : ScanPlan :=
  { start := "Decimal"
    pattern :=
      .capture "Sign" ["Sign"] (.optionalLiteral '-' .empty)
        (.capture "Natural" ["Natural"] (.tokenRun .digit .atLeastOne .empty)
          (.literal '.'
            (.capture "Fraction" ["Fraction"] (.tokenRun .digit (.between 1 4) .empty)
              .empty))) }

#guard
  (lowerScanPlan decimalPlan).operations =
    [ .beginCapture "Sign" ["Sign"],
      .consumeOptional '-',
      .endCapture "Sign",
      .beginCapture "Natural" ["Natural"],
      .consumeRun .digit .greedyAtLeastOne,
      .endCapture "Natural",
      .expect '.',
      .beginCapture "Fraction" ["Fraction"],
      .consumeRun .digit (.greedyBetween 1 4),
      .endCapture "Fraction" ]

#guard (lowerScanPlan decimalPlan).decode "-12.34" = decimalPlan.decode "-12.34"
#guard (lowerScanPlan decimalPlan).decode "12.34567" = decimalPlan.decode "12.34567"

example (source : String) :
    (lowerScanPlan decimalPlan).decode source = decimalPlan.decode source :=
  CursorProgram.lowerScanPlan_decode decimalPlan source

example (source : String) :
    (lowerScanPlan decimalPlan).decode source = decimalPlan.decodePattern source :=
  CursorProgram.lowerScanPlan_decodePattern decimalPlan source

end Triptych.CursorProgramTests
