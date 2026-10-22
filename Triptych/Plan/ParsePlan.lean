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

import Triptych.Plan.CursorProgram
import Triptych.Plan.SearchPlan
import Triptych.Plan.SearchProgram

/-!
# Shared parser compilation plan

`ParsePlan` is the backend-neutral decision made after Triptych has elaborated a grammar:

* `cursor` carries a certified deterministic `ScanPlan`; backends lower it to the shared
  `CursorProgram` and emit specialized straight-line code;
* `search` carries a certified, reference-resolved ordered search for the remaining acyclic
  grammar surface;
* `scanner` records why plan compilation was unavailable and selects the complete scanner.

Keeping this decision separate from either emitter ensures that Lean and Verus see the same
grammar analysis. Backend-specific code generation starts only after this plan has been chosen.
-/

namespace Triptych

/-- The parser implementation strategy selected for one elaborated grammar. -/
inductive ParsePlan where
  | cursor (scan : ScanPlan)
  | search (plan : SearchPlan)
  | scanner (reason : String)
  deriving Repr, Inhabited

/-- Select the strongest parser plan currently certified for a grammar. This function never
    fails: unsupported direct shapes retain the complete scanner and the diagnostic explaining
    why specialization was unavailable. -/
def compileParsePlan (grammar : Grammar) : ParsePlan :=
  match compileScanPlan grammar with
  | .ok scan => .cursor scan
  | .error _ =>
      match compileSearchPlan grammar with
      | .ok plan => .search plan
      | .error reason => .scanner reason

namespace ParsePlan

/-- Whether this plan has a specialized cursor implementation. -/
def usesCursor : ParsePlan → Bool
  | .cursor _ => true
  | .search _ => false
  | .scanner _ => false

/-- The proof-facing deterministic plan, when specialization succeeded. -/
def scanPlan? : ParsePlan → Option ScanPlan
  | .cursor scan => some scan
  | .search _ => none
  | .scanner _ => none

/-- The proof-facing ordered search plan, when the grammar needs branching. -/
def searchPlan? : ParsePlan → Option SearchPlan
  | .cursor _ => none
  | .search plan => some plan
  | .scanner _ => none

/-- The continuation-fused program consumed by staged search backends. -/
def searchProgram? : ParsePlan → Option SearchProgram
  | .cursor _ => none
  | .search plan => some (lowerSearchPlan plan)
  | .scanner _ => none

/-- Whether this plan uses resolved ordered search. -/
def usesSearch : ParsePlan → Bool
  | .cursor _ => false
  | .search _ => true
  | .scanner _ => false

/-- Whether this plan has a generated implementation independent of source-grammar lookup. -/
def usesDirect (plan : ParsePlan) : Bool :=
  plan.usesCursor || plan.usesSearch

/-- The verified-lowered instruction program consumed by direct backends. -/
def cursorProgram? : ParsePlan → Option CursorProgram
  | .cursor scan => some (lowerScanPlan scan)
  | .search _ => none
  | .scanner _ => none

/-- Execute the selected implementation strategy in Lean. -/
def decode (plan : ParsePlan) (grammar : Grammar) (source : String) : Option CaptureMap :=
  match plan with
  | .cursor scan => (lowerScanPlan scan).decode source
  | .search searchPlan => (lowerSearchPlan searchPlan).decode source
  | .scanner _ => Triptych.scan grammar source

end ParsePlan

end Triptych
