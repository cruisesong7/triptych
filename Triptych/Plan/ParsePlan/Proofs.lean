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

import Triptych.Plan.ParsePlan
import Triptych.Plan.ScanPlan.Proofs
import Triptych.Plan.SearchPlan.Proofs
import Triptych.Plan.SearchProgram.Proofs

/-!
# Parse-plan correctness

The shared compiler decision does not change parser behavior. A successfully compiled cursor plan
is connected to the reference decoder by the scan-plan theorems, a resolved search plan is
connected by the ordered-search theorems, and the fallback case runs the complete scanner
directly.
-/

namespace Triptych

namespace ParsePlan

/-- Evidence that a parser strategy is valid for one grammar. The scanner is complete for every
    grammar. A cursor plan additionally carries the structural correspondence and capture
    functionality needed to identify its successful result with the grammar's selected parse. -/
inductive CertifiedFor (grammar : Grammar) : ParsePlan → Prop where
  | cursor {scanPlan : ScanPlan}
      (mirrors : ScanPlan.MirrorsGrammar scanPlan grammar)
      (captureFunctional : GrammarCaptureFunctional grammar)
      (certified : scanPlan.certified = true) :
      CertifiedFor grammar (.cursor scanPlan)
  | search {searchPlan : SearchPlan}
      (mirrors : SearchPlan.MirrorsGrammar searchPlan grammar) :
      CertifiedFor grammar (.search searchPlan)
  | scanner {reason : String} :
      CertifiedFor grammar (.scanner reason)

/-- Every certified parser plan has exactly the complete scanner's behavior. -/
theorem decode_eq_scan {grammar : Grammar} {plan : ParsePlan}
    (hcertified : CertifiedFor grammar plan) (source : String) :
    plan.decode grammar source = scan grammar source := by
  cases hcertified with
  | scanner =>
      rfl
  | search hmirror =>
      change (lowerSearchPlan _).decode source = scan grammar source
      rw [SearchProgram.lowerSearchPlan_decode]
      rw [SearchPlan.decode_eq_scanSearch hmirror]
      rw [scanSearch_eq_decode]
      exact (scan_eq_decode grammar source).symm
  | cursor hmirror hfunctional hplanCertified =>
      change
        (lowerScanPlan _).decode source =
          scan grammar source
      rw [CursorProgram.decode_eq_decode_of_mirrors
        hmirror hfunctional hplanCertified source]
      exact (scan_eq_decode grammar source).symm

/-- A generated cursor plan agrees with the complete scanner when its structural grammar witness
    and capture-functionality proof have been checked. This is the certificate used by direct
    backend code that embeds a plan literal instead of reducing `compileParsePlan` again. -/
theorem cursor_decode_eq_scan_of_mirrors {grammar : Grammar} {scanPlan : ScanPlan}
    (hmirror : ScanPlan.MirrorsGrammar scanPlan grammar)
    (hfunctional : GrammarCaptureFunctional grammar)
    (hcertified : scanPlan.certified = true) (source : String) :
    (ParsePlan.cursor scanPlan).decode grammar source = scan grammar source :=
  decode_eq_scan (.cursor hmirror hfunctional hcertified) source

/-- The plan selected by `compileParsePlan` always carries a certificate for its source grammar. -/
theorem compile_certifiedFor (grammar : Grammar) :
    CertifiedFor grammar (compileParsePlan grammar) := by
  cases hcompile : compileScanPlan grammar with
  | error reason =>
      cases hsearch : compileSearchPlan grammar with
      | error searchReason =>
          simpa [compileParsePlan, hcompile, hsearch] using
            (CertifiedFor.scanner (grammar := grammar) (reason := searchReason))
      | ok searchPlan =>
          simpa [compileParsePlan, hcompile, hsearch] using
            (CertifiedFor.search (compileSearchPlan_mirrorsGrammar hsearch))
  | ok scanPlan =>
      have hfunctional : GrammarCaptureFunctional grammar :=
        GrammarCaptureFunctional.of_unique grammar
          (GrammarDecodeUnique.of_staticUnique grammar
            (compileScanPlan_staticUnique hcompile))
      simpa [compileParsePlan, hcompile] using
        (CertifiedFor.cursor (compileScanPlan_mirrorsGrammar hcompile) hfunctional
          (compileScanPlan_certified hcompile))

/-- The shared plan compiler selects the cursor path exactly when scan-plan compilation succeeds. -/
theorem compile_usesCursor (grammar : Grammar) :
    (compileParsePlan grammar).usesCursor = (compileScanPlan grammar).isOk := by
  cases hscan : compileScanPlan grammar with
  | ok scanPlan =>
      simp [compileParsePlan, hscan, usesCursor, Except.isOk, Except.toBool]
  | error reason =>
      cases hsearch : compileSearchPlan grammar <;>
        simp [compileParsePlan, hscan, hsearch, usesCursor, Except.isOk, Except.toBool]

/-- The shared plan compiler selects ordered search exactly when direct compilation fails and
    ordered-search compilation succeeds. -/
theorem compile_usesSearch (grammar : Grammar) :
    (compileParsePlan grammar).usesSearch =
      (!((compileScanPlan grammar).isOk) && (compileSearchPlan grammar).isOk) := by
  cases hscan : compileScanPlan grammar with
  | ok scanPlan =>
      simp [compileParsePlan, hscan, usesSearch, Except.isOk, Except.toBool]
  | error reason =>
      cases hsearch : compileSearchPlan grammar <;>
        simp [compileParsePlan, hscan, hsearch, usesSearch, Except.isOk, Except.toBool]

/-- Executing the selected parser plan always agrees with the complete scanner. -/
@[simp] theorem compile_decode_eq_scan (grammar : Grammar) (source : String) :
    (compileParsePlan grammar).decode grammar source = scan grammar source :=
  decode_eq_scan (compile_certifiedFor grammar) source

/-- The cursor program exposed by a successful shared plan is exactly the verified lowering of
    the scan plan returned by `compileScanPlan`. -/
theorem compile_cursorProgram?_eq_some {grammar : Grammar} {scanPlan : ScanPlan}
    (hcompile : compileScanPlan grammar = .ok scanPlan) :
    (compileParsePlan grammar).cursorProgram? = some (lowerScanPlan scanPlan) := by
  simp [compileParsePlan, hcompile, cursorProgram?]

end ParsePlan

end Triptych
