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

import Triptych.Backend.Verus.AstSemantics
import Triptych.Backend.Verus.Translation

/-!
# End-to-end translation preservation

These theorems compose Triptych-AST translation, IR lowering, and the Verus-AST evaluator. They
use `canonicalCalls`, whose generated helper bodies are validated separately by
`helperDeclaration_realizes`.

Coverage is total over `ValExpr` and `Constraint`. The only hypothesis beyond environment
agreement is `ConstraintStringCapturesPresent`, required for the same reason as in the
IR-denotation theorem: Verus views represent scalar fields as byte sequences rather than
options, so `Constraint.strEq`'s vacuous truth on an absent capture needs the capture to be
present to transfer.
-/

namespace Triptych.Backend.Verus

def AstEnvAgrees (sourceEnv : Env) (fieldName : FieldName)
    (targetEnv : Ast.EvalEnv) : Prop :=
  ∀ source, targetEnv (fieldName source) =
    some (.text (Ast.encodeString ((sourceEnv source).getD "")))

@[simp]
theorem lower_translateValExpr_preserves (sourceEnv : Env) (fieldName : FieldName)
    (targetEnv : Ast.EvalEnv) (expression : ValExpr)
    (hagrees : AstEnvAgrees sourceEnv fieldName targetEnv) :
    (lowerExpr (translateValExpr fieldName expression)).evaluate canonicalCalls targetEnv =
      some (.int (expression.eval sourceEnv)) := by
  induction expression with
  | lit literal =>
      simp [translateValExpr, lowerExpr, Ast.Expr.evaluate, ValExpr.eval]
  | «nat» source =>
      simp [translateValExpr, lowerExpr, captureExpr, Ast.Expr.evaluate, hagrees source,
        ValExpr.eval]
  | «int» source =>
      simp [translateValExpr, lowerExpr, captureExpr, Ast.Expr.evaluate, hagrees source,
        ValExpr.eval]
  | «len» source =>
      simp [translateValExpr, lowerExpr, captureExpr, Ast.Expr.evaluate, hagrees source,
        ValExpr.eval, Ast.encodeString]
      rw [String.length_toList]
      exact lenOf_capture sourceEnv source
  | «count» source =>
      simp [translateValExpr, lowerExpr, captureExpr, Ast.Expr.evaluate,
        hagrees (source ++ "#count"), ValExpr.eval]
  | signOf source =>
      simp [translateValExpr, lowerExpr, captureExpr, Ast.Expr.evaluate, hagrees source,
        ValExpr.eval]
  | add left right left_ih right_ih =>
      simp [translateValExpr, lowerExpr, Ast.Expr.evaluate, ValExpr.eval,
        left_ih, right_ih]
  | sub left right left_ih right_ih =>
      simp [translateValExpr, lowerExpr, Ast.Expr.evaluate, ValExpr.eval,
        left_ih, right_ih]
  | mul left right left_ih right_ih =>
      simp [translateValExpr, lowerExpr, Ast.Expr.evaluate, ValExpr.eval,
        left_ih, right_ih]
  | pow base exponent base_ih exponent_ih =>
      simp [translateValExpr, lowerExpr, Ast.Expr.evaluate, ValExpr.eval,
        base_ih, exponent_ih, intPowModel]
  | neg expression expression_ih =>
      simp [translateValExpr, lowerExpr, Ast.Expr.evaluate, ValExpr.eval,
        expression_ih]

private theorem string_eq_of_toList_eq {a b : String} (h : a.toList = b.toList) : a = b :=
  String.ext (by simpa using h)

private theorem presentCount_shift (ss : List String) (n : Nat) :
    ss.foldl (fun acc s => if s == "" then acc else acc + 1) n =
      n + presentCount ss := by
  induction ss generalizing n with
  | nil => simp [presentCount]
  | cons s ss ih =>
      simp only [presentCount, List.foldl_cons]
      rw [ih, ih]
      by_cases hs : s = "" <;> simp [hs] <;> omega

private theorem presentCount_cons (s : String) (ss : List String) :
    presentCount (s :: ss) = (if s = "" then 0 else 1) + presentCount ss := by
  simp only [presentCount, List.foldl_cons]
  rw [presentCount_shift ss (if s == "" then 0 else 1)]
  by_cases hs : s = "" <;> simp [presentCount, hs]

/-- The lowered presence indicator of one capture evaluates to the 0/1 presence value. -/
private theorem evaluate_presence (sourceEnv : Env) (fieldName : FieldName)
    (targetEnv : Ast.EvalEnv) (hagrees : AstEnvAgrees sourceEnv fieldName targetEnv)
    (source : String) :
    (Ast.Expr.ifThenElse
        (.intEq (.textLen (.var (fieldName source))) (.intLit 0))
        (.intLit 0) (.intLit 1)).evaluate canonicalCalls targetEnv =
      some (.int (if (sourceEnv source).getD "" = "" then 0 else 1)) := by
  by_cases hempty : (sourceEnv source).getD "" = "" <;>
    simp [Ast.Expr.evaluate, hagrees source, hempty]

private theorem evaluate_presence_foldl (sourceEnv : Env) (fieldName : FieldName)
    (targetEnv : Ast.EvalEnv) (hagrees : AstEnvAgrees sourceEnv fieldName targetEnv)
    (sources : List String) (acc : Ast.Expr) (accValue : Int)
    (hacc : acc.evaluate canonicalCalls targetEnv = some (.int accValue)) :
    ((sources.map (fun src => Ast.Expr.ifThenElse
        (.intEq (.textLen (.var (fieldName src))) (.intLit 0))
        (.intLit 0) (.intLit 1))).foldl Ast.Expr.intAdd acc).evaluate
        canonicalCalls targetEnv =
      some (.int (accValue +
        Int.ofNat (presentCount (sources.map fun f => (sourceEnv f).getD "")))) := by
  induction sources generalizing acc accValue with
  | nil => simpa [presentCount] using hacc
  | cons source rest ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [presentCount_cons]
      have hstep :
          (Ast.Expr.intAdd acc
            (Ast.Expr.ifThenElse
              (.intEq (.textLen (.var (fieldName source))) (.intLit 0))
              (.intLit 0) (.intLit 1))).evaluate canonicalCalls targetEnv =
            some (.int (accValue +
              if (sourceEnv source).getD "" = "" then 0 else 1)) := by
        simp [Ast.Expr.evaluate, hacc,
          evaluate_presence sourceEnv fieldName targetEnv hagrees source]
      rw [ih _ _ hstep]
      congr 2
      by_cases hs : (sourceEnv source).getD "" = "" <;> simp [hs] <;> omega

private theorem evaluate_presence_total (sourceEnv : Env) (fieldName : FieldName)
    (targetEnv : Ast.EvalEnv) (hagrees : AstEnvAgrees sourceEnv fieldName targetEnv)
    (sources : List String) :
    (Ast.Expr.intSum (sources.map (fun src => Ast.Expr.ifThenElse
        (.intEq (.textLen (.var (fieldName src))) (.intLit 0))
        (.intLit 0) (.intLit 1)))).evaluate canonicalCalls targetEnv =
      some (.int
        (Int.ofNat (presentCount (sources.map fun f => (sourceEnv f).getD "")))) := by
  cases sources with
  | nil => simp [Ast.Expr.intSum, Ast.Expr.evaluate, presentCount]
  | cons source rest =>
      simp only [List.map_cons, Ast.Expr.intSum]
      rw [evaluate_presence_foldl sourceEnv fieldName targetEnv hagrees rest _ _
        (evaluate_presence sourceEnv fieldName targetEnv hagrees source)]
      rw [presentCount_cons]
      congr 2
      by_cases hs : (sourceEnv source).getD "" = "" <;> simp [hs] <;> omega

@[simp]
theorem lower_translateConstraint_preserves (sourceEnv : Env)
    (fieldName : FieldName) (targetEnv : Ast.EvalEnv) (constraint : Constraint)
    (hpresent : ConstraintStringCapturesPresent sourceEnv constraint)
    (hagrees : AstEnvAgrees sourceEnv fieldName targetEnv) :
    (lowerExpr (translateConstraint fieldName constraint)).evaluate canonicalCalls targetEnv =
      some (.bool (decide (constraint.eval sourceEnv))) := by
  induction constraint with
  | «noLeadingZero» source =>
      by_cases hempty : (sourceEnv source).getD "" = ""
      · simp [translateConstraint, lowerExpr, captureExpr, Ast.Expr.evaluate,
          hagrees source, hempty, Constraint.eval]
      · by_cases hself : (sourceEnv source).getD "" = "0"
        · simp [translateConstraint, lowerExpr, captureExpr, Ast.Expr.evaluate,
            hagrees source, hself, Constraint.eval, Ast.encodeString]
        · obtain ⟨c, cs, hlist⟩ : ∃ c cs, ((sourceEnv source).getD "").toList = c :: cs := by
            cases hchars : ((sourceEnv source).getD "").toList with
            | nil => exact absurd (string_eq_of_toList_eq (by simp [hchars])) hempty
            | cons c cs => exact ⟨c, cs, rfl⟩
          have hlen : ((sourceEnv source).getD "").length ≠ 0 := by
            rw [← String.length_toList, hlist]
            simp
          by_cases hzero : c = '0'
          · have hcs : cs ≠ [] := by
              intro h
              exact hself (string_eq_of_toList_eq (by simp [hlist, h, hzero]))
            simp [translateConstraint, lowerExpr, captureExpr, Ast.Expr.evaluate,
              hagrees source, Constraint.eval, Ast.encodeString, hlist, hzero, hself,
              hcs, String.startsWith_string_iff]
            omega
          · have hcode : c.toNat ≠ 48 := fun h => hzero (Char.toNat_inj.mp h)
            have hzero' : ¬('0' = c) := fun h => hzero h.symm
            simp [translateConstraint, lowerExpr, captureExpr, Ast.Expr.evaluate,
              hagrees source, Constraint.eval, Ast.encodeString, hlist, hcode,
              hzero', hself, String.startsWith_string_iff]
  | strEq source literal =>
      obtain ⟨str, hstr⟩ := Option.isSome_iff_exists.mp hpresent
      simp [translateConstraint, lowerExpr, captureExpr, Ast.Expr.evaluate,
        hagrees source, hstr, Constraint.eval,
        show Ast.encodeString str = Ast.encodeString literal ↔ str = literal from
          encodeString_inj_iff str literal]
  | card operation k sources =>
      have htotal :=
        evaluate_presence_total sourceEnv fieldName targetEnv hagrees sources
      cases operation <;>
        simp [translateConstraint, lowerExpr, captureExpr, Ast.Expr.evaluate,
          Constraint.eval, List.map_map, Function.comp_def, htotal] <;>
        exact decide_eq_decide.mpr (by omega)
  | le left right =>
      simp [translateConstraint, lowerExpr, Ast.Expr.evaluate, Constraint.eval,
        lower_translateValExpr_preserves sourceEnv fieldName targetEnv left hagrees,
        lower_translateValExpr_preserves sourceEnv fieldName targetEnv right hagrees]
      exact decide_eq_decide.mpr Iff.rfl
  | lt left right =>
      simp [translateConstraint, lowerExpr, Ast.Expr.evaluate, Constraint.eval,
        lower_translateValExpr_preserves sourceEnv fieldName targetEnv left hagrees,
        lower_translateValExpr_preserves sourceEnv fieldName targetEnv right hagrees]
      exact decide_eq_decide.mpr Iff.rfl
  | eq left right =>
      simp [translateConstraint, lowerExpr, Ast.Expr.evaluate, Constraint.eval,
        lower_translateValExpr_preserves sourceEnv fieldName targetEnv left hagrees,
        lower_translateValExpr_preserves sourceEnv fieldName targetEnv right hagrees]
      exact decide_eq_decide.mpr Iff.rfl
  | «and» left right left_ih right_ih =>
      obtain ⟨hleft, hright⟩ := hpresent
      simp [translateConstraint, lowerExpr, Ast.Expr.evaluate, Constraint.eval,
        left_ih hleft, right_ih hright]
      exact (Bool.decide_and (Constraint.eval sourceEnv left)
        (Constraint.eval sourceEnv right)).symm

end Triptych.Backend.Verus
