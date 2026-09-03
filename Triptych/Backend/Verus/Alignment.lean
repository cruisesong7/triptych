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

import Triptych.Backend.Verus.SurfaceSemantics
import Triptych.Backend.Verus.Translation

/-!
# End-to-end alignment of translated expressions

These theorems compose source translation, semantic-node desugaring, and the Surface AST
evaluator. They use `canonicalCalls`, whose generated helper bodies are validated separately by
`helperDeclaration_realizes`.
-/

namespace Triptych.Backend.Verus

def ValueSupported : ValExpr → Prop
  | .count _ => False
  | .add left right
  | .sub left right
  | .mul left right
  | .pow left right => ValueSupported left ∧ ValueSupported right
  | .neg expression => ValueSupported expression
  | _ => True

def ArithmeticConstraintSupported : Constraint → Prop
  | .le left right
  | .lt left right
  | .eq left right => ValueSupported left ∧ ValueSupported right
  | .and left right =>
      ArithmeticConstraintSupported left ∧ ArithmeticConstraintSupported right
  | _ => False

def SurfaceEnvAgrees (sourceEnv : Env) (fieldName : FieldName)
    (targetEnv : Surface.EvalEnv) : Prop :=
  ∀ source, targetEnv (fieldName source) =
    some (.text (Surface.encodeString ((sourceEnv source).getD "")))

@[simp]
theorem denote_desugar_translateValExpr (sourceEnv : Env) (fieldName : FieldName)
    (targetEnv : Surface.EvalEnv) (expression : ValExpr)
    (hsupported : ValueSupported expression)
    (hagrees : SurfaceEnvAgrees sourceEnv fieldName targetEnv) :
    (desugarExpr (translateValExpr fieldName expression)).denote canonicalCalls targetEnv =
      some (.int (expression.eval sourceEnv)) := by
  induction expression with
  | lit literal =>
      simp [translateValExpr, desugarExpr, Surface.Expr.denote, ValExpr.eval]
  | «nat» source =>
      simp [translateValExpr, desugarExpr, captureExpr, Surface.Expr.denote, hagrees source,
        ValExpr.eval]
  | «int» source =>
      simp [translateValExpr, desugarExpr, captureExpr, Surface.Expr.denote, hagrees source,
        ValExpr.eval]
  | «len» source =>
      simp [translateValExpr, desugarExpr, captureExpr, Surface.Expr.denote, hagrees source,
        ValExpr.eval, Surface.encodeString]
      rw [String.length_toList]
      exact lenOf_capture sourceEnv source
  | «count» source =>
      simp [ValueSupported] at hsupported
  | signOf source =>
      simp [translateValExpr, desugarExpr, captureExpr, Surface.Expr.denote, hagrees source,
        ValExpr.eval]
  | add left right left_ih right_ih =>
      simp [ValueSupported] at hsupported
      simp [translateValExpr, desugarExpr, Surface.Expr.denote, ValExpr.eval,
        left_ih hsupported.1, right_ih hsupported.2]
  | sub left right left_ih right_ih =>
      simp [ValueSupported] at hsupported
      simp [translateValExpr, desugarExpr, Surface.Expr.denote, ValExpr.eval,
        left_ih hsupported.1, right_ih hsupported.2]
  | mul left right left_ih right_ih =>
      simp [ValueSupported] at hsupported
      simp [translateValExpr, desugarExpr, Surface.Expr.denote, ValExpr.eval,
        left_ih hsupported.1, right_ih hsupported.2]
  | pow base exponent base_ih exponent_ih =>
      simp [ValueSupported] at hsupported
      simp [translateValExpr, desugarExpr, Surface.Expr.denote, ValExpr.eval,
        base_ih hsupported.1, exponent_ih hsupported.2, intPowModel]
  | neg expression expression_ih =>
      simp [ValueSupported] at hsupported
      simp [translateValExpr, desugarExpr, Surface.Expr.denote, ValExpr.eval,
        expression_ih hsupported]

@[simp]
theorem denote_desugar_translateArithmeticConstraint (sourceEnv : Env)
    (fieldName : FieldName) (targetEnv : Surface.EvalEnv) (constraint : Constraint)
    (hsupported : ArithmeticConstraintSupported constraint)
    (hagrees : SurfaceEnvAgrees sourceEnv fieldName targetEnv) :
    (desugarExpr (translateConstraint fieldName constraint)).denote canonicalCalls targetEnv =
      some (.bool (decide (constraint.eval sourceEnv))) := by
  induction constraint with
  | «noLeadingZero» source =>
      simp [ArithmeticConstraintSupported] at hsupported
  | strEq source literal =>
      simp [ArithmeticConstraintSupported] at hsupported
  | card operation k sources =>
      simp [ArithmeticConstraintSupported] at hsupported
  | le left right =>
      simp [ArithmeticConstraintSupported] at hsupported
      simp [translateConstraint, desugarExpr, Surface.Expr.denote, Constraint.eval,
        denote_desugar_translateValExpr sourceEnv fieldName targetEnv left hsupported.1 hagrees,
        denote_desugar_translateValExpr sourceEnv fieldName targetEnv right hsupported.2 hagrees]
      exact decide_eq_decide.mpr Iff.rfl
  | lt left right =>
      simp [ArithmeticConstraintSupported] at hsupported
      simp [translateConstraint, desugarExpr, Surface.Expr.denote, Constraint.eval,
        denote_desugar_translateValExpr sourceEnv fieldName targetEnv left hsupported.1 hagrees,
        denote_desugar_translateValExpr sourceEnv fieldName targetEnv right hsupported.2 hagrees]
      exact decide_eq_decide.mpr Iff.rfl
  | eq left right =>
      simp [ArithmeticConstraintSupported] at hsupported
      simp [translateConstraint, desugarExpr, Surface.Expr.denote, Constraint.eval,
        denote_desugar_translateValExpr sourceEnv fieldName targetEnv left hsupported.1 hagrees,
        denote_desugar_translateValExpr sourceEnv fieldName targetEnv right hsupported.2 hagrees]
      exact decide_eq_decide.mpr Iff.rfl
  | «and» left right left_ih right_ih =>
      simp [ArithmeticConstraintSupported] at hsupported
      simp [translateConstraint, desugarExpr, Surface.Expr.denote, Constraint.eval,
        left_ih hsupported.1, right_ih hsupported.2]
      exact (Bool.decide_and (Constraint.eval sourceEnv left)
        (Constraint.eval sourceEnv right)).symm

end Triptych.Backend.Verus
