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

import Triptych.Backend.Verus.SemanticSemantics

/-!
# Triptych-to-Verus translation

This module translates Triptych values and constraints into the Verus AST while retaining capture
provenance. The left-inverse theorems ensure that translation neither drops nor changes a
supported source node.

Semantic-preservation theorems are stated against the Lean denotation of `Verus.Semantic`.
-/

namespace Triptych.Backend.Verus

open Semantic

abbrev FieldName := String → String

def captureExpr (fieldName : FieldName) (source : String) : Semantic.Expr :=
  .capture (fieldName source) source

@[simp]
private theorem captureSource_capture (fieldName : FieldName) (source : String) :
    (captureExpr fieldName source).captureSource? = some source := rfl

@[simp]
private theorem captureSources_map (fieldName : FieldName) (sources : List String) :
    (sources.map (captureExpr fieldName)).mapM Semantic.Expr.captureSource? = some sources := by
  induction sources <;> simp_all

@[simp]
private theorem captureSources_mapM (fieldName : FieldName) (sources : List String) :
    sources.mapM (Semantic.Expr.captureSource? ∘ captureExpr fieldName) = some sources := by
  induction sources <;> simp_all [Function.comp]

@[simp]
private theorem denoteTexts_capture (env : Env) (fieldName : FieldName)
    (sources : List String) :
    (sources.map (captureExpr fieldName)).mapM (Semantic.Expr.denoteText env) =
      some (sources.map fun source => (env source).getD "") := by
  induction sources <;> simp_all [captureExpr, Semantic.Expr.denoteText]

@[simp]
private theorem denoteTexts_capture_mapM (env : Env) (fieldName : FieldName)
    (sources : List String) :
    sources.mapM (Semantic.Expr.denoteText env ∘ captureExpr fieldName) =
      some (sources.map fun source => (env source).getD "") := by
  induction sources <;> simp_all [captureExpr, Semantic.Expr.denoteText, Function.comp]

/-- Translate a Triptych value into the Verus AST without target-level abbreviation. -/
def translateValExpr (fieldName : FieldName) : ValExpr → Semantic.Expr
  | .lit literal => .intLit literal
  | .nat source => .natOf (captureExpr fieldName source)
  | .int source => .intOf (captureExpr fieldName source)
  | .len source => .textLen (captureExpr fieldName source)
  | .count source => .countOf source (captureExpr fieldName (source ++ "#count"))
  | .signOf source => .signOf (captureExpr fieldName source)
  | .add left right => .intAdd (translateValExpr fieldName left) (translateValExpr fieldName right)
  | .sub left right => .intSub (translateValExpr fieldName left) (translateValExpr fieldName right)
  | .mul left right => .intMul (translateValExpr fieldName left) (translateValExpr fieldName right)
  | .pow base exponent => .intPow (translateValExpr fieldName base) (translateValExpr fieldName exponent)
  | .neg expression => .intNeg (translateValExpr fieldName expression)

private def namedOr (source expression : ValExpr) (name : String) (args : List Semantic.Expr)
    (otherwise : Semantic.Expr) : Semantic.Expr :=
  if expression = source then .valueRef name source args else otherwise

/-- Translate a value while retaining the conventional name for the complete format value. -/
def translateValExprNamed (fieldName : FieldName) (source : ValExpr) (name : String)
    (args : List Semantic.Expr) : ValExpr → Semantic.Expr
  | expression@(.lit literal) =>
      namedOr source expression name args (.intLit literal)
  | expression@(.nat captureName) =>
      namedOr source expression name args (.natOf (captureExpr fieldName captureName))
  | expression@(.int captureName) =>
      namedOr source expression name args (.intOf (captureExpr fieldName captureName))
  | expression@(.len captureName) =>
      namedOr source expression name args (.textLen (captureExpr fieldName captureName))
  | expression@(.count captureName) =>
      namedOr source expression name args
        (.countOf captureName (captureExpr fieldName (captureName ++ "#count")))
  | expression@(.signOf captureName) =>
      namedOr source expression name args (.signOf (captureExpr fieldName captureName))
  | expression@(.add left right) =>
      namedOr source expression name args
        (.intAdd
          (translateValExprNamed fieldName source name args left)
          (translateValExprNamed fieldName source name args right))
  | expression@(.sub left right) =>
      namedOr source expression name args
        (.intSub
          (translateValExprNamed fieldName source name args left)
          (translateValExprNamed fieldName source name args right))
  | expression@(.mul left right) =>
      namedOr source expression name args
        (.intMul
          (translateValExprNamed fieldName source name args left)
          (translateValExprNamed fieldName source name args right))
  | expression@(.pow base exponent) =>
      namedOr source expression name args
        (.intPow
          (translateValExprNamed fieldName source name args base)
          (translateValExprNamed fieldName source name args exponent))
  | expression@(.neg operand) =>
      namedOr source expression name args
        (.intNeg (translateValExprNamed fieldName source name args operand))

/-- Translate a Triptych constraint into the Verus AST. -/
def translateConstraint (fieldName : FieldName) : Constraint → Semantic.Expr
  | .noLeadingZero source => .noLeadingZero (captureExpr fieldName source)
  | .strEq source literal => .textEq (captureExpr fieldName source) (.textLit literal)
  | .card operation k sources => .card operation k (sources.map (captureExpr fieldName))
  | .le left right => .intLe (translateValExpr fieldName left) (translateValExpr fieldName right)
  | .lt left right => .intLt (translateValExpr fieldName left) (translateValExpr fieldName right)
  | .eq left right => .intEq (translateValExpr fieldName left) (translateValExpr fieldName right)
  | .and left right => .boolAnd (translateConstraint fieldName left)
      (translateConstraint fieldName right)

/-- Name occurrences of the complete format value inside a translated constraint. -/
def translateConstraintNamed (fieldName : FieldName) (source : ValExpr) (name : String)
    (args : List Semantic.Expr) : Constraint → Semantic.Expr
  | .noLeadingZero captureName => .noLeadingZero (captureExpr fieldName captureName)
  | .strEq captureName literal => .textEq (captureExpr fieldName captureName) (.textLit literal)
  | .card operation k captures => .card operation k (captures.map (captureExpr fieldName))
  | .le left right =>
      .intLe (translateValExprNamed fieldName source name args left)
        (translateValExprNamed fieldName source name args right)
  | .lt left right =>
      .intLt (translateValExprNamed fieldName source name args left)
        (translateValExprNamed fieldName source name args right)
  | .eq left right =>
      .intEq (translateValExprNamed fieldName source name args left)
        (translateValExprNamed fieldName source name args right)
  | .and left right =>
      .boolAnd (translateConstraintNamed fieldName source name args left)
        (translateConstraintNamed fieldName source name args right)

@[simp]
theorem recover_translateValExpr (fieldName : FieldName) (expression : ValExpr) :
    (translateValExpr fieldName expression).toValExpr? = some expression := by
  induction expression <;> simp [translateValExpr, Semantic.Expr.toValExpr?, *]

@[simp]
theorem recover_translateValExprNamed (fieldName : FieldName) (source expression : ValExpr)
    (name : String) (args : List Semantic.Expr) :
    (translateValExprNamed fieldName source name args expression).toValExpr? = some expression := by
  induction expression <;> simp only [translateValExprNamed, namedOr]
  all_goals
    split <;> rename_i h <;> simp_all [Semantic.Expr.toValExpr?]

@[simp]
theorem recover_translateConstraint (fieldName : FieldName) (constraint : Constraint) :
    (translateConstraint fieldName constraint).toConstraint? = some constraint := by
  induction constraint <;>
    simp [translateConstraint, Semantic.Expr.toConstraint?, recover_translateValExpr, *]

@[simp]
theorem recover_translateConstraintNamed (fieldName : FieldName) (source : ValExpr)
    (name : String) (args : List Semantic.Expr) (constraint : Constraint) :
    (translateConstraintNamed fieldName source name args constraint).toConstraint? =
      some constraint := by
  induction constraint <;>
    simp [translateConstraintNamed, Semantic.Expr.toConstraint?, recover_translateValExprNamed, *]

@[simp]
theorem denoteInt_translateValExpr (env : Env) (fieldName : FieldName) (expression : ValExpr) :
    (translateValExpr fieldName expression).denoteInt env = some (expression.eval env) := by
  induction expression <;>
    simp [translateValExpr, captureExpr, Semantic.Expr.denoteInt, Semantic.Expr.denoteText,
      ValExpr.eval, *]

@[simp]
theorem denoteInt_translateValExprNamed (env : Env) (fieldName : FieldName)
    (source expression : ValExpr) (name : String) (args : List Semantic.Expr) :
    (translateValExprNamed fieldName source name args expression).denoteInt env =
      some (expression.eval env) := by
  induction expression <;> simp only [translateValExprNamed, namedOr]
  all_goals
    split <;> rename_i h
    · subst source
      simp [Semantic.Expr.denoteInt, ValExpr.eval]
    · simp_all [captureExpr, Semantic.Expr.denoteInt, Semantic.Expr.denoteText, ValExpr.eval]

@[simp]
theorem denoteProp_translateConstraint (env : Env) (fieldName : FieldName)
    (constraint : Constraint) (hpresent : ConstraintStringCapturesPresent env constraint) :
    (translateConstraint fieldName constraint).denoteProp env =
      some (constraint.eval env) := by
  induction constraint with
  | «noLeadingZero» field =>
      simp [translateConstraint, captureExpr, Semantic.Expr.denoteProp, Semantic.Expr.denoteText,
        Constraint.eval]
  | strEq field literal =>
      cases hfield : env field <;>
        simp_all [ConstraintStringCapturesPresent, translateConstraint, captureExpr,
          Semantic.Expr.denoteProp, Semantic.Expr.denoteText, Constraint.eval]
  | card operation k fields =>
      simp [translateConstraint, Semantic.Expr.denoteProp, Constraint.eval]
      exact Iff.rfl
  | le left right =>
      simp [translateConstraint, Semantic.Expr.denoteProp, Constraint.eval]
  | lt left right =>
      simp [translateConstraint, Semantic.Expr.denoteProp, Constraint.eval]
  | eq left right =>
      simp [translateConstraint, Semantic.Expr.denoteProp, Constraint.eval]
  | and left right left_ih right_ih =>
      simp [translateConstraint, Semantic.Expr.denoteProp, Constraint.eval,
        ConstraintStringCapturesPresent] at hpresent ⊢
      rw [left_ih hpresent.1, right_ih hpresent.2]
      rfl

@[simp]
theorem denoteProp_translateConstraintNamed (env : Env) (fieldName : FieldName)
    (source : ValExpr) (name : String) (args : List Semantic.Expr)
    (constraint : Constraint) (hpresent : ConstraintStringCapturesPresent env constraint) :
    (translateConstraintNamed fieldName source name args constraint).denoteProp env =
      some (constraint.eval env) := by
  induction constraint with
  | «noLeadingZero» field =>
      simp [translateConstraintNamed, captureExpr, Semantic.Expr.denoteProp, Semantic.Expr.denoteText,
        Constraint.eval]
  | strEq field literal =>
      cases hfield : env field <;>
        simp_all [ConstraintStringCapturesPresent, translateConstraintNamed, captureExpr,
          Semantic.Expr.denoteProp, Semantic.Expr.denoteText, Constraint.eval]
  | card operation k fields =>
      simp [translateConstraintNamed, Semantic.Expr.denoteProp, Constraint.eval]
      exact Iff.rfl
  | le left right =>
      simp [translateConstraintNamed, Semantic.Expr.denoteProp, Constraint.eval]
  | lt left right =>
      simp [translateConstraintNamed, Semantic.Expr.denoteProp, Constraint.eval]
  | eq left right =>
      simp [translateConstraintNamed, Semantic.Expr.denoteProp, Constraint.eval]
  | and left right left_ih right_ih =>
      simp [translateConstraintNamed, Semantic.Expr.denoteProp, Constraint.eval,
        ConstraintStringCapturesPresent] at hpresent ⊢
      rw [left_ih hpresent.1, right_ih hpresent.2]
      rfl

end Triptych.Backend.Verus
