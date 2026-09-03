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

import Triptych.Backend.Verus.Semantic

/-!
# Denotation of the Verus semantic AST

These functions assign Lean meanings to the semantic AST nodes produced from `ValExpr` and
`Constraint`. They deliberately cover the semantic expression subset, not arbitrary generated
functions, quantifiers, or target-language control flow.

The pretty-printer remains a separate boundary: these definitions specify what a semantic AST node
is intended to mean before Verus surface syntax is emitted.
-/

namespace Triptych.Backend.Verus

open Semantic

/-- The string value represented by the Verus semantic AST subset. -/
def Semantic.Expr.denoteText (env : Env) : Semantic.Expr → Option String
  | .capture _ source => some ((env source).getD "")
  | .textLit literal => some literal
  | .textConcat left right => return (← left.denoteText env) ++ (← right.denoteText env)
  | _ => none

/-- The integer value represented by the Verus semantic AST subset. -/
def Semantic.Expr.denoteInt (env : Env) : Semantic.Expr → Option Int
  | .intLit literal => some literal
  | .valueRef _ source _ => some (source.eval env)
  | .intAdd left right => return (← left.denoteInt env) + (← right.denoteInt env)
  | .intSub left right => return (← left.denoteInt env) - (← right.denoteInt env)
  | .intMul left right => return (← left.denoteInt env) * (← right.denoteInt env)
  | .intNeg expression => return -(← expression.denoteInt env)
  | .intPow base exponent =>
      return (← base.denoteInt env) ^ (← exponent.denoteInt env).toNat
  | .textLen expression => return Triptych.lenOf (← expression.denoteText env)
  | .natOf expression => return Triptych.natOf (← expression.denoteText env)
  | .intOf expression => return Triptych.intOf (← expression.denoteText env)
  | .signOf expression => return Triptych.signOf (← expression.denoteText env)
  | .countOf _ expression => return Triptych.countOf (← expression.denoteText env)
  | _ => none

/-- The proposition represented by the semantic Verus AST subset. -/
def Semantic.Expr.denoteProp (env : Env) : Semantic.Expr → Option Prop
  | .boolLit literal => some (literal = true)
  | .boolAnd left right => return (← left.denoteProp env) ∧ (← right.denoteProp env)
  | .boolOr left right => return (← left.denoteProp env) ∨ (← right.denoteProp env)
  | .boolImplies left right => return (← left.denoteProp env) → (← right.denoteProp env)
  | .intEq left right => return (← left.denoteInt env) = (← right.denoteInt env)
  | .intNe left right => return (← left.denoteInt env) ≠ (← right.denoteInt env)
  | .intLt left right => return (← left.denoteInt env) < (← right.denoteInt env)
  | .intLe left right => return (← left.denoteInt env) ≤ (← right.denoteInt env)
  | .intGt left right => return (← left.denoteInt env) > (← right.denoteInt env)
  | .intGe left right => return (← left.denoteInt env) ≥ (← right.denoteInt env)
  | .textEq left right => return (← left.denoteText env) = (← right.denoteText env)
  | .textNe left right => return (← left.denoteText env) ≠ (← right.denoteText env)
  | .noLeadingZero expression => do
      let text ← expression.denoteText env
      pure (text.startsWith "0" = true → text = "0")
  | .card operation k expressions => do
      let texts ← expressions.mapM (Semantic.Expr.denoteText env)
      let present := presentCount texts
      pure <| match operation with
        | .atLeast => k ≤ present
        | .atMost => present ≤ k
        | .exactlyK => present = k
  | _ => none

/-- Every capture used by a string-equality constraint is present. Verus views currently
    represent scalar fields as byte sequences rather than options, so this condition is required
    to preserve `Constraint.strEq`'s vacuous truth for an absent capture. Other constraint forms
    already interpret absence through the same empty-string or zero defaults as Triptych. -/
def ConstraintStringCapturesPresent (env : Env) : Constraint → Prop
  | .strEq capture _ => (env capture).isSome
  | .and left right =>
      ConstraintStringCapturesPresent env left ∧ ConstraintStringCapturesPresent env right
  | _ => True

@[simp]
theorem natOf_capture (env : Env) (source : String) :
    Triptych.natOf ((env source).getD "") = env.natVal source := by
  cases h : env source <;>
    simp [Env.natVal, Triptych.natOf, readNat, h]

@[simp]
theorem intOf_capture (env : Env) (source : String) :
    Triptych.intOf ((env source).getD "") = env.intVal source := by
  cases h : env source with
  | none => simp [Env.intVal, Triptych.intOf, h]
  | some text =>
      by_cases hempty : text = ""
      · subst text
        simp [Env.intVal, Triptych.intOf, readInt, h]
      · simp [Env.intVal, Triptych.intOf, hempty, h]

@[simp]
theorem lenOf_capture (env : Env) (source : String) :
    Triptych.lenOf ((env source).getD "") = env.lenVal source := by
  cases h : env source <;> simp [Env.lenVal, Triptych.lenOf, h]

@[simp]
theorem signOf_capture (env : Env) (source : String) :
    Triptych.signOf ((env source).getD "") = env.signVal source := by
  cases h : env source <;> simp [Env.signVal, Triptych.signOf, h]

@[simp]
theorem countOf_capture (env : Env) (source : String) :
    Triptych.countOf ((env (source ++ "#count")).getD "") = env.countVal source := by
  cases h : env (source ++ "#count") <;>
    simp [Env.countVal, Env.natVal, Triptych.countOf, readNat, h]

end Triptych.Backend.Verus
