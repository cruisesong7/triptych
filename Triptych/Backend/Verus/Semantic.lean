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

import Triptych.Architecture.Constraint
import Triptych.Architecture.Grammar

/-!
# Semantic Verus specification AST

This is the backend's semantic Verus specification AST. It contains functions, quantifiers, text
values, options, and explicit semantic operations such as `natOf`. `Verus.Desugar` later
eliminates those operations into the `Verus.Surface` AST.
There is no raw Verus source escape.

`capture` retains both the printed target identifier and the originating Triptych capture. That
metadata is erased by the pretty-printer but lets Lean check that value and constraint translation
is lossless.
-/

namespace Triptych.Backend.Verus.Semantic

inductive Ty where
  | bool
  | int
  | byte
  | text
  | option (inner : Ty)
  | named (name : String)
  deriving Repr, Inhabited, DecidableEq

structure Binder where
  name : String
  ty : Ty
  deriving Repr, Inhabited, DecidableEq

/-- Expressions in the generated pure-Verus subset. Domain operations such as `natOf` and `card`
    remain explicit nodes so their intended semantics and concrete pretty-printing can be reviewed
    independently. -/
inductive Expr where
  | var (name : String)
  | capture (ident source : String)
  | boolLit (literal : Bool)
  | intLit (literal : Int)
  | byteLit (literal : Nat)
  | textLit (literal : String)
  | optionNone
  | optionSome (expression : Expr)
  | call (name : String) (args : List Expr)
  | valueRef (name : String) (source : Triptych.ValExpr) (args : List Expr)
  | field (base : Expr) (name : String)
  | textConcat (left right : Expr)
  | intAdd (left right : Expr)
  | intSub (left right : Expr)
  | intMul (left right : Expr)
  | intNeg (expression : Expr)
  | intPow (base exponent : Expr)
  | textLen (expression : Expr)
  | textIndex (expression index : Expr)
  | textSubrange (expression start stop : Expr)
  | byteToInt (expression : Expr)
  | boolAnd (left right : Expr)
  | boolOr (left right : Expr)
  | boolImplies (left right : Expr)
  | intEq (left right : Expr)
  | intNe (left right : Expr)
  | intLt (left right : Expr)
  | intLe (left right : Expr)
  | intGt (left right : Expr)
  | intGe (left right : Expr)
  | byteEq (left right : Expr)
  | byteNe (left right : Expr)
  | textEq (left right : Expr)
  | textNe (left right : Expr)
  | ifThenElse (condition thenBranch elseBranch : Expr)
  | forallE (binders : List Binder) (autoTrigger : Bool) (body : Expr)
  | existsE (binders : List Binder) (body : Expr)
  | choose (binder : Binder) (body : Expr)
  | matchOption (scrutinee : Expr) (binder : Binder) (someBranch noneBranch : Expr)
  | isToken (token : Triptych.TokClass) (expression : Expr)
  | natOf (expression : Expr)
  | intOf (expression : Expr)
  | signOf (expression : Expr)
  | countOf (source : String) (expression : Expr)
  | noLeadingZero (expression : Expr)
  | card (operation : Triptych.CardOp) (k : Nat) (expressions : List Expr)

namespace Expr

def andAll : List Expr → Expr
  | [] => .boolLit true
  | first :: rest => rest.foldl .boolAnd first

def orAll : List Expr → Expr
  | [] => .boolLit false
  | first :: rest => rest.foldl .boolOr first

def concatAll : List Expr → Expr
  | [] => .textLit ""
  | first :: rest => rest.foldl .textConcat first

def intSum : List Expr → Expr
  | [] => .intLit 0
  | first :: rest => rest.foldl .intAdd first

/-- Recover the originating Triptych capture from a target identifier. -/
def captureSource? : Expr → Option String
  | .capture _ source => some source
  | _ => none

/-- Recover the source value AST represented by the translated Verus expression subset. -/
def toValExpr? : Expr → Option Triptych.ValExpr
  | .intLit literal => Option.some (.lit literal)
  | .natOf expression => return .nat (← expression.captureSource?)
  | .intOf expression => return .int (← expression.captureSource?)
  | .textLen expression => return .len (← expression.captureSource?)
  | .countOf source _ => Option.some (.count source)
  | .signOf expression => return .signOf (← expression.captureSource?)
  | .intAdd left right => return .add (← left.toValExpr?) (← right.toValExpr?)
  | .intSub left right => return .sub (← left.toValExpr?) (← right.toValExpr?)
  | .intMul left right => return .mul (← left.toValExpr?) (← right.toValExpr?)
  | .intPow base exponent => return .pow (← base.toValExpr?) (← exponent.toValExpr?)
  | .intNeg expression => return .neg (← expression.toValExpr?)
  | .valueRef _ source _ => Option.some source
  | _ => Option.none

/-- Recover a source constraint represented by the translated Verus expression subset. -/
def toConstraint? : Expr → Option Triptych.Constraint
  | .noLeadingZero expression => return .noLeadingZero (← expression.captureSource?)
  | .textEq expression (.textLit literal) =>
      return .strEq (← expression.captureSource?) literal
  | .card operation k expressions =>
      return .card operation k (← expressions.mapM captureSource?)
  | .intLe left right => return .le (← left.toValExpr?) (← right.toValExpr?)
  | .intLt left right => return .lt (← left.toValExpr?) (← right.toValExpr?)
  | .intEq left right => return .eq (← left.toValExpr?) (← right.toValExpr?)
  | .boolAnd left right => return .and (← left.toConstraint?) (← right.toConstraint?)
  | _ => Option.none

end Expr

inductive FunctionMode where
  | spec
  | executable
  | proof
  deriving Repr, Inhabited, DecidableEq

structure Param where
  name : String
  ty : Ty
  deriving Repr, Inhabited, DecidableEq

structure FunctionDecl where
  name : String
  params : List Param
  returnType : Ty
  body : Expr
  mode : FunctionMode := .spec
  isPublic : Bool := true
  isOpen : Bool := true
  recommends : List Expr := []
  decreases : Option Expr := none
  doc : Option String := none

structure FieldDecl where
  name : String
  ty : Ty
  isPublic : Bool := true
  deriving Repr, Inhabited, DecidableEq

structure StructDecl where
  name : String
  fields : List FieldDecl
  isPublic : Bool := true

structure ConstDecl where
  name : String
  ty : Ty
  initializer : Expr
  isPublic : Bool := true

inductive Decl where
  | function (decl : FunctionDecl)
  | structure (decl : StructDecl)
  | constant (decl : ConstDecl)

structure Module where
  header : List String := []
  imports : List String := []
  declarations : List Decl := []

end Triptych.Backend.Verus.Semantic
