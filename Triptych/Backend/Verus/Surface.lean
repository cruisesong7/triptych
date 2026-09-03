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
# Verus surface AST

Unlike `Verus.Semantic`, this type contains only constructs that correspond directly to emitted
Verus syntax. Triptych-specific semantic operations are eliminated before values enter this layer.
-/

namespace Triptych.Backend.Verus.Surface

abbrev Ty := Semantic.Ty
abbrev Binder := Semantic.Binder
abbrev FunctionMode := Semantic.FunctionMode
abbrev Param := Semantic.Param
abbrev FieldDecl := Semantic.FieldDecl
abbrev StructDecl := Semantic.StructDecl

inductive Expr where
  | var (name : String)
  | boolLit (literal : Bool)
  | intLit (literal : Int)
  | byteLit (literal : Nat)
  | textLit (literal : String)
  | optionNone
  | optionSome (expression : Expr)
  | call (name : String) (args : List Expr)
  | field (base : Expr) (name : String)
  | textConcat (left right : Expr)
  | intAdd (left right : Expr)
  | intSub (left right : Expr)
  | intMul (left right : Expr)
  | intNeg (expression : Expr)
  | textLen (expression : Expr)
  | textIndex (expression index : Expr)
  | textSubrange (expression start stop : Expr)
  | byteToInt (expression : Expr)
  | boolNot (expression : Expr)
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

end Expr

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

structure ConstDecl where
  name : String
  ty : Ty
  initializer : Expr
  isPublic : Bool := true

structure TraitSpecMethod where
  name : String
  params : List Param
  returnType : Ty
  doc : Option String := none

structure TraitProofMethod where
  name : String
  params : List Param
  requires : List Expr := []
  ensures : List Expr := []
  doc : Option String := none

inductive TraitItem where
  | specMethod (method : TraitSpecMethod)
  | proofMethod (method : TraitProofMethod)

structure TraitDecl where
  name : String
  items : List TraitItem
  isPublic : Bool := true
  doc : Option String := none

inductive Decl where
  | function (decl : FunctionDecl)
  | structure (decl : StructDecl)
  | constant (decl : ConstDecl)
  | trait (decl : TraitDecl)

structure Module where
  header : List String := []
  imports : List String := []
  declarations : List Decl := []

end Triptych.Backend.Verus.Surface
