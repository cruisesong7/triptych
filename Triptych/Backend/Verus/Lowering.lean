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

import Triptych.Backend.Verus.Ast

/-!
# Verus IR lowering

This phase eliminates every Triptych-specific expression from `Verus.IR`, selects the
required runtime helpers, and produces `Verus.Ast`, which contains only constructs that map
directly to Verus syntax.
-/

namespace Triptych.Backend.Verus

inductive Helper where
  | minusConstant
  | zeroConstant
  | isDigit
  | isHexDigit
  | isBit
  | natOfFrom
  | natOf
  | countOf
  | intOf
  | signOf
  | intPow
  deriving Repr, Inhabited, DecidableEq, BEq

def helperOrder : List Helper :=
  [.minusConstant, .zeroConstant, .isDigit, .isHexDigit, .isBit,
   .natOfFrom, .natOf, .countOf, .intOf, .signOf, .intPow]

def Helper.dependencies : Helper → List Helper
  | .isHexDigit => [.isDigit]
  | .natOfFrom => [.zeroConstant]
  | .natOf => [.natOfFrom]
  | .countOf => [.natOf]
  | .intOf => [.minusConstant, .natOf]
  | .signOf => [.minusConstant]
  | _ => []

def tokenHelper : TokClass → Helper
  | .digit => .isDigit
  | .hexDigit => .isHexDigit
  | .bit => .isBit

def expressionHelpers : IR.Expr → List Helper
  | .var _ | .capture _ _ | .boolLit _ | .intLit _ | .byteLit _ | .textLit _
  | .optionNone => []
  | .optionSome expression | .field expression _ | .intNeg expression
  | .textLen expression | .byteToInt expression | .noLeadingZero expression =>
      expressionHelpers expression
  | .call _ args | .valueRef _ _ args =>
      args.flatMap expressionHelpers
  | .textConcat left right | .intAdd left right | .intSub left right
  | .intMul left right | .textIndex left right | .boolAnd left right
  | .boolOr left right | .boolImplies left right | .intEq left right
  | .intNe left right | .intLt left right | .intLe left right | .intGt left right
  | .intGe left right | .byteEq left right | .byteNe left right | .textEq left right
  | .textNe left right =>
      expressionHelpers left ++ expressionHelpers right
  | .intPow base exponent =>
      .intPow :: (expressionHelpers base ++ expressionHelpers exponent)
  | .textSubrange expression start stop =>
      expressionHelpers expression ++ expressionHelpers start ++ expressionHelpers stop
  | .ifThenElse condition thenBranch elseBranch =>
      expressionHelpers condition ++ expressionHelpers thenBranch ++
        expressionHelpers elseBranch
  | .forallE _ _ body | .existsE _ body | .choose _ body =>
      expressionHelpers body
  | .matchOption scrutinee _ someBranch noneBranch =>
      expressionHelpers scrutinee ++ expressionHelpers someBranch ++
        expressionHelpers noneBranch
  | .isToken token expression =>
      tokenHelper token :: expressionHelpers expression
  | .natOf expression =>
      .natOf :: expressionHelpers expression
  | .intOf expression =>
      .intOf :: expressionHelpers expression
  | .signOf expression =>
      .signOf :: expressionHelpers expression
  | .countOf _ expression =>
      .countOf :: expressionHelpers expression
  | .card _ _ expressions =>
      expressions.flatMap expressionHelpers

def declarationHelpers : IR.Decl → List Helper
  | .function function =>
      expressionHelpers function.body ++
        function.recommends.flatMap expressionHelpers ++
        function.decreases.toList.flatMap expressionHelpers
  | .structure _ => []
  | .constant constant => expressionHelpers constant.initializer

def closeHelperDependencies : Nat → List Helper → List Helper
  | 0, helpers => helpers.eraseDups
  | fuel + 1, helpers =>
      let expanded := (helpers ++ helpers.flatMap Helper.dependencies).eraseDups
      closeHelperDependencies fuel expanded

def requiredHelpers (declarations : List IR.Decl) : List Helper :=
  closeHelperDependencies helperOrder.length
    (declarations.flatMap declarationHelpers).eraseDups

private def tokenPredicateName : TokClass → String
  | .digit => "triptych_is_digit"
  | .hexDigit => "triptych_is_hex_digit"
  | .bit => "triptych_is_bit"

def lowerExpr : IR.Expr → Ast.Expr
  | .var name => .var name
  | .capture ident _ => .var ident
  | .boolLit literal => .boolLit literal
  | .intLit literal => .intLit literal
  | .byteLit literal => .byteLit literal
  | .textLit literal => .textLit literal
  | .optionNone => .optionNone
  | .optionSome expression => .optionSome (lowerExpr expression)
  | .call name args => .call name (args.map lowerExpr)
  | .valueRef name _ args => .call name (args.map lowerExpr)
  | .field base name => .field (lowerExpr base) name
  | .textConcat left right => .textConcat (lowerExpr left) (lowerExpr right)
  | .intAdd left right => .intAdd (lowerExpr left) (lowerExpr right)
  | .intSub left right => .intSub (lowerExpr left) (lowerExpr right)
  | .intMul left right => .intMul (lowerExpr left) (lowerExpr right)
  | .intNeg expression => .intNeg (lowerExpr expression)
  | .intPow base exponent =>
      .call "triptych_int_pow" [lowerExpr base, lowerExpr exponent]
  | .textLen expression => .textLen (lowerExpr expression)
  | .textIndex expression index => .textIndex (lowerExpr expression) (lowerExpr index)
  | .textSubrange expression start stop =>
      .textSubrange (lowerExpr expression) (lowerExpr start) (lowerExpr stop)
  | .byteToInt expression => .byteToInt (lowerExpr expression)
  | .boolAnd left right => .boolAnd (lowerExpr left) (lowerExpr right)
  | .boolOr left right => .boolOr (lowerExpr left) (lowerExpr right)
  | .boolImplies left right => .boolImplies (lowerExpr left) (lowerExpr right)
  | .intEq left right => .intEq (lowerExpr left) (lowerExpr right)
  | .intNe left right => .intNe (lowerExpr left) (lowerExpr right)
  | .intLt left right => .intLt (lowerExpr left) (lowerExpr right)
  | .intLe left right => .intLe (lowerExpr left) (lowerExpr right)
  | .intGt left right => .intGt (lowerExpr left) (lowerExpr right)
  | .intGe left right => .intGe (lowerExpr left) (lowerExpr right)
  | .byteEq left right => .byteEq (lowerExpr left) (lowerExpr right)
  | .byteNe left right => .byteNe (lowerExpr left) (lowerExpr right)
  | .textEq left right => .textEq (lowerExpr left) (lowerExpr right)
  | .textNe left right => .textNe (lowerExpr left) (lowerExpr right)
  | .ifThenElse condition thenBranch elseBranch =>
      .ifThenElse (lowerExpr condition) (lowerExpr thenBranch) (lowerExpr elseBranch)
  | .forallE binders autoTrigger body => .forallE binders autoTrigger (lowerExpr body)
  | .existsE binders body => .existsE binders (lowerExpr body)
  | .choose binder body => .choose binder (lowerExpr body)
  | .matchOption scrutinee binder someBranch noneBranch =>
      .matchOption (lowerExpr scrutinee) binder (lowerExpr someBranch)
        (lowerExpr noneBranch)
  | .isToken token expression =>
      .call (tokenPredicateName token) [lowerExpr expression]
  | .natOf expression =>
      .call "triptych_nat_of" [lowerExpr expression]
  | .intOf expression =>
      .call "triptych_int_of" [lowerExpr expression]
  | .signOf expression =>
      .call "triptych_sign_of" [lowerExpr expression]
  | .countOf _ expression =>
      .call "triptych_count_of" [lowerExpr expression]
  | .noLeadingZero expression =>
      let operand := lowerExpr expression
      .boolOr (.intEq (.textLen operand) (.intLit 0))
        (.boolOr
          (.byteNe (.textIndex operand (.intLit 0)) (.byteLit 48))
          (.textEq operand (.textLit "0")))
  | .card operation k expressions =>
      let operands := expressions.map lowerExpr
      let present operand :=
        Ast.Expr.ifThenElse (.intEq (.textLen operand) (.intLit 0))
          (.intLit 0) (.intLit 1)
      let total := Ast.Expr.intSum (operands.map present)
      match operation with
      | .atLeast => .intLe (.intLit (Int.ofNat k)) total
      | .atMost => .intLe total (.intLit (Int.ofNat k))
      | .exactlyK => .intEq total (.intLit (Int.ofNat k))

def lowerFunction (function : IR.FunctionDecl) : Ast.FunctionDecl :=
  { name := function.name
    params := function.params
    returnType := function.returnType
    body := lowerExpr function.body
    mode := function.mode
    isPublic := function.isPublic
    isOpen := function.isOpen
    recommends := function.recommends.map lowerExpr
    decreases := function.decreases.map lowerExpr
    doc := function.doc }

def lowerDeclaration : IR.Decl → Ast.Decl
  | .function function => .function (lowerFunction function)
  | .structure structDecl => .structure structDecl
  | .constant constant =>
      .constant
        { name := constant.name
          ty := constant.ty
          initializer := lowerExpr constant.initializer
          isPublic := constant.isPublic }

def helperBoolFunction (name : String) (params : List Ast.Param) (body : Ast.Expr)
    (doc : Option String := none) : Ast.Decl :=
  .function { name, params, returnType := .bool, body, doc }

def helperIntFunction (name : String) (params : List Ast.Param) (body : Ast.Expr)
    (doc : Option String := none) : Ast.Decl :=
  .function { name, params, returnType := .int, body, doc }

def helperDeclaration : Helper → Ast.Decl
  | .minusConstant =>
      .constant { name := "TRIPTYCH_MINUS", ty := .byte, initializer := .byteLit 45 }
  | .zeroConstant =>
      .constant { name := "TRIPTYCH_ZERO", ty := .byte, initializer := .byteLit 48 }
  | .isDigit =>
      let byte : Ast.Expr := .var "byte"
      let byteInt := Ast.Expr.byteToInt byte
      helperBoolFunction "triptych_is_digit" [{ name := "byte", ty := .byte }]
        (.boolAnd
          (.intLe (.intLit 48) byteInt)
          (.intLe byteInt (.intLit 57)))
  | .isHexDigit =>
      let byte : Ast.Expr := .var "byte"
      let byteInt := Ast.Expr.byteToInt byte
      helperBoolFunction "triptych_is_hex_digit" [{ name := "byte", ty := .byte }]
        (.boolOr
          (.call "triptych_is_digit" [byte])
          (.boolOr
            (.boolAnd (.intLe (.intLit 65) byteInt) (.intLe byteInt (.intLit 70)))
            (.boolAnd (.intLe (.intLit 97) byteInt) (.intLe byteInt (.intLit 102)))))
  | .isBit =>
      let byte : Ast.Expr := .var "byte"
      helperBoolFunction "triptych_is_bit" [{ name := "byte", ty := .byte }]
        (.boolOr (.byteEq byte (.byteLit 48)) (.byteEq byte (.byteLit 49)))
  | .natOfFrom =>
      let bytes : Ast.Expr := .var "bytes"
      let index : Ast.Expr := .var "index"
      let accumulator : Ast.Expr := .var "accumulator"
      let byteInt := Ast.Expr.byteToInt (.textIndex bytes index)
      let zeroInt := Ast.Expr.byteToInt (.var "TRIPTYCH_ZERO")
      let digitValue :=
        Ast.Expr.ifThenElse (.intLt byteInt zeroInt) (.intLit 0)
          (.intSub byteInt zeroInt)
      .function
        { name := "triptych_nat_of_from"
          params :=
            [{ name := "bytes", ty := .text },
             { name := "index", ty := .int },
             { name := "accumulator", ty := .int }]
          returnType := .int
          body :=
            .ifThenElse
              (.intLt index (.textLen bytes))
              (.call "triptych_nat_of_from"
                [bytes,
                 .intAdd index (.intLit 1),
                 .intAdd (.intMul accumulator (.intLit 10)) digitValue])
              accumulator
          recommends :=
            [.boolAnd (.intLe (.intLit 0) index) (.intLe index (.textLen bytes))]
          decreases := some (.intSub (.textLen bytes) index) }
  | .natOf =>
      let bytes : Ast.Expr := .var "bytes"
      helperIntFunction "triptych_nat_of" [{ name := "bytes", ty := .text }]
        (.call "triptych_nat_of_from" [bytes, .intLit 0, .intLit 0])
  | .countOf =>
      let bytes : Ast.Expr := .var "bytes"
      helperIntFunction "triptych_count_of" [{ name := "bytes", ty := .text }]
        (.call "triptych_nat_of" [bytes])
  | .intOf =>
      let bytes : Ast.Expr := .var "bytes"
      helperIntFunction "triptych_int_of" [{ name := "bytes", ty := .text }]
        (.ifThenElse
          (.boolAnd
            (.intGt (.textLen bytes) (.intLit 0))
            (.byteEq (.textIndex bytes (.intLit 0)) (.var "TRIPTYCH_MINUS")))
          (.intNeg
            (.call "triptych_nat_of"
              [.textSubrange bytes (.intLit 1) (.textLen bytes)]))
          (.call "triptych_nat_of" [bytes]))
  | .signOf =>
      let bytes : Ast.Expr := .var "bytes"
      helperIntFunction "triptych_sign_of" [{ name := "bytes", ty := .text }]
        (.ifThenElse
          (.boolAnd
            (.intGt (.textLen bytes) (.intLit 0))
            (.byteEq (.textIndex bytes (.intLit 0)) (.var "TRIPTYCH_MINUS")))
          (.intLit (-1))
          (.intLit 1))
  | .intPow =>
      let exponent : Ast.Expr := .var "exponent"
      let base : Ast.Expr := .var "base"
      .function
        { name := "triptych_int_pow"
          params := [{ name := "base", ty := .int }, { name := "exponent", ty := .int }]
          returnType := .int
          body :=
            .ifThenElse
              (.intGt exponent (.intLit 0))
              (.intMul base
                (.call "triptych_int_pow" [base, .intSub exponent (.intLit 1)]))
              (.intLit 1)
          decreases :=
            some (.ifThenElse (.intGt exponent (.intLit 0)) exponent (.intLit 0)) }

def helperDeclarations (declarations : List IR.Decl) : List Ast.Decl :=
  let needed := requiredHelpers declarations
  (helperOrder.filter needed.contains).map helperDeclaration

def lowerModule (irModule : IR.Module) : Ast.Module :=
  { header := irModule.header
    imports := irModule.imports
    declarations :=
      helperDeclarations irModule.declarations ++
        irModule.declarations.map lowerDeclaration }

end Triptych.Backend.Verus
