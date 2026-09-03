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

import Triptych.Backend.Verus.Surface

/-!
# Verus semantic-node desugaring

This phase eliminates every Triptych-specific expression from `Verus.Semantic`, selects the
required runtime helpers, and produces `Verus.Surface`, which contains only surface-language
constructs.
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
  | intOf
  | signOf
  | intPow
  deriving Repr, Inhabited, DecidableEq, BEq

def helperOrder : List Helper :=
  [.minusConstant, .zeroConstant, .isDigit, .isHexDigit, .isBit,
   .natOfFrom, .natOf, .intOf, .signOf, .intPow]

def Helper.dependencies : Helper → List Helper
  | .isHexDigit => [.isDigit]
  | .natOfFrom => [.zeroConstant]
  | .natOf => [.natOfFrom]
  | .intOf => [.minusConstant, .natOf]
  | .signOf => [.minusConstant]
  | _ => []

def tokenHelper : TokClass → Helper
  | .digit => .isDigit
  | .hexDigit => .isHexDigit
  | .bit => .isBit

def expressionHelpers : Semantic.Expr → List Helper
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
      expressionHelpers expression
  | .card _ _ expressions =>
      expressions.flatMap expressionHelpers

def declarationHelpers : Semantic.Decl → List Helper
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

def requiredHelpers (declarations : List Semantic.Decl) : List Helper :=
  closeHelperDependencies helperOrder.length
    (declarations.flatMap declarationHelpers).eraseDups

private def tokenPredicateName : TokClass → String
  | .digit => "triptych_is_digit"
  | .hexDigit => "triptych_is_hex_digit"
  | .bit => "triptych_is_bit"

def desugarExpr : Semantic.Expr → Surface.Expr
  | .var name => .var name
  | .capture ident _ => .var ident
  | .boolLit literal => .boolLit literal
  | .intLit literal => .intLit literal
  | .byteLit literal => .byteLit literal
  | .textLit literal => .textLit literal
  | .optionNone => .optionNone
  | .optionSome expression => .optionSome (desugarExpr expression)
  | .call name args => .call name (args.map desugarExpr)
  | .valueRef name _ args => .call name (args.map desugarExpr)
  | .field base name => .field (desugarExpr base) name
  | .textConcat left right => .textConcat (desugarExpr left) (desugarExpr right)
  | .intAdd left right => .intAdd (desugarExpr left) (desugarExpr right)
  | .intSub left right => .intSub (desugarExpr left) (desugarExpr right)
  | .intMul left right => .intMul (desugarExpr left) (desugarExpr right)
  | .intNeg expression => .intNeg (desugarExpr expression)
  | .intPow base exponent =>
      .call "triptych_int_pow" [desugarExpr base, desugarExpr exponent]
  | .textLen expression => .textLen (desugarExpr expression)
  | .textIndex expression index => .textIndex (desugarExpr expression) (desugarExpr index)
  | .textSubrange expression start stop =>
      .textSubrange (desugarExpr expression) (desugarExpr start) (desugarExpr stop)
  | .byteToInt expression => .byteToInt (desugarExpr expression)
  | .boolAnd left right => .boolAnd (desugarExpr left) (desugarExpr right)
  | .boolOr left right => .boolOr (desugarExpr left) (desugarExpr right)
  | .boolImplies left right => .boolImplies (desugarExpr left) (desugarExpr right)
  | .intEq left right => .intEq (desugarExpr left) (desugarExpr right)
  | .intNe left right => .intNe (desugarExpr left) (desugarExpr right)
  | .intLt left right => .intLt (desugarExpr left) (desugarExpr right)
  | .intLe left right => .intLe (desugarExpr left) (desugarExpr right)
  | .intGt left right => .intGt (desugarExpr left) (desugarExpr right)
  | .intGe left right => .intGe (desugarExpr left) (desugarExpr right)
  | .byteEq left right => .byteEq (desugarExpr left) (desugarExpr right)
  | .byteNe left right => .byteNe (desugarExpr left) (desugarExpr right)
  | .textEq left right => .textEq (desugarExpr left) (desugarExpr right)
  | .textNe left right => .textNe (desugarExpr left) (desugarExpr right)
  | .ifThenElse condition thenBranch elseBranch =>
      .ifThenElse (desugarExpr condition) (desugarExpr thenBranch) (desugarExpr elseBranch)
  | .forallE binders autoTrigger body => .forallE binders autoTrigger (desugarExpr body)
  | .existsE binders body => .existsE binders (desugarExpr body)
  | .choose binder body => .choose binder (desugarExpr body)
  | .matchOption scrutinee binder someBranch noneBranch =>
      .matchOption (desugarExpr scrutinee) binder (desugarExpr someBranch)
        (desugarExpr noneBranch)
  | .isToken token expression =>
      .call (tokenPredicateName token) [desugarExpr expression]
  | .natOf expression =>
      .call "triptych_nat_of" [desugarExpr expression]
  | .intOf expression =>
      .call "triptych_int_of" [desugarExpr expression]
  | .signOf expression =>
      .call "triptych_sign_of" [desugarExpr expression]
  | .countOf _ expression =>
      .call "triptych_count_of" [desugarExpr expression]
  | .noLeadingZero expression =>
      let operand := desugarExpr expression
      .boolOr (.intEq (.textLen operand) (.intLit 0))
        (.boolOr
          (.byteNe (.textIndex operand (.intLit 0)) (.byteLit 48))
          (.textEq operand (.textLit "0")))
  | .card operation k expressions =>
      let operands := expressions.map desugarExpr
      let present operand :=
        Surface.Expr.ifThenElse (.intEq (.textLen operand) (.intLit 0))
          (.intLit 0) (.intLit 1)
      let total := Surface.Expr.intSum (operands.map present)
      match operation with
      | .atLeast => .intLe (.intLit (Int.ofNat k)) total
      | .atMost => .intLe total (.intLit (Int.ofNat k))
      | .exactlyK => .intEq total (.intLit (Int.ofNat k))

def desugarFunction (function : Semantic.FunctionDecl) : Surface.FunctionDecl :=
  { name := function.name
    params := function.params
    returnType := function.returnType
    body := desugarExpr function.body
    mode := function.mode
    isPublic := function.isPublic
    isOpen := function.isOpen
    recommends := function.recommends.map desugarExpr
    decreases := function.decreases.map desugarExpr
    doc := function.doc }

def desugarDeclaration : Semantic.Decl → Surface.Decl
  | .function function => .function (desugarFunction function)
  | .structure structDecl => .structure structDecl
  | .constant constant =>
      .constant
        { name := constant.name
          ty := constant.ty
          initializer := desugarExpr constant.initializer
          isPublic := constant.isPublic }

def helperBoolFunction (name : String) (params : List Surface.Param) (body : Surface.Expr)
    (doc : Option String := none) : Surface.Decl :=
  .function { name, params, returnType := .bool, body, doc }

def helperIntFunction (name : String) (params : List Surface.Param) (body : Surface.Expr)
    (doc : Option String := none) : Surface.Decl :=
  .function { name, params, returnType := .int, body, doc }

def helperDeclaration : Helper → Surface.Decl
  | .minusConstant =>
      .constant { name := "TRIPTYCH_MINUS", ty := .byte, initializer := .byteLit 45 }
  | .zeroConstant =>
      .constant { name := "TRIPTYCH_ZERO", ty := .byte, initializer := .byteLit 48 }
  | .isDigit =>
      let byte : Surface.Expr := .var "byte"
      let byteInt := Surface.Expr.byteToInt byte
      helperBoolFunction "triptych_is_digit" [{ name := "byte", ty := .byte }]
        (.boolAnd
          (.intLe (.intLit 48) byteInt)
          (.intLe byteInt (.intLit 57)))
  | .isHexDigit =>
      let byte : Surface.Expr := .var "byte"
      let byteInt := Surface.Expr.byteToInt byte
      helperBoolFunction "triptych_is_hex_digit" [{ name := "byte", ty := .byte }]
        (.boolOr
          (.call "triptych_is_digit" [byte])
          (.boolOr
            (.boolAnd (.intLe (.intLit 65) byteInt) (.intLe byteInt (.intLit 70)))
            (.boolAnd (.intLe (.intLit 97) byteInt) (.intLe byteInt (.intLit 102)))))
  | .isBit =>
      let byte : Surface.Expr := .var "byte"
      helperBoolFunction "triptych_is_bit" [{ name := "byte", ty := .byte }]
        (.boolOr (.byteEq byte (.byteLit 48)) (.byteEq byte (.byteLit 49)))
  | .natOfFrom =>
      let bytes : Surface.Expr := .var "bytes"
      let index : Surface.Expr := .var "index"
      let accumulator : Surface.Expr := .var "accumulator"
      let byteInt := Surface.Expr.byteToInt (.textIndex bytes index)
      let zeroInt := Surface.Expr.byteToInt (.var "TRIPTYCH_ZERO")
      let digitValue :=
        Surface.Expr.ifThenElse (.intLt byteInt zeroInt) (.intLit 0)
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
      let bytes : Surface.Expr := .var "bytes"
      helperIntFunction "triptych_nat_of" [{ name := "bytes", ty := .text }]
        (.call "triptych_nat_of_from" [bytes, .intLit 0, .intLit 0])
  | .intOf =>
      let bytes : Surface.Expr := .var "bytes"
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
      let bytes : Surface.Expr := .var "bytes"
      helperIntFunction "triptych_sign_of" [{ name := "bytes", ty := .text }]
        (.ifThenElse
          (.boolAnd
            (.intGt (.textLen bytes) (.intLit 0))
            (.byteEq (.textIndex bytes (.intLit 0)) (.var "TRIPTYCH_MINUS")))
          (.intLit (-1))
          (.intLit 1))
  | .intPow =>
      let exponent : Surface.Expr := .var "exponent"
      let base : Surface.Expr := .var "base"
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

def helperDeclarations (declarations : List Semantic.Decl) : List Surface.Decl :=
  let needed := requiredHelpers declarations
  (helperOrder.filter needed.contains).map helperDeclaration

def desugarModule (semanticModule : Semantic.Module) : Surface.Module :=
  { header := semanticModule.header
    imports := semanticModule.imports
    declarations :=
      helperDeclarations semanticModule.declarations ++
        semanticModule.declarations.map desugarDeclaration }

end Triptych.Backend.Verus
