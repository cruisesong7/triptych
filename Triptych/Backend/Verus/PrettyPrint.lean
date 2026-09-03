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
# Verus AST pretty-printer

This is the only layer that knows Verus punctuation. It accepts only `Verus.Surface`, after semantic
operations and helper dependencies have been resolved by `Verus.Desugar`. Expressions are
pretty-printed with explicit precedence, and there is no raw-expression constructor.
-/

namespace Triptych.Backend.Verus

open Surface

private def leftBrace : String := "{"
private def rightBrace : String := "}"

private def indent (source : String) (width : Nat := 4) : String :=
  let spaces := String.ofList (List.replicate width ' ')
  String.intercalate "\n" ((source.splitOn "\n").map fun line =>
    if line.isEmpty then "" else spaces ++ line)

private def prettyPrintTy : Surface.Ty → String
  | .bool => "bool"
  | .int => "int"
  | .byte => "u8"
  | .text => "Seq<u8>"
  | .option inner => s!"Option<{prettyPrintTy inner}>"
  | .named name => name

private def prettyPrintBinder (binder : Surface.Binder) : String :=
  s!"{binder.name}: {prettyPrintTy binder.ty}"

private def prettyPrintParam (param : Surface.Param) : String :=
  s!"{param.name}: {prettyPrintTy param.ty}"

private def textLiteral (literal : String) : String :=
  let bytes := literal.toList.map Char.toNat
  "seq![" ++ String.intercalate ", " (bytes.map fun byte => s!"{byte}u8") ++ "]"

private def parenthesize (condition : Bool) (source : String) : String :=
  if condition then "(" ++ source ++ ")" else source

private partial def prettyPrintExprAt (parentPrecedence : Nat) (expression : Surface.Expr) : String :=
  let binary (precedence : Nat) (operator : String) (left right : Surface.Expr) :=
    let source :=
      prettyPrintExprAt precedence left ++ " " ++ operator ++ " " ++
        prettyPrintExprAt (precedence + 1) right
    parenthesize (precedence < parentPrecedence) source
  match expression with
  | .var name => name
  | .boolLit literal => if literal then "true" else "false"
  | .intLit literal => s!"({literal})"
  | .byteLit literal => s!"{literal}u8"
  | .textLit literal => textLiteral literal
  | .optionNone => "None"
  | .optionSome inner => s!"Some({prettyPrintExprAt 0 inner})"
  | .call name args =>
      name ++ "(" ++ String.intercalate ", " (args.map (prettyPrintExprAt 0)) ++ ")"
  | .field base name => s!"{prettyPrintExprAt 90 base}.{name}"
  | .textConcat left right => binary 60 "+" left right
  | .intAdd left right => binary 60 "+" left right
  | .intSub left right => binary 60 "-" left right
  | .intMul left right => binary 70 "*" left right
  | .intNeg operand =>
      parenthesize (80 < parentPrecedence) ("-" ++ prettyPrintExprAt 80 operand)
  | .textLen operand => s!"({prettyPrintExprAt 90 operand}.len() as int)"
  | .textIndex operand index => s!"{prettyPrintExprAt 90 operand}[{prettyPrintExprAt 0 index}]"
  | .textSubrange operand start stop =>
      s!"{prettyPrintExprAt 90 operand}.subrange({prettyPrintExprAt 0 start}, {prettyPrintExprAt 0 stop})"
  | .byteToInt operand => s!"({prettyPrintExprAt 0 operand} as int)"
  | .boolNot operand =>
      parenthesize (80 < parentPrecedence) ("!" ++ prettyPrintExprAt 80 operand)
  | .boolAnd left right => binary 40 "&&" left right
  | .boolOr left right => binary 30 "||" left right
  | .boolImplies left right => binary 20 "==>" left right
  | .intEq left right => binary 50 "==" left right
  | .intNe left right => binary 50 "!=" left right
  | .intLt left right => binary 50 "<" left right
  | .intLe left right => binary 50 "<=" left right
  | .intGt left right => binary 50 ">" left right
  | .intGe left right => binary 50 ">=" left right
  | .byteEq left right => binary 50 "==" left right
  | .byteNe left right => binary 50 "!=" left right
  | .textEq left right => binary 50 "==" left right
  | .textNe left right => binary 50 "!=" left right
  | .ifThenElse condition thenBranch elseBranch =>
      let source :=
        s!"if {prettyPrintExprAt 0 condition} {leftBrace}\n\
          {indent (prettyPrintExprAt 0 thenBranch)}\n\
          {rightBrace} else {leftBrace}\n\
          {indent (prettyPrintExprAt 0 elseBranch)}\n\
          {rightBrace}"
      parenthesize (5 < parentPrecedence) source
  | .forallE binders autoTrigger body =>
      let trigger := if autoTrigger then " #![auto]" else ""
      let source :=
        "forall|" ++ String.intercalate ", " (binders.map prettyPrintBinder) ++ "|" ++ trigger ++
          " " ++ prettyPrintExprAt 20 body
      parenthesize (10 < parentPrecedence) source
  | .existsE binders body =>
      let source :=
        "exists|" ++ String.intercalate ", " (binders.map prettyPrintBinder) ++ "|\n" ++
          indent (prettyPrintExprAt 0 body)
      parenthesize (10 < parentPrecedence) source
  | .choose binder body =>
      let source := s!"choose|{prettyPrintBinder binder}| {prettyPrintExprAt 0 body}"
      parenthesize (10 < parentPrecedence) source
  | .matchOption scrutinee binder someBranch noneBranch =>
      let someArm := s!"Some({binder.name}) => {prettyPrintExprAt 0 someBranch},"
      let noneArm := s!"None => {prettyPrintExprAt 0 noneBranch},"
      let source :=
        s!"match {prettyPrintExprAt 0 scrutinee} {leftBrace}\n\
          {indent someArm}\n\
          {indent noneArm}\n\
          {rightBrace}"
      parenthesize (5 < parentPrecedence) source
def prettyPrintExpr (expression : Surface.Expr) : String :=
  prettyPrintExprAt 0 expression

private def prettyPrintDoc : Option String → String
  | none => ""
  | some doc => "/** " ++ doc ++ " */\n"

private def prettyPrintFunction (function : Surface.FunctionDecl) : String :=
  let visibility := if function.isPublic then "pub " else ""
  let openness := if function.isOpen then "open " else ""
  let mode := match function.mode with
    | .spec => "spec "
    | .executable => ""
    | .proof => "proof "
  let signature :=
    visibility ++ openness ++ mode ++ "fn " ++ function.name ++ "(" ++
      String.intercalate ", " (function.params.map prettyPrintParam) ++ ") -> " ++
      prettyPrintTy function.returnType
  let recommends :=
    if function.recommends.isEmpty then ""
    else
      "\n    recommends\n" ++
        String.intercalate ",\n" (function.recommends.map fun expression =>
          indent (prettyPrintExpr expression) 8) ++ ","
  let decreases := match function.decreases with
    | none => ""
    | some expression => "\n    decreases " ++ prettyPrintExpr expression ++ ","
  prettyPrintDoc function.doc ++ signature ++ recommends ++ decreases ++
    "\n" ++ leftBrace ++ "\n" ++ indent (prettyPrintExpr function.body) ++ "\n" ++ rightBrace

private def prettyPrintStruct (structDecl : Surface.StructDecl) : String :=
  let visibility := if structDecl.isPublic then "pub " else ""
  let fields := structDecl.fields.map fun field =>
    let visibility := if field.isPublic then "pub " else ""
    s!"    {visibility}{field.name}: {prettyPrintTy field.ty},"
  visibility ++ "struct " ++ structDecl.name ++ " " ++ leftBrace ++ "\n" ++
    String.intercalate "\n" fields ++ "\n" ++ rightBrace

private def prettyPrintConst (constant : Surface.ConstDecl) : String :=
  let visibility := if constant.isPublic then "pub " else ""
  visibility ++ "const " ++ constant.name ++ ": " ++ prettyPrintTy constant.ty ++ " = " ++
    prettyPrintExpr constant.initializer ++ ";"

private def prettyPrintContractClause (keyword : String) (expressions : List Surface.Expr) :
    String :=
  if expressions.isEmpty then
    ""
  else
    "\n    " ++ keyword ++ "\n" ++
      String.intercalate ",\n" (expressions.map fun expression =>
        indent (prettyPrintExpr expression) 8) ++ ","

private def prettyPrintTraitItem : Surface.TraitItem → String
  | .specMethod method =>
      prettyPrintDoc method.doc ++
        "spec fn " ++ method.name ++ "(" ++
          String.intercalate ", " (method.params.map prettyPrintParam) ++ ") -> " ++
          prettyPrintTy method.returnType ++ ";"
  | .proofMethod method =>
      prettyPrintDoc method.doc ++
        "proof fn " ++ method.name ++ "(" ++
          String.intercalate ", " (method.params.map prettyPrintParam) ++ ")" ++
          prettyPrintContractClause "requires" method.requires ++
          prettyPrintContractClause "ensures" method.ensures ++
          "\n;"

private def prettyPrintTrait (traitDecl : Surface.TraitDecl) : String :=
  let visibility := if traitDecl.isPublic then "pub " else ""
  let items := String.intercalate "\n\n" (traitDecl.items.map prettyPrintTraitItem)
  prettyPrintDoc traitDecl.doc ++ visibility ++ "trait " ++ traitDecl.name ++ " " ++
    leftBrace ++ "\n" ++ indent items ++ "\n" ++ rightBrace

private def prettyPrintDecl : Surface.Decl → String
  | .function function => prettyPrintFunction function
  | .structure structDecl => prettyPrintStruct structDecl
  | .constant constant => prettyPrintConst constant
  | .trait traitDecl => prettyPrintTrait traitDecl

def prettyPrintModule (targetModule : Surface.Module) : String :=
  let header := String.intercalate "\n" (targetModule.header.map ("// " ++ ·))
  let imports := String.intercalate "\n" (targetModule.imports.map fun path => "use " ++ path ++ ";")
  let declarations := String.intercalate "\n\n" (targetModule.declarations.map prettyPrintDecl)
  header ++ "\n\n" ++ imports ++ "\n\nverus! " ++ leftBrace ++ "\n\n" ++ declarations ++
    "\n\n" ++ rightBrace ++ " // verus!\n"

end Triptych.Backend.Verus
