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

import Triptych.Backend.Verus

namespace Triptych.Verus.Tests

private def decimalGrammar : Grammar :=
  { start := "Decimal"
    prods :=
      [ { name := "Decimal"
          alts :=
            [[SymItem.mk (.ref "Sign") false, SymItem.mk (.ref "Natural") false,
              SymItem.mk (.lit ".") false, SymItem.mk (.ref "Fraction") false]] },
        { name := "Sign", alts := [[SymItem.mk (.lit "-") true]] },
        { name := "Natural", alts := [[SymItem.mk (.term .digit .atLeastOne) false]] },
        { name := "Fraction", alts := [[SymItem.mk (.term .digit (.between 1 4)) false]] } ] }

private def decimalValue : ValExpr :=
  .mul (.signOf "Sign")
    (.add
      (.mul (.nat "Natural") (.pow (.lit 10) (.lit 4)))
      (.mul (.nat "Fraction") (.pow (.lit 10) (.sub (.lit 4) (.len "Fraction")))))

private def decimalConstraints : List Constraint :=
  [.and
    (.le (.lit (-9223372036854775808)) decimalValue)
    (.le decimalValue (.lit 9223372036854775807))]

private def contains (source needle : String) : Bool :=
  (source.splitOn needle).length > 1

example (env : Env) (fieldName : Backend.Verus.FieldName) (expression : ValExpr) :
    (Backend.Verus.translateValExpr fieldName expression).denoteInt env =
      some (expression.eval env) :=
  Backend.Verus.denoteInt_translateValExpr env fieldName expression

example (env : Env) (fieldName : Backend.Verus.FieldName) (constraint : Constraint)
    (hpresent : Backend.Verus.ConstraintStringCapturesPresent env constraint) :
    (Backend.Verus.translateConstraint fieldName constraint).denoteProp env =
      some (constraint.eval env) :=
  Backend.Verus.denoteProp_translateConstraint env fieldName constraint hpresent

example (helper : Backend.Verus.Helper) : helper.Realizes :=
  Backend.Verus.helperDeclaration_realizes helper

example (sourceEnv : Env) (fieldName : Backend.Verus.FieldName)
    (targetEnv : Backend.Verus.Ast.EvalEnv) (expression : ValExpr)
    (hagrees : Backend.Verus.AstEnvAgrees sourceEnv fieldName targetEnv) :
    (Backend.Verus.lowerExpr (Backend.Verus.translateValExpr fieldName expression)).evaluate
        Backend.Verus.canonicalCalls targetEnv =
      some (.int (expression.eval sourceEnv)) :=
  Backend.Verus.lower_translateValExpr_preserves sourceEnv fieldName targetEnv expression
    hagrees

example (sourceEnv : Env) (fieldName : Backend.Verus.FieldName)
    (targetEnv : Backend.Verus.Ast.EvalEnv) (constraint : Constraint)
    (hpresent : Backend.Verus.ConstraintStringCapturesPresent sourceEnv constraint)
    (hagrees : Backend.Verus.AstEnvAgrees sourceEnv fieldName targetEnv) :
    (Backend.Verus.lowerExpr (Backend.Verus.translateConstraint fieldName constraint)).evaluate
        Backend.Verus.canonicalCalls targetEnv =
      some (.bool (decide (constraint.eval sourceEnv))) :=
  Backend.Verus.lower_translateConstraint_preserves sourceEnv fieldName targetEnv constraint
    hpresent hagrees

#guard
  Backend.Verus.evaluateHelper .natOf [.text [49, 50]] == some (.int 12)

#guard
  Backend.Verus.evaluateHelper .signOf [.text [45]] == some (.int (-1))

#guard
  Backend.Verus.evaluateHelper .intPow [.int 10, .int 4] == some (.int 10000)

#guard
  Triptych.Backend.Verus.prettyPrintExpr
    (.textLen (.var "input")) == "(input.len() as int)"

#guard
  (emitSpec "Decimal" decimalGrammar decimalValue [] decimalConstraints
    `Int64.ofInt `Int64.toInt).isOk
#guard
  match emitSpec "Decimal" decimalGrammar decimalValue [] decimalConstraints
      `Int64.ofInt `Int64.toInt with
  | .error _ => false
  | .ok source =>
      [ "decimal_is_wf_sign",
        "decimal_is_wf_natural",
        "decimal_is_wf_fraction",
        "decimal_is_wf_decimal",
        "triptych_is_digit",
        "triptych_nat_of",
        "triptych_sign_of",
        "triptych_int_pow",
        "pub struct DecimalView",
        "decimal_value",
        "decimal_constraints",
        "decimal_satisfies_constraints",
        "decimal_view_valid",
        "decimal_view_denotation",
        "decimal_is_valid" ].all (contains source) &&
      !contains source "proof fn" &&
      !contains source "parser_contract" &&
      !contains source "printer_contract" &&
      !contains source "decimal_decode_view" &&
      !contains source "decimal_compute_value" &&
      !contains source "decimal_spec_parse" &&
      !contains source "triptych_is_hex_digit" &&
      !contains source "triptych_is_bit" &&
      !contains source "fn triptych_int_of"

#guard
  match emitSoundness "Decimal" decimalGrammar decimalValue [] decimalConstraints
      `Int64.ofInt `Int64.toInt with
  | .error _ => false
  | .ok source =>
      [ "use crate::spec::*;",
        "decimal_matches_result",
        "pub trait DecimalExternalParserContract",
        "spec fn parse_to_spec",
        "proof fn extparse_sound",
        "proof fn extparse_complete",
        "proof fn extparse_reject",
        "requires",
        "ensures" ].all (contains source) &&
      !contains source "external_body" &&
      !contains source "assume("

#guard
  match emitCertifiedRust "Decimal" decimalGrammar decimalValue [] decimalConstraints
      `Int64.ofInt `Int64.toInt with
  | .error _ => false
  | .ok output =>
      let source := output.parser
      [ "ScanPlan is verified-lowered to CursorProgram, which is compiled away.",
        "pub struct DecimalParseSpec",
        "pub struct DecimalParseResult",
        "pub open spec fn decimal_parse_plan",
        "pub proof fn decimal_is_wf_implies_parse_plan",
        "pub fn decimal_parse_candidate(input: &str)",
        "&& decimal_is_wf_decimal(input@)",
        "&& !decimal_is_wf_decimal(input@)",
        "plan_scan_token_end_at_boundary",
        "plan_scan_token_end_exec",
        "PlanTokenClass::Digit",
        "sign_start",
        "natural_start",
        "fraction_start" ].all (contains source) &&
      !contains source "GrammarInput" &&
      !contains source "Vec<Candidate>" &&
      !contains source "let program = RuntimeProgram" &&
      !contains source "use regex" &&
      !contains source "FixedPoint" &&
      !contains source "external_body" &&
      !contains source "assume("

private def moneyGrammar : Grammar :=
  { start := "Amount"
    prods :=
      [ { name := "Amount"
          alts :=
            [[SymItem.mk (.ref "Polarity") false, SymItem.mk (.ref "Whole") false,
              SymItem.mk (.lit ",") false, SymItem.mk (.ref "Cents") false]] },
        { name := "Polarity", alts := [[SymItem.mk (.lit "-") true]] },
        { name := "Whole", alts := [[SymItem.mk (.term .digit .atLeastOne) false]] },
        { name := "Cents", alts := [[SymItem.mk (.term .digit (.between 1 4)) false]] } ] }

private def moneyValue : ValExpr :=
  .mul (.signOf "Polarity")
    (.add
      (.mul (.nat "Whole") (.pow (.lit 10) (.lit 4)))
      (.mul (.nat "Cents") (.pow (.lit 10) (.sub (.lit 4) (.len "Cents")))))

private def moneyConstraints : List Constraint :=
  [.and
    (.le (.lit (-9223372036854775808)) moneyValue)
    (.le moneyValue (.lit 9223372036854775807))]

#guard
  match emitCertifiedRust "Money" moneyGrammar moneyValue [] moneyConstraints
      `Int64.ofInt `Int64.toInt with
  | .error _ => false
  | .ok output =>
      let source := output.parser
      [ "pub fn money_parse_candidate(input: &str)",
        "pub proof fn money_is_wf_implies_parse_plan",
        "pub struct MoneyParseResult",
        "polarity_start",
        "whole_start",
        "cents_start",
        "== 45u8",
        "== 44u8" ].all (contains source) &&
      !contains source "GrammarSymbol" &&
      !contains source "GrammarItem" &&
      !contains source "let program = RuntimeProgram" &&
      !contains source "DecimalView"

#guard
  match emitCertifiedRust "Decimal" decimalGrammar decimalValue []
      (decimalConstraints ++ [.le decimalValue (.lit 0)])
      `Int64.ofInt `Int64.toInt with
  | .error _ => false
  | .ok output => contains output.parser "decimal_parse_candidate"

#guard
  match emitCertifiedRust "Decimal" decimalGrammar decimalValue [] decimalConstraints
      `id `id with
  | .error _ => false
  | .ok output => contains output.parser "decimal_parse_candidate"

private def quantityGrammar : Grammar :=
  { start := "Quantity"
    prods :=
      [ { name := "Quantity", alts := [[SymItem.mk (.ref "Digits") false]] },
        { name := "Digits", alts := [[SymItem.mk (.term .digit .atLeastOne) false]] } ] }

private def quantityValue : ValExpr :=
  .nat "Digits"

#guard
  match emitCertifiedRust "Quantity" quantityGrammar quantityValue
      [.noLeadingZero "Digits"] [.le quantityValue (.lit 100)] `id `id with
  | .error _ => false
  | .ok output =>
      [ "pub fn quantity_parse_candidate(input: &str)",
        "GrammarInput",
        "parse_checked_grammar_candidate" ].all (contains output.parser) &&
      !contains output.parser "pub proof fn quantity_is_wf_implies_parse_plan" &&
      !contains output.parser "assume("

#guard
  match emitSpec "Quantity" quantityGrammar quantityValue
      [.noLeadingZero "Digits"] [.le quantityValue (.lit 100)] `id `id with
  | .error _ => false
  | .ok source =>
      [ "quantity_is_wf_quantity",
        "quantity_is_wf_digits",
        "quantity_wf_constraints",
        "quantity_satisfies_wf_constraints",
        "quantity_value",
        "quantity_constraints",
        "quantity_is_valid",
        "Lean conversion boundary: ofSpec `id`, toSpec `id`" ].all (contains source) &&
      !contains source "decimal_"

private def hexadecimalGrammar : Grammar :=
  { start := "Hexadecimal"
    prods :=
      [{ name := "Hexadecimal"
         alts := [[SymItem.mk (.term .hexDigit .atLeastOne) false]] }] }

#guard
  match emitSpec "Hexadecimal" hexadecimalGrammar (.lit 0) [] [] `id `id with
  | .error _ => false
  | .ok source =>
      contains source "triptych_is_digit" &&
      contains source "triptych_is_hex_digit" &&
      !contains source "triptych_is_bit" &&
      !contains source "triptych_nat_of"

private def bitStringGrammar : Grammar :=
  { start := "BitString"
    prods :=
      [{ name := "BitString"
         alts := [[SymItem.mk (.term .bit .atLeastOne) false]] }] }

#guard
  match emitSpec "BitString" bitStringGrammar (.lit 0) [] [] `id `id with
  | .error _ => false
  | .ok source =>
      contains source "triptych_is_bit" &&
      !contains source "triptych_is_digit" &&
      !contains source "triptych_is_hex_digit" &&
      !contains source "triptych_nat_of"

#guard
  match emitSpec "Decimal" decimalGrammar (.count "Natural") [] decimalConstraints
      `Int64.ofInt `Int64.toInt with
  | .error _ => true
  | .ok _ => false

private def missingCaptureAlternativeGrammar : Grammar :=
  { start := "Root"
    prods :=
      [ { name := "Root"
          alts :=
            [[SymItem.mk (.lit "a") false, SymItem.mk (.ref "Tag") false],
             [SymItem.mk (.lit "b") false]] },
        { name := "Tag", alts := [[SymItem.mk (.term .digit .atLeastOne) false]] } ] }

#guard
  match emitSpec "MissingCapture" missingCaptureAlternativeGrammar (.lit 0)
      [.strEq "Tag" "1"] [] `id `id with
  | .error _ => true
  | .ok _ => false

private def quotedStringGrammar : Grammar :=
  { start := "Quoted"
    prods :=
      [{ name := "Quoted", alts := [[SymItem.mk .str false]] }] }

#guard
  match emitCertifiedRust "Quoted" quotedStringGrammar (.lit 0) [] [] `id `id with
  | .error _ => false
  | .ok output =>
      [ "triptych_string_tail",
        "triptych_is_string_literal",
        "GrammarSymbol::StringLiteral",
        "quoted_parse_candidate" ].all (contains (output.spec ++ output.parser))

private def separatedGrammar : Grammar :=
  { start := "List"
    prods :=
      [ { name := "List"
          alts :=
            [[SymItem.mk (.rep "," (.ref "Item") 1 (some 4)) false]] },
        { name := "Item"
          alts := [[SymItem.mk (.term .digit .atLeastOne) false]] } ] }

#guard
  match emitCertifiedRust "Separated" separatedGrammar (.lit 0) [] [] `id `id with
  | .error _ => false
  | .ok output =>
      [ "separated_rep_0_matches",
        "GrammarSymbol::Repetition",
        "separator: \",\"",
        "separated_parse_candidate" ].all (contains (output.spec ++ output.parser))

private def ambiguousGrammar : Grammar :=
  { start := "Ambiguous"
    prods :=
      [{ name := "Ambiguous"
         alts :=
           [[SymItem.mk (.term .digit .atLeastOne) false],
            [SymItem.mk (.term .digit (.exactly 1)) false]] }] }

#guard
  (emitCertifiedRust "Ambiguous" ambiguousGrammar (.lit 0) [] [] `id `id).isOk

private def unicodeGrammar : Grammar :=
  { start := "Unicode"
    prods := [{ name := "Unicode", alts := [[SymItem.mk (.lit "λ") false]] }] }

#guard
  match emitCertifiedRust "Unicode" unicodeGrammar (.lit 0) [] [] `id `id with
  | .error _ => false
  | .ok output =>
      contains output.spec "'\\u{3bb}'" &&
        contains output.parser "GrammarSymbol::Literal(\"λ\")"

end Triptych.Verus.Tests
