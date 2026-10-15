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

open Triptych.Backend.Verus

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

private def orderedSearchGrammar : Grammar :=
  { start := "Root"
    prods :=
      [ { name := "Root"
          alts := [[SymItem.mk (.ref "Left") false, SymItem.mk (.ref "Right") false]] },
        { name := "Left", alts := [[SymItem.mk (.term .digit .atLeastOne) false]] },
        { name := "Right", alts := [[SymItem.mk (.term .digit .atLeastOne) false]] } ] }

private def orderedSearchValue : ValExpr :=
  .add (.nat "Left") (.nat "Right")

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
  Backend.Verus.evaluateHelper .hexOf [.text [49, 97, 70]] == some (.int 431)

#guard
  Backend.Verus.evaluateHelper .hexSeqOf [.text [49, 58, 50]] == some (.int 65538)

#guard
  Backend.Verus.evaluateHelper .segmentsOf [.text [49, 58, 50]] == some (.int 2)

#guard
  Triptych.Backend.Verus.prettyPrintExpr
    (.textLen (.var "input")) == "(input.len() as int)"

#guard
  Triptych.Backend.Verus.prettyPrintExpr
    (.intTDiv (.intLit (-9)) (.intLit 4)) == "rust_div((-9int), (4int))"

#guard
  Triptych.Backend.Verus.prettyPrintExpr
    (.intMod (.intLit 9) (.intLit 4)) == "(9int) % (4int)"

#guard
  (emitSpec "Decimal" decimalGrammar decimalValue [] decimalConstraints
    `Int64.ofInt `Int64.toInt).isOk
#guard
  match emitSpec "Decimal" decimalGrammar decimalValue [] decimalConstraints
      `Int64.ofInt `Int64.toInt with
  | .error _ => false
  | .ok source =>
      [ "decimal_is_wf_Sign",
        "decimal_is_wf_Natural",
        "decimal_is_wf_Fraction",
        "decimal_is_wf_Decimal",
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
      `Int64.ofInt `Int64.toInt true with
  | .error _ => false
  | .ok source =>
      [ "use super::spec::*;",
        "decimal_matches_result",
        "pub trait DecimalExternalParserContract",
        "spec fn parse_to_spec",
        "proof fn extparse_sound",
        "proof fn extparse_complete",
        "proof fn extparse_reject",
        "decimal_has_result",
        "spec fn to_string_to_spec",
        "proof fn extparse_to_string_roundtrip",
        "proof fn extparse_to_string_injective",
        "proof fn extparse_normalize_eq_iff_parse_eq",
        "requires",
        "ensures" ].all (contains source) &&
      !contains source "external_body" &&
      !contains source "assume("

#guard
  match emitSoundness "Decimal" decimalGrammar decimalValue [] decimalConstraints
      `Int64.ofInt `Int64.toInt with
  | .error _ => false
  | .ok source =>
      [ "proof fn extparse_sound",
        "proof fn extparse_complete",
        "proof fn extparse_reject" ].all (contains source) &&
      !contains source "decimal_has_result" &&
      !contains source "to_string_to_spec" &&
      !contains source "extparse_to_string_roundtrip" &&
      !contains source "extparse_to_string_injective" &&
      !contains source "extparse_normalize_eq_iff_parse_eq"

#guard
  match emitCertifiedRust "Decimal" decimalGrammar decimalValue [] decimalConstraints
      `Int64.ofInt `Int64.toInt with
  | .error _ => false
  | .ok output =>
      let source := output.parser
      (source.splitOn "pub open spec fn decimal_parse_view").length == 2 &&
      [ "ScanPlan is verified-lowered to CursorProgram, which is compiled away.",
        "pub struct DecimalParseSpec",
        "pub struct DecimalParseResult",
        "pub open spec fn decimal_parse_plan",
        "pub open spec fn decimal_view_runtime_safe",
        "pub proof fn decimal_is_wf_implies_parse_plan",
        "pub fn decimal_parse_candidate(input: &str)",
        "pub fn decimal_parse(input: &str)",
        "match decimal_parse_plan(input@)",
        "!decimal_view_runtime_safe(view) || !decimal_view_valid(view)",
        "Option<i64>",
        "triptych_checked_nat_range",
        "decimal_view_denotation(parsed_view) == value as int",
        "&& decimal_is_wf_Decimal(input@)",
        "&& !decimal_is_wf_Decimal(input@)",
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
      !contains source "assume(" &&
      !contains source "assert(false)"

#guard
  match compileParsePlan decimalGrammar with
  | .scanner _ => false
  | .search _ => false
  | plan@(.cursor _) =>
      match emitCertifiedRustWithPlan "Decimal" decimalGrammar decimalValue []
          decimalConstraints `Int64.ofInt `Int64.toInt plan with
      | .error _ => false
      | .ok output => contains output.parser "decimal_parse_candidate"

#guard
  match emitCertifiedRustWithPlan "Decimal" decimalGrammar decimalValue []
      decimalConstraints `Int64.ofInt `Int64.toInt (.scanner "forced test fallback") with
  | .error message =>
      message.contains "scanner ParsePlans are not emitted" &&
        message.contains "forced test fallback"
  | .ok _ => false

#guard
  match emitCertifiedRustWithPlan "Decimal" decimalGrammar decimalValue []
      decimalConstraints `Int64.ofInt `Int64.toInt
      (.cursor { start := "Unrelated", pattern := .empty }) with
  | .error _ => true
  | .ok _ => false

#guard
  match compileParsePlan orderedSearchGrammar with
  | .cursor _ => false
  | .scanner _ => false
  | plan@(.search _) =>
      match emitCertifiedRustWithPlan "OrderedSearch" orderedSearchGrammar
          orderedSearchValue [] [] `Int64.ofInt `Int64.toInt plan with
      | .error _ => false
      | .ok output =>
            contains output.parser
              "SearchPlan is verified-lowered to callback-free, literal-dispatched SearchMachine states." &&
            contains output.parser "ordered_search_search_state_" &&
            contains output.parser "search_token_prefix_end" &&
            contains output.parser "search_match_terminal_from_prefix" &&
            !contains output.parser "search_match_terminal_at_width" &&
            contains output.parser "ordered_search_search_parse_candidate" &&
            contains output.parser "ordered_search_parse_candidate" &&
            contains output.parser "fn ordered_search_evaluate_candidate" &&
            contains output.parser "ordered_search_candidate_runtime_safe" &&
            contains output.parser
              "match ordered_search_search_parse_candidate(input@)" &&
            contains output.parser
              "!ordered_search_candidate_runtime_safe(input@, candidate)" &&
            !contains output.parser
              "parse_grammar_candidate(\n        &source_grammar"

#guard
  match emitCertifiedRustWithPlan "OrderedSearch" orderedSearchGrammar
      orderedSearchValue [] [] `Int64.ofInt `Int64.toInt
      (.search { start := "Unrelated", alternatives := [] }) with
  | .error _ => true
  | .ok _ => false

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
        "== 44u8",
        "pub fn money_parse(input: &str)",
        "triptych_checked_nat_range",
        "money_view_denotation(parsed_view) == value as int" ].all (contains source) &&
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
      && !contains output.parser "pub fn decimal_parse(input: &str)"

#guard
  match emitCertifiedRust "Decimal" decimalGrammar decimalValue [] decimalConstraints
      `id `id with
  | .error _ => false
  | .ok output => contains output.parser "decimal_parse_candidate"
      && !contains output.parser "pub fn decimal_parse(input: &str)"

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
        "pub proof fn quantity_is_wf_implies_parse_plan",
        "pub struct QuantityParseResult",
        "digits_start",
        "plan_scan_token_end_at_boundary" ].all (contains output.parser) &&
      !contains output.parser "GrammarInput" &&
      !contains output.parser "parse_checked_grammar_candidate" &&
      !contains output.parser "assume(" &&
      !contains output.parser "assert(false)"

private def directCoverageGrammar : Grammar :=
  { start := "DirectCoverage"
    prods :=
      [ { name := "DirectCoverage"
          alts :=
            [[SymItem.mk (.ref "Prefix") false, SymItem.mk (.ref "Digits") false,
              SymItem.mk (.lit "-") false, SymItem.mk (.ref "Payload") false,
              SymItem.mk (.lit ":") false, SymItem.mk (.ref "Bits") false,
              SymItem.mk (.lit "/") false, SymItem.mk (.ref "Upper") false]] },
        { name := "Prefix", alts := [[SymItem.mk (.lit "+") true]] },
        { name := "Payload", alts := [[SymItem.mk (.ref "Hex") false]] },
        { name := "Digits", alts := [[SymItem.mk (.term .digit .atLeastOne) false]] },
        { name := "Hex"
          alts := [[SymItem.mk (.term .hexDigit (.between 1 4)) false]] },
        { name := "Bits", alts := [[SymItem.mk (.term .bit .atLeastOne) false]] },
        { name := "Upper"
          alts := [[SymItem.mk (.term (.asciiRange 65 90) (.exactly 2)) false]] } ] }

#guard
  match emitCertifiedRust "DirectCoverage" directCoverageGrammar (.len "Payload")
      [] [] `id `id with
  | .error _ => false
  | .ok output =>
      [ "pub proof fn direct_coverage_is_wf_implies_parse_plan",
        "pub fn direct_coverage_parse_candidate(input: &str)",
        "payload_start",
        "hex_start",
        "PlanTokenClass::HexDigit",
        "PlanTokenClass::Bit",
        "PlanTokenClass::AsciiRange",
        "#[verifier::rlimit(20)]" ].all (contains output.parser) &&
      !contains output.parser "GrammarInput" &&
      !contains output.parser "assume(" &&
      !contains output.parser "assert(false)"

#guard
  match emitSpec "NestedCoverage" directCoverageGrammar (.len "Payload.Hex")
      [] [] `id `id with
  | .error _ => false
  | .ok source =>
      [ "pub payload_hex: Seq<char>",
        "nested_coverage_matches_view",
        "nested_coverage_value",
        "view.payload_hex" ].all (contains source)

#guard
  match emitCertifiedRust "NestedCoverage" directCoverageGrammar (.len "Payload.Hex")
      [] [] `id `id with
  | .error _ => false
  | .ok output =>
      [ "nested_coverage_parse_view",
        "payload_hex: input.subrange(parsed.hex_start, parsed.hex_end)",
        "nested_coverage_matches_view" ].all (contains output.parser)

#guard
  match emitSpec "Quantity" quantityGrammar quantityValue
      [.noLeadingZero "Digits"] [.le quantityValue (.lit 100)] `id `id with
  | .error _ => false
  | .ok source =>
      [ "quantity_is_wf_Quantity",
        "quantity_is_wf_Digits",
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
        "SearchPlan is verified-lowered to callback-free, literal-dispatched SearchMachine states.",
        "separated_search_state_",
        "search_close_count_capture",
        "CaptureKey::Repetition(1)",
        "search_match_literal_at(",
        "\",\"",
        "separated_parse_candidate" ].all (contains (output.spec ++ output.parser))

#guard
  match emitSpec "SeparatedCount" separatedGrammar (.count "Item") [] [] `id `id with
  | .error _ => false
  | .ok source =>
      [ "separated_count_rep_0_matches_count",
        "pub item_count: Seq<char>",
        "triptych_count_of(item_count)",
        "separated_count_value(view.item_count)" ].all (contains source)

#guard
  match emitCertifiedRust "Decimal" decimalGrammar decimalValue []
      (decimalConstraints ++ [.le decimalValue (.lit 0)]) `Int64.ofInt `Int64.toInt with
  | .error _ => false
  | .ok output => !contains output.parser "pub fn decimal_parse(input: &str)"

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
        contains output.parser "search_match_literal_at(" &&
        contains output.parser "\"λ\""

private def semanticIpGrammar : Grammar :=
  { start := "Net"
    prods :=
      [ { name := "Net"
          alts :=
            [[SymItem.mk (.ref "Address") false,
              SymItem.mk (.lit "/") false,
              SymItem.mk (.ref "Prefix") true]] },
        { name := "Address"
          alts := [[SymItem.mk (.ref "Octet") false]] },
        { name := "Octet"
          alts := [[SymItem.mk (.term .digit (.between 1 3)) false]] },
        { name := "Prefix"
          alts := [[SymItem.mk (.term .digit (.between 1 3)) false]] } ] }

private def semanticIpAddress : ValExpr :=
  .nat "Octet"

private def semanticIpPrefix : ValExpr :=
  .iteEmpty "Prefix" (.lit 32) (.nat "Prefix")

private def semanticIpv4Expression : ValExpr :=
  .add (.mul semanticIpAddress (.lit 33)) semanticIpPrefix

private def semanticIpv6Expression : ValExpr :=
  .add (.mul (.hexSeq "Address") (.lit 129))
    (.iteEmpty "Prefix" (.lit 128) (.nat "Prefix"))

#guard
  match compileSemanticPlan decimalValue [] decimalConstraints "Int64.ofInt" with
  | .ok plan => plan.result == .int64
  | .error _ => false

#guard
  match compileSemanticPlan semanticIpv4Expression [] [] "ipv4CodeToNet" with
  | .ok plan =>
      plan.result == .ip 4 32 33 &&
        match compileFlatGrammar semanticIpGrammar with
        | .ok grammar =>
            match compileSemanticFields grammar plan with
            | .ok fields =>
                fields ==
                  [ { name := "Octet", selector := .production 2 },
                    { name := "Prefix", selector := .production 3 } ]
            | .error _ => false
        | .error _ => false
  | .error _ => false

#guard
  match compileSemanticPlan semanticIpv4Expression [] [] "ipv4CodeToNet",
      compileFlatGrammar semanticIpGrammar with
  | .ok plan, .ok grammar =>
      match compileExecutableSemanticPlan grammar plan with
      | .ok (.ip _ _ _ address prefixExpr _ _) =>
          address.range? == some { lower := 0, upper := 999 } &&
            prefixExpr.range? == some { lower := 0, upper := 999 }
      | _ => false
  | _, _ => false

#guard
  match compileSemanticPlan semanticIpv6Expression [] [] "ipv6CodeToNet" with
  | .ok plan => plan.result == .ip 6 128 129
  | .error _ => false

#guard
  match emitCertifiedRust "IPv4" semanticIpGrammar semanticIpv4Expression [] []
      `ipv4CodeToNet `id with
  | .error _ => false
  | .ok output =>
      [ "pub struct IPv4ParseResult",
        "pub fn ipv4_parse(input: &str)",
        "fn ipv4_evaluate_candidate",
        "ipv4_candidate_runtime_safe",
        "match ipv4_search_parse_candidate(input@)",
        "!ipv4_candidate_runtime_safe(input@, candidate)",
        "ipv4_candidate_address",
        "ipv4_candidate_prefix",
        "bounded_nat_",
        "semantic_nat_of_span",
        "semantic_nat_of_short_span" ].all (contains output.parser)
        && !contains output.parser "pub struct SemanticInt"

#guard
  match emitCertifiedRust "IPv6" semanticIpGrammar semanticIpv6Expression [] []
      `ipv6CodeToNet `id with
  | .error _ => false
  | .ok output =>
      [ "pub struct IPv6ParseResult",
        "pub fn ipv6_parse(input: &str)",
        "fn ipv6_evaluate_candidate",
        "ipv6_candidate_runtime_safe",
        "match ipv6_search_parse_candidate(input@)",
        "!ipv6_candidate_runtime_safe(input@, candidate)",
        "ipv6_candidate_address",
        "ipv6_candidate_prefix",
        "semantic_hex_sequence_of_span",
        "340282366920938463463374607431768211456int" ].all (contains output.parser)
        && !contains output.parser "pub struct SemanticInt"

#guard
  match compileSemanticPlan (.lit 0) [] [] "unknownConversion" with
  | .ok _ => false
  | .error _ => true

end Triptych.Verus.Tests
