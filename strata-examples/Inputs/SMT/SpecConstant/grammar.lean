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

import Triptych.Architecture.Syntax
import StrataDDM.Util.Decimal

/-!
# SMT-LIB specification constants

An acyclic reference grammar for the numeral, decimal, and string alternatives currently
covered by Strata's `SpecConstant` parser tests.
-/

namespace StrataExamples.SMT.SpecConstant
open Triptych

/-- The five specification-constant operations represented by Strata's SMT dialect. -/
inductive Value where
  | numeral (contents : Nat)
  | decimal (contents : StrataDDM.Decimal)
  | string (contents : String)
  | numeralNeg (contents : Nat)
  | decimalNeg (contents : StrataDDM.Decimal)
  deriving Repr, DecidableEq, Inhabited

private def toDecimal (natural fraction : String) : StrataDDM.Decimal where
  mantissa := Int.ofNat ((natural ++ fraction).toNat?.getD 0)
  exponent := -Int.ofNat fraction.length

def toValue (stringLiteral «sign» natural fraction : String) : Value :=
  match decodeStringLiteral stringLiteral with
  | some contents => .string contents
  | none =>
      let negative := «sign» == "-"
      if fraction.isEmpty then
        if negative then .numeralNeg (natural.toNat?.getD 0)
        else .numeral (natural.toNat?.getD 0)
      else
        if negative then .decimalNeg (toDecimal natural fraction)
        else .decimal (toDecimal natural fraction)

/--
Serialize an SMT-LIB specification constant without numeric normalization.

Strata accepts a leading minus as a parser compatibility extension, but its printer must represent
negation at the term level rather than emit that extension.
-/
def serialize : Value → Option String
  | .numeral contents => some (toString contents)
  | .decimal contents => some contents.toPlainString
  | .string contents => some (String.quote contents)
  | .numeralNeg _ => none
  | .decimalNeg _ => none

/-
Strata-DDM primitive definitions used by these operations:

  -- StrataDDM/BuiltinDialects/Init.lean
  declareAtomicCat q`Init.Num
  declareAtomicCat q`Init.Decimal
  declareAtomicCat q`Init.Str

  -- StrataDDM/Elab/LoadedDialects.lean
  (q`Init.Num, Parser.numLit),
  (q`Init.Decimal, Parser.decimalLit),
  (q`Init.Str, Parser.strLit)

  -- StrataDDM/Elab/Tree.lean
  abbrev NumInfo := ConstInfo Nat
  abbrev DecimalInfo := ConstInfo Decimal
  abbrev StrlitInfo := ConstInfo String

  -- StrataDDM/Util/Decimal.lean
  structure Decimal where
    mantissa : Int
    exponent : Int

Corresponding Strata declarations:

  op sc_numeral (@[unwrap] n:Num) : SpecConstant => n;
  op sc_decimal (@[noExponent, unwrap] d:Decimal) : SpecConstant => d;
  op sc_str (@[unwrap] s:Str) : SpecConstant => s;
  op sc_numeral_neg (@[unwrap] n:Num) : SpecConstant => "-" n:0;
  op sc_decimal_neg (@[noExponent, unwrap] n:Decimal) : SpecConstant => "-" n:0;

Existing Strata parser tests:

  parse_spec_constant 1;
  parse_spec_constant -1;
  parse_spec_constant 1.5;
  parse_spec_constant -1.5;
  parse_spec_constant "test";
-/
triptych SpecConstant where
  grammar
    SpecConstant  ::= StringLiteral | NumericLiteral
    StringLiteral ::= str
    NumericLiteral ::= Sign Natural [DecimalPart]
    Sign           ::= sign
    Natural        ::= digit+
    DecimalPart    ::= "." Fraction
    Fraction       ::= digit+
  value'
    toValue StringLiteral Sign Natural Fraction
  to "Outputs/SMT/SpecConstant"

#guard SpecConstant.parse "1" = some (.numeral 1)
#guard SpecConstant.parse "-1" = some (.numeralNeg 1)
#guard SpecConstant.parse "1.5" =
  some (.decimal { mantissa := 15, exponent := -1 })
#guard SpecConstant.parse "-1.5" =
  some (.decimalNeg { mantissa := 15, exponent := -1 })
#guard SpecConstant.parse "\"test\"" = some (.string "test")

end StrataExamples.SMT.SpecConstant
