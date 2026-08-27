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

/-!
# SMT-LIB bit-vector literals

An acyclic reference grammar for binary (`#b...`) and hexadecimal (`#x...`) literals.
-/

namespace StrataExamples.SMT.BitVector
open Triptych

inductive Radix where
  | binary
  | hexadecimal
  deriving Repr, DecidableEq, Inhabited

/-- A bit-vector literal with its radix and exact source digits preserved. -/
structure Value where
  radix : Radix
  digits : String
  deriving Repr, DecidableEq, Inhabited

def toValue (binary hexadecimal : String) : Value :=
  if binary.isEmpty then
    { radix := .hexadecimal, digits := hexadecimal }
  else
    { radix := .binary, digits := binary }

/-- Render the literal with the prefix selected by its stored radix. -/
def serialize : Value → String
  | { radix := .binary, digits } => "#b" ++ digits
  | { radix := .hexadecimal, digits } => "#x" ++ digits

/-
Corresponding Strata source:

  // <hexadecimal> and <binary> are not available yet.

Strata currently has no parser tests for these forms.
-/
triptych BitVector where
  grammar
    BitVector    ::= "#" Payload
    Payload      ::= Binary | Hexadecimal
    Binary       ::= "b" BinaryDigits
    Hexadecimal  ::= "x" HexDigits
    BinaryDigits ::= bit+
    HexDigits    ::= hexDigit+
  value'
    toValue BinaryDigits HexDigits
  to "Outputs/SMT/BitVector"

end StrataExamples.SMT.BitVector
