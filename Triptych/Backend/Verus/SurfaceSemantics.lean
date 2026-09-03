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

import Triptych.Backend.Verus.Desugar

/-!
# Semantics of Verus surface helpers

This module interprets the first-order `Verus.Surface` fragment used by generated helper functions.
Text values are lists of bytes, matching Verus `Seq<u8>`. Calls are interpreted by a canonical
environment whose definitions are connected to Triptych's audited Lean readers.

The helper-realization theorems evaluate the bodies returned by `helperDeclaration`; they do not
merely restate the intended meaning of the higher-level semantic AST.
-/

namespace Triptych.Backend.Verus.Surface

inductive Value where
  | bool (data : Bool)
  | int (data : Int)
  | byte (data : Nat)
  | text (data : List Nat)
  deriving Repr, DecidableEq

abbrev EvalEnv := String → Option Value
abbrev CallEnv := String → List Value → Option Value

@[simp]
def Value.asBool : Value → Option Bool
  | .bool data => some data
  | _ => none

@[simp]
def Value.asInt : Value → Option Int
  | .int data => some data
  | _ => none

@[simp]
def Value.asByte : Value → Option Nat
  | .byte data => some data
  | _ => none

@[simp]
def Value.asText : Value → Option (List Nat)
  | .text data => some data
  | _ => none

def encodeString (source : String) : List Nat :=
  source.toList.map Char.toNat

@[simp]
def nonnegativeNat? (data : Int) : Option Nat :=
  if 0 ≤ data then some data.toNat else none

@[simp]
theorem nonnegativeNat_ofNat (data : Nat) :
    nonnegativeNat? (Int.ofNat data) = some data := by
  simp [nonnegativeNat?]

@[simp]
theorem nonnegativeNat_ofNat_add_one (data : Nat) :
    nonnegativeNat? (Int.ofNat data + 1) = some (data + 1) := by
  simp [nonnegativeNat?]
  omega

@[simp]
theorem optionBind_if {α β : Type} (proposition : Prop) [Decidable proposition]
    (thenBranch elseBranch : Option α) (continuation : α → Option β) :
    (if proposition then thenBranch else elseBranch).bind continuation =
      if proposition then thenBranch.bind continuation else elseBranch.bind continuation := by
  by_cases proposition <;> simp_all

@[simp]
theorem someBool_and (left right : Bool) :
    (if left then some (Value.bool right) else some (Value.bool false)) =
      some (Value.bool (left && right)) := by
  cases left <;> rfl

@[simp]
theorem someBool_or (left right : Bool) :
    (if left then some (Value.bool true) else some (Value.bool right)) =
      some (Value.bool (left || right)) := by
  cases left <;> rfl

@[simp]
theorem ifProp_someBool_and (proposition : Prop) [Decidable proposition] (right : Bool) :
    (if proposition then some (Value.bool right) else some (Value.bool false)) =
      some (Value.bool (decide proposition && right)) := by
  by_cases proposition <;> simp_all

@[simp]
theorem ifProp_someBool_or (proposition : Prop) [Decidable proposition] (right : Bool) :
    (if proposition then some (Value.bool true) else some (Value.bool right)) =
      some (Value.bool (decide proposition || right)) := by
  by_cases proposition <;> simp_all

def Expr.denote (calls : CallEnv) (env : EvalEnv) : Surface.Expr → Option Value
  | .var name => env name
  | .boolLit literal => some (.bool literal)
  | .intLit literal => some (.int literal)
  | .byteLit literal => some (.byte literal)
  | .textLit literal => some (.text (encodeString literal))
  | .optionNone | .optionSome _ | .field _ _ => none
  | .call name args => do
      let values ← args.mapM (Expr.denote calls env)
      calls name values
  | .textConcat left right => do
      let left ← (← left.denote calls env).asText
      let right ← (← right.denote calls env).asText
      pure (.text (left ++ right))
  | .intAdd left right => do
      let left ← (← left.denote calls env).asInt
      let right ← (← right.denote calls env).asInt
      pure (.int (left + right))
  | .intSub left right => do
      let left ← (← left.denote calls env).asInt
      let right ← (← right.denote calls env).asInt
      pure (.int (left - right))
  | .intMul left right => do
      let left ← (← left.denote calls env).asInt
      let right ← (← right.denote calls env).asInt
      pure (.int (left * right))
  | .intNeg expression => do
      let data ← (← expression.denote calls env).asInt
      pure (.int (-data))
  | .textLen expression => do
      let data ← (← expression.denote calls env).asText
      pure (.int (Int.ofNat data.length))
  | .textIndex expression index => do
      let data ← (← expression.denote calls env).asText
      let index ← (← index.denote calls env).asInt
      let index ← nonnegativeNat? index
      pure (.byte (← data[index]?))
  | .textSubrange expression start stop => do
      let data ← (← expression.denote calls env).asText
      let start ← (← start.denote calls env).asInt
      let stop ← (← stop.denote calls env).asInt
      let start ← nonnegativeNat? start
      let stop ← nonnegativeNat? stop
      if start ≤ stop ∧ stop ≤ data.length then
        pure (.text ((data.drop start).take (stop - start)))
      else
        none
  | .byteToInt expression => do
      let data ← (← expression.denote calls env).asByte
      pure (.int (Int.ofNat data))
  | .boolNot expression => do
      let data ← (← expression.denote calls env).asBool
      pure (.bool (!data))
  | .boolAnd left right => do
      let left ← (← left.denote calls env).asBool
      if left then
        let right ← (← right.denote calls env).asBool
        pure (.bool right)
      else
        pure (.bool false)
  | .boolOr left right => do
      let left ← (← left.denote calls env).asBool
      if left then
        pure (.bool true)
      else
        let right ← (← right.denote calls env).asBool
        pure (.bool right)
  | .boolImplies left right => do
      let left ← (← left.denote calls env).asBool
      if left then
        let right ← (← right.denote calls env).asBool
        pure (.bool right)
      else
        pure (.bool true)
  | .intEq left right => do
      let left ← (← left.denote calls env).asInt
      let right ← (← right.denote calls env).asInt
      pure (.bool (decide (left = right)))
  | .intNe left right => do
      let left ← (← left.denote calls env).asInt
      let right ← (← right.denote calls env).asInt
      pure (.bool (decide (left ≠ right)))
  | .intLt left right => do
      let left ← (← left.denote calls env).asInt
      let right ← (← right.denote calls env).asInt
      pure (.bool (decide (left < right)))
  | .intLe left right => do
      let left ← (← left.denote calls env).asInt
      let right ← (← right.denote calls env).asInt
      pure (.bool (decide (left ≤ right)))
  | .intGt left right => do
      let left ← (← left.denote calls env).asInt
      let right ← (← right.denote calls env).asInt
      pure (.bool (decide (left > right)))
  | .intGe left right => do
      let left ← (← left.denote calls env).asInt
      let right ← (← right.denote calls env).asInt
      pure (.bool (decide (left ≥ right)))
  | .byteEq left right => do
      let left ← (← left.denote calls env).asByte
      let right ← (← right.denote calls env).asByte
      pure (.bool (decide (left = right)))
  | .byteNe left right => do
      let left ← (← left.denote calls env).asByte
      let right ← (← right.denote calls env).asByte
      pure (.bool (decide (left ≠ right)))
  | .textEq left right => do
      let left ← (← left.denote calls env).asText
      let right ← (← right.denote calls env).asText
      pure (.bool (decide (left = right)))
  | .textNe left right => do
      let left ← (← left.denote calls env).asText
      let right ← (← right.denote calls env).asText
      pure (.bool (decide (left ≠ right)))
  | .ifThenElse condition thenBranch elseBranch => do
      let condition ← (← condition.denote calls env).asBool
      if condition then thenBranch.denote calls env else elseBranch.denote calls env
  | .forallE _ _ _ | .existsE _ _ | .choose _ _ | .matchOption _ _ _ _ => none

end Triptych.Backend.Verus.Surface

namespace Triptych.Backend.Verus

open Surface

def digitValue (byte : Nat) : Int :=
  if Int.ofNat byte < 48 then 0 else Int.ofNat byte - 48

theorem digitValue_eq_ofNatSub (byte : Nat) :
    digitValue byte = Int.ofNat (byte - 48) := by
  unfold digitValue
  split
  · rename_i hbyte
    have hnat : byte < 48 := Int.ofNat_lt.mp hbyte
    have hzero : byte - 48 = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hnat)
    simp [hzero]
  · rename_i hbyte
    have hleInt : (48 : Int) ≤ Int.ofNat byte := Int.not_lt.mp hbyte
    have hle : 48 ≤ byte := Int.ofNat_le.mp hleInt
    exact (Int.ofNat_sub hle).symm

def foldDigitBytes (bytes : List Nat) (accumulator : Int) : Int :=
  bytes.foldl (fun acc byte => acc * 10 + digitValue byte) accumulator

def natOfBytesFrom (bytes : List Nat) (index : Nat) (accumulator : Int) : Int :=
  foldDigitBytes (bytes.drop index) accumulator

def natOfBytes (bytes : List Nat) : Int :=
  natOfBytesFrom bytes 0 0

def intOfBytes : List Nat → Int
  | 45 :: rest => -natOfBytes rest
  | bytes => natOfBytes bytes

def signOfBytes : List Nat → Int
  | 45 :: _ => -1
  | _ => 1

def intPowModel (base exponent : Int) : Int :=
  base ^ exponent.toNat

def isDigitByte (byte : Nat) : Bool :=
  decide ((48 : Int) ≤ Int.ofNat byte) && decide (Int.ofNat byte ≤ 57)

def isHexDigitByte (byte : Nat) : Bool :=
  isDigitByte byte ||
    ((decide ((65 : Int) ≤ Int.ofNat byte) && decide (Int.ofNat byte ≤ 70)) ||
     (decide ((97 : Int) ≤ Int.ofNat byte) && decide (Int.ofNat byte ≤ 102)))

def isBitByte (byte : Nat) : Bool :=
  decide (byte = 48) || decide (byte = 49)

def canonicalCalls : Surface.CallEnv
  | "triptych_is_digit", [.byte byte] =>
      some (.bool (isDigitByte byte))
  | "triptych_is_hex_digit", [.byte byte] =>
      some (.bool (isHexDigitByte byte))
  | "triptych_is_bit", [.byte byte] =>
      some (.bool (isBitByte byte))
  | "triptych_nat_of_from", [.text bytes, .int index, .int accumulator] =>
      if 0 ≤ index then
        some (.int (natOfBytesFrom bytes index.toNat accumulator))
      else
        none
  | "triptych_nat_of", [.text bytes] =>
      some (.int (natOfBytes bytes))
  | "triptych_int_of", [.text bytes] =>
      some (.int (intOfBytes bytes))
  | "triptych_sign_of", [.text bytes] =>
      some (.int (signOfBytes bytes))
  | "triptych_int_pow", [.int base, .int exponent] =>
      some (.int (intPowModel base exponent))
  | _, _ => none

@[simp]
theorem canonicalCalls_isDigit (byte : Nat) :
    canonicalCalls "triptych_is_digit" [.byte byte] = some (.bool (isDigitByte byte)) := by
  rfl

@[simp]
theorem canonicalCalls_isHexDigit (byte : Nat) :
    canonicalCalls "triptych_is_hex_digit" [.byte byte] =
      some (.bool (isHexDigitByte byte)) := by
  rfl

@[simp]
theorem canonicalCalls_isBit (byte : Nat) :
    canonicalCalls "triptych_is_bit" [.byte byte] = some (.bool (isBitByte byte)) := by
  rfl

@[simp]
theorem canonicalCalls_natOfFrom (bytes : List Nat) (index : Nat) (accumulator : Int) :
    canonicalCalls "triptych_nat_of_from"
      [.text bytes, .int (Int.ofNat index), .int accumulator] =
        some (.int (natOfBytesFrom bytes index accumulator)) := by
  simp [canonicalCalls]

@[simp]
theorem canonicalCalls_natOfFrom_zero (bytes : List Nat) (accumulator : Int) :
    canonicalCalls "triptych_nat_of_from"
      [.text bytes, .int 0, .int accumulator] =
        some (.int (natOfBytesFrom bytes 0 accumulator)) := by
  simp [canonicalCalls]

@[simp]
theorem canonicalCalls_natOfFrom_addOne (bytes : List Nat) (index : Nat)
    (accumulator : Int) :
    canonicalCalls "triptych_nat_of_from"
      [.text bytes, .int (Int.ofNat index + 1), .int accumulator] =
        some (.int (natOfBytesFrom bytes (index + 1) accumulator)) := by
  simp [canonicalCalls]
  omega

@[simp]
theorem canonicalCalls_natOf (bytes : List Nat) :
    canonicalCalls "triptych_nat_of" [.text bytes] = some (.int (natOfBytes bytes)) := by
  rfl

@[simp]
theorem canonicalCalls_intOf (bytes : List Nat) :
    canonicalCalls "triptych_int_of" [.text bytes] = some (.int (intOfBytes bytes)) := by
  rfl

@[simp]
theorem canonicalCalls_signOf (bytes : List Nat) :
    canonicalCalls "triptych_sign_of" [.text bytes] = some (.int (signOfBytes bytes)) := by
  rfl

@[simp]
theorem canonicalCalls_intPow (base exponent : Int) :
    canonicalCalls "triptych_int_pow" [.int base, .int exponent] =
      some (.int (intPowModel base exponent)) := by
  rfl

private def bindingEnv (bindings : List (String × Surface.Value)) : Surface.EvalEnv :=
  fun name => (bindings.find? (·.1 == name)).map (·.2)

private def bindParams : List Surface.Param → List Surface.Value →
    Option (List (String × Surface.Value))
  | [], [] => some []
  | param :: params, argument :: arguments => do
      pure ((param.name, argument) :: (← bindParams params arguments))
  | _, _ => none

private def helperConstants : List (String × Surface.Value) :=
  [("TRIPTYCH_MINUS", .byte 45), ("TRIPTYCH_ZERO", .byte 48)]

def evaluateHelper (helper : Helper) (arguments : List Surface.Value) : Option Surface.Value :=
  match helperDeclaration helper with
  | .function function => do
      let bindings ← bindParams function.params arguments
      function.body.denote canonicalCalls (bindingEnv (bindings ++ helperConstants))
  | .constant constant =>
      if arguments.isEmpty then
        constant.initializer.denote canonicalCalls (bindingEnv helperConstants)
      else
        none
  | .structure _ | .trait _ => none

@[simp]
theorem natOfBytesFrom_step (bytes : List Nat) (index : Nat) (accumulator : Int)
    (hindex : index < bytes.length) :
    natOfBytesFrom bytes index accumulator =
      natOfBytesFrom bytes (index + 1)
        (accumulator * 10 + digitValue bytes[index]) := by
  simp only [natOfBytesFrom, foldDigitBytes]
  rw [List.drop_eq_getElem_cons hindex]
  rfl

@[simp]
theorem natOfBytesFrom_end (bytes : List Nat) (index : Nat) (accumulator : Int)
    (hindex : bytes.length ≤ index) :
    natOfBytesFrom bytes index accumulator = accumulator := by
  simp [natOfBytesFrom, foldDigitBytes, List.drop_eq_nil_of_le hindex]

private theorem foldDigitBytes_ofNat (bytes : List Nat) (accumulator : Nat) :
    foldDigitBytes bytes (Int.ofNat accumulator) =
      Int.ofNat
        (bytes.foldl (fun acc byte => acc * 10 + (byte - 48)) accumulator) := by
  induction bytes generalizing accumulator with
  | nil => rfl
  | cons byte bytes ih =>
      simp only [foldDigitBytes, List.foldl_cons]
      rw [show Int.ofNat accumulator * 10 + digitValue byte =
          Int.ofNat (accumulator * 10 + (byte - 48)) by
        simp [digitValue_eq_ofNatSub]]
      exact ih (accumulator * 10 + (byte - 48))

@[simp]
theorem natOfBytes_map_toNat (characters : List Char) :
    natOfBytes (characters.map Char.toNat) = Int.ofNat (Triptych.readNatChars characters) := by
  change foldDigitBytes (characters.map Char.toNat) (Int.ofNat 0) =
    Int.ofNat (Triptych.readNatChars characters)
  rw [foldDigitBytes_ofNat]
  simp [Triptych.readNatChars, List.foldl_map]

@[simp]
theorem natOfBytes_encodeString (source : String) :
    natOfBytes (Surface.encodeString source) = Triptych.natOf source := by
  simp [Surface.encodeString, Triptych.natOf, Triptych.readNat_eq_readNatChars]

@[simp]
theorem encodeString_empty : Surface.encodeString "" = [] := by
  rfl

@[simp]
theorem intOfBytes_encodeString (source : String) :
    intOfBytes (Surface.encodeString source) = Triptych.intOf source := by
  cases hsource : source.toList with
  | nil =>
      have hempty : source = "" := by
        apply String.ext
        simp [hsource]
      subst source
      simp [intOfBytes, Triptych.intOf, natOfBytes, natOfBytesFrom,
        foldDigitBytes]
  | cons character rest =>
      have hnonempty : source ≠ "" := by
        intro heq
        subst source
        simp at hsource
      by_cases hminus : character = '-'
      · subst character
        calc
          intOfBytes (Surface.encodeString source) =
              -natOfBytes (rest.map Char.toNat) := by
            simp [Surface.encodeString, hsource, intOfBytes]
          _ = -Int.ofNat (Triptych.readNatChars rest) := by
            rw [natOfBytes_map_toNat]
          _ = Triptych.intOf source := by
            simp [Triptych.intOf, hnonempty, Triptych.readInt, hsource,
              String.startsWith_string_iff, Triptych.readNat_eq_readNatChars]
      · have hcode : character.toNat ≠ 45 := by
          intro h
          apply hminus
          exact Char.toNat_inj.mp h
        have hminus' : '-' ≠ character := Ne.symm hminus
        calc
          intOfBytes (Surface.encodeString source) =
              natOfBytes ((character :: rest).map Char.toNat) := by
            simp [Surface.encodeString, hsource, intOfBytes, hcode]
          _ = Int.ofNat (Triptych.readNatChars (character :: rest)) :=
            natOfBytes_map_toNat (character :: rest)
          _ = Triptych.intOf source := by
            simp [Triptych.intOf, hnonempty, Triptych.readInt, hsource,
              hminus', String.startsWith_string_iff, Triptych.readNat_eq_readNatChars]

@[simp]
theorem signOfBytes_encodeString (source : String) :
    signOfBytes (Surface.encodeString source) = Triptych.signOf source := by
  simp only [Surface.encodeString, Triptych.signOf]
  cases hsource : source.toList with
  | nil => simp [signOfBytes, String.startsWith_string_iff, hsource]
  | cons character rest =>
      by_cases hminus : character = '-'
      · subst character
        simp [signOfBytes, String.startsWith_string_iff, hsource]
      · have hcode : character.toNat ≠ 45 := by
          intro h
          apply hminus
          exact Char.toNat_inj.mp h
        have hminus' : '-' ≠ character := Ne.symm hminus
        simp [hminus', hcode, signOfBytes, String.startsWith_string_iff, hsource]

@[simp]
theorem evaluateHelper_minusConstant :
    evaluateHelper .minusConstant [] = some (.byte 45) := by
  simp [evaluateHelper, helperDeclaration, helperConstants, Surface.Expr.denote]

@[simp]
theorem evaluateHelper_zeroConstant :
    evaluateHelper .zeroConstant [] = some (.byte 48) := by
  simp [evaluateHelper, helperDeclaration, helperConstants, Surface.Expr.denote]

@[simp]
theorem evaluateHelper_isDigit (byte : Nat) :
    evaluateHelper .isDigit [.byte byte] =
      some (.bool (isDigitByte byte)) := by
  simp [evaluateHelper, helperDeclaration, Surface.Expr.denote, bindingEnv, bindParams,
    helperConstants, helperBoolFunction, isDigitByte]

@[simp]
theorem evaluateHelper_isHexDigit (byte : Nat) :
    evaluateHelper .isHexDigit [.byte byte] =
      some (.bool (isHexDigitByte byte)) := by
  simp [evaluateHelper, helperDeclaration, Surface.Expr.denote, bindingEnv, bindParams,
    helperConstants, helperBoolFunction, isHexDigitByte, isDigitByte]

@[simp]
theorem evaluateHelper_isBit (byte : Nat) :
    evaluateHelper .isBit [.byte byte] =
      some (.bool (isBitByte byte)) := by
  simp [evaluateHelper, helperDeclaration, Surface.Expr.denote, bindingEnv, bindParams,
    helperConstants, helperBoolFunction, isBitByte]

@[simp]
theorem evaluateHelper_natOfFrom (bytes : List Nat) (index : Nat) (accumulator : Int)
    (hindex : index ≤ bytes.length) :
    evaluateHelper .natOfFrom [.text bytes, .int (Int.ofNat index), .int accumulator] =
      some (.int (natOfBytesFrom bytes index accumulator)) := by
  by_cases hlt : index < bytes.length
  · rw [natOfBytesFrom_step bytes index accumulator hlt]
    by_cases hbyte : (bytes[index] : Int) < 48
    · simp [evaluateHelper, helperDeclaration, Surface.Expr.denote, bindingEnv, bindParams,
        helperConstants, Surface.nonnegativeNat?, digitValue, hlt, hbyte]
      simp [canonicalCalls]
      omega
    · simp [evaluateHelper, helperDeclaration, Surface.Expr.denote, bindingEnv, bindParams,
        helperConstants, Surface.nonnegativeNat?, digitValue, hlt, hbyte]
      simp [canonicalCalls]
      omega
  · have heq : index = bytes.length := by omega
    subst index
    simp [evaluateHelper, helperDeclaration, Surface.Expr.denote, bindingEnv, bindParams,
      helperConstants, Surface.nonnegativeNat?, natOfBytesFrom_end]

@[simp]
theorem evaluateHelper_natOf (bytes : List Nat) :
    evaluateHelper .natOf [.text bytes] = some (.int (natOfBytes bytes)) := by
  simp [evaluateHelper, helperDeclaration, helperIntFunction, Surface.Expr.denote, bindParams,
    bindingEnv, helperConstants, natOfBytes]

@[simp]
theorem evaluateHelper_intOf (bytes : List Nat) :
    evaluateHelper .intOf [.text bytes] = some (.int (intOfBytes bytes)) := by
  cases bytes with
  | nil =>
      simp [evaluateHelper, helperDeclaration, Surface.Expr.denote, bindingEnv, bindParams,
        helperConstants, helperIntFunction, intOfBytes, natOfBytes,
        natOfBytesFrom, foldDigitBytes]
  | cons byte rest =>
      by_cases hminus : byte = 45
      · subst byte
        simp [evaluateHelper, helperDeclaration, Surface.Expr.denote, bindingEnv, bindParams,
          helperConstants, helperIntFunction, intOfBytes, List.take_length] <;>
          omega
      · simp [evaluateHelper, helperDeclaration, Surface.Expr.denote, bindingEnv, bindParams,
          helperConstants, helperIntFunction, intOfBytes, hminus]

@[simp]
theorem evaluateHelper_signOf (bytes : List Nat) :
    evaluateHelper .signOf [.text bytes] = some (.int (signOfBytes bytes)) := by
  cases bytes with
  | nil =>
      simp [evaluateHelper, helperDeclaration, Surface.Expr.denote, bindingEnv, bindParams,
        helperConstants, helperIntFunction, signOfBytes]
  | cons byte rest =>
      by_cases hminus : byte = 45
      · subst byte
        simp [evaluateHelper, helperDeclaration, Surface.Expr.denote, bindingEnv, bindParams,
          helperConstants, helperIntFunction, signOfBytes]
      · simp [evaluateHelper, helperDeclaration, Surface.Expr.denote, bindingEnv, bindParams,
          helperConstants, helperIntFunction, signOfBytes, hminus]

private theorem intPowModel_step (base exponent : Int) (hpositive : 0 < exponent) :
    base * intPowModel base (exponent - 1) = intPowModel base exponent := by
  cases exponent with
  | ofNat exponent =>
      cases exponent with
      | zero => simp at hpositive
      | succ exponent =>
          simp [intPowModel, Int.pow_succ, Int.mul_comm]
  | negSucc exponent => simp at hpositive

@[simp]
theorem evaluateHelper_intPow (base exponent : Int) :
    evaluateHelper .intPow [.int base, .int exponent] =
      some (.int (intPowModel base exponent)) := by
  by_cases hpositive : 0 < exponent
  · simp [evaluateHelper, helperDeclaration, Surface.Expr.denote, bindingEnv, bindParams,
      helperConstants, hpositive,
      intPowModel_step base exponent hpositive]
  · have hnonpositive : exponent ≤ 0 := by omega
    simp [evaluateHelper, helperDeclaration, Surface.Expr.denote, bindingEnv, bindParams,
      helperConstants, hpositive, intPowModel,
      Int.toNat_of_nonpos hnonpositive]

def Helper.Realizes : Helper → Prop
  | .minusConstant => evaluateHelper .minusConstant [] = some (.byte 45)
  | .zeroConstant => evaluateHelper .zeroConstant [] = some (.byte 48)
  | .isDigit =>
      ∀ byte, evaluateHelper .isDigit [.byte byte] =
        some (.bool (isDigitByte byte))
  | .isHexDigit =>
      ∀ byte, evaluateHelper .isHexDigit [.byte byte] =
        some (.bool (isHexDigitByte byte))
  | .isBit =>
      ∀ byte, evaluateHelper .isBit [.byte byte] =
        some (.bool (isBitByte byte))
  | .natOfFrom =>
      ∀ (bytes : List Nat) (index : Nat) (accumulator : Int), index ≤ bytes.length →
        evaluateHelper .natOfFrom
          [.text bytes, .int (Int.ofNat index), .int accumulator] =
            some (.int (natOfBytesFrom bytes index accumulator))
  | .natOf =>
      ∀ bytes, evaluateHelper .natOf [.text bytes] = some (.int (natOfBytes bytes))
  | .intOf =>
      ∀ bytes, evaluateHelper .intOf [.text bytes] = some (.int (intOfBytes bytes))
  | .signOf =>
      ∀ bytes, evaluateHelper .signOf [.text bytes] = some (.int (signOfBytes bytes))
  | .intPow =>
      ∀ base exponent, evaluateHelper .intPow [.int base, .int exponent] =
        some (.int (intPowModel base exponent))

theorem helperDeclaration_realizes (helper : Helper) : helper.Realizes := by
  cases helper with
  | minusConstant => exact evaluateHelper_minusConstant
  | zeroConstant => exact evaluateHelper_zeroConstant
  | isDigit => exact evaluateHelper_isDigit
  | isHexDigit => exact evaluateHelper_isHexDigit
  | isBit => exact evaluateHelper_isBit
  | natOfFrom => exact evaluateHelper_natOfFrom
  | natOf => exact evaluateHelper_natOf
  | intOf => exact evaluateHelper_intOf
  | signOf => exact evaluateHelper_signOf
  | intPow => exact evaluateHelper_intPow

end Triptych.Backend.Verus
