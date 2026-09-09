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

import Inputs.Graph
import Triptych.Architecture.Dependent

/-!
# Graph6 as a dependent format

A Graph6 value begins with a one-, four-, or eight-character order header. The decoded vertex
count `n` determines the exact payload width `ceil(n * (n - 1) / 2 / 6)`. This cannot be modeled
as a fixed-boundary Triptych grammar: the header must be parsed before the payload grammar is
known.

`graph6HeaderGrammar` remains an ordinary Triptych grammar. `graph6PayloadGrammar` constructs
another ordinary grammar from the captured header. `scanDependent` composes the two stages while
preserving the header's source-ordered alternatives.
-/

namespace Graph6Example

open Triptych

private def graph6Alphabet : TokClass :=
  .asciiRange 63 126

/-- Decode one Graph6 alphabet character to its six-bit value. -/
def graph6Digit? (c : Char) : Option Nat :=
  if 63 ≤ c.toNat && c.toNat ≤ 126 then some (c.toNat - 63) else none

private def decodeBase64Digits : List Char → Option Nat
  | [] => some 0
  | c :: cs => do
      let head ← graph6Digit? c
      let tail ← decodeBase64Digits cs
      return head * 64 ^ cs.length + tail

/-- Decode the Graph6 order header. The three cases are intentionally disjoint by their numeric
    ranges, so a leading `~` cannot be mistaken for a complete short header. -/
def graph6Order? (header : String) : Option Nat :=
  match header.toList with
  | [c] => do
      let n ← graph6Digit? c
      if n ≤ 62 then some n else none
  | '~' :: a :: b :: c :: [] => do
      let n ← decodeBase64Digits [a, b, c]
      if 63 ≤ n && n ≤ 258047 then some n else none
  | '~' :: '~' :: a :: b :: c :: d :: e :: f :: [] => do
      let n ← decodeBase64Digits [a, b, c, d, e, f]
      if 258048 ≤ n then some n else none
  | _ => none

/-- Number of six-bit Graph6 payload characters required for a graph of order `n`. -/
def graph6PayloadLength (n : Nat) : Nat :=
  (n * (n - 1) / 2 + 5) / 6

/-- Grammar for the one-, four-, or eight-character Graph6 order header. -/
def graph6HeaderGrammar : Grammar where
  start := "Start"
  prods := [
    {
      name := "Start"
      alts := [[{ sym := .ref "Header" }]]
    },
    {
      name := "Header"
      alts := [
        [{ sym := .term graph6Alphabet (.exactly 1) }],
        [{ sym := .lit "~" }, { sym := .term graph6Alphabet (.exactly 3) }],
        [{ sym := .lit "~~" }, { sym := .term graph6Alphabet (.exactly 6) }]
      ]
    }
  ]

private def rejectingGrammar : Grammar where
  start := "Reject"
  prods := []

private def payloadGrammar (width : Nat) : Grammar where
  start := "Start"
  prods := [
    {
      name := "Start"
      alts := [[{ sym := .ref "Payload" }]]
    },
    {
      name := "Payload"
      alts := [[{ sym := .term graph6Alphabet (.exactly width) }]]
    }
  ]

/-- Instantiate the exact payload grammar selected by a decoded header. -/
def graph6PayloadGrammar (captures : CaptureMap) : Grammar :=
  match captures.toEnv "Header" >>= graph6Order? with
  | none => rejectingGrammar
  | some order => payloadGrammar (graph6PayloadLength order)

/-- Parse one Graph6 encoding into its lossless header and payload captures. -/
def parseView (input : String) : Option CaptureMap :=
  scanDependent graph6HeaderGrammar graph6PayloadGrammar input

private def graph6Bits (payload : String) : Option (List Bool) := do
  let digits ← payload.toList.mapM graph6Digit?
  return digits.flatMap fun sixBits =>
    (List.range 6).map fun shift => sixBits.testBit (5 - shift)

private def upperTrianglePairs (order : Nat) : List (Nat × Nat) :=
  (List.range order).flatMap fun upper =>
    (List.range upper).map fun lower => (lower, upper)

/-- Interpret a lossless Graph6 view as the structured graph used by the existing Graph example. -/
def graphOfCaptures (captures : CaptureMap) : Option GraphExample.Graph := do
  let header ← captures.toEnv "Header"
  let payload ← captures.toEnv "Payload"
  let order ← graph6Order? header
  let bits ← graph6Bits payload
  let bitCount := order * (order - 1) / 2
  guard <| (bits.drop bitCount).all not
  let edges :=
    ((upperTrianglePairs order).zip (bits.take bitCount)).filterMap fun (edge, present) =>
      if present then some edge else none
  return { order, edges }

/-- Parse and interpret one Graph6 graph. -/
def parse (input : String) : Option GraphExample.Graph :=
  parseView input >>= graphOfCaptures

end Graph6Example
