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

import Outputs.Lrat.parser

/-!
# LRAT conformance against `Std`

Differential check of the generated verified parser against
`Std.Tactic.BVDecide.LRAT.parseLRATProof` on text proofs. Both return `Array IntAction`, so each
case compares the two results directly. Round-trip cases render action arrays with `Std`'s own
`lratProofToString` and require both parsers to recover them.

`Std`'s parser is assembled from `partial` definitions, so its behavior cannot be proved; this
suite is the available evidence. Comment lines are excluded because the Triptych grammar does
not yet cover them.
-/

namespace LratExample.Conformance

open Std.Tactic.BVDecide.LRAT

/-- `Std`'s result, with its error message dropped. -/
def stdParse (text : String) : Option (Array IntAction) :=
  match parseLRATProof text.toUTF8 with
  | .ok actions => some actions
  | .error _ => none

def corpus : List String := [
  -- additions, deletions, RUP and RAT steps
  "5 1 -2 0 3 4 0\n6 d 1 2 0\n",
  "7 1 2 0 5 -3 1 2 -4 6 0\n",
  "7 0 5 6 0\n",
  "7 0 0\n",
  "8 3 0 0\n",
  "9 1 0 -3 0\n",
  "9 1 0 2 -3 -4 5 0\n",
  "10 d 0\n",
  "11 -1 -2 -3 0 1 2 3 0\n",
  -- leading zeros and Windows line endings
  "007 01 -02 0 03 0\n",
  "5 1 0 2 0\r\n6 d 3 0\r\n",
  -- rejected: zero ids or literals, empty clause with RAT hints, layout errors
  "0 1 0 2 0\n",
  "5 0 0 0\n",
  "5 00 0 2 0\n",
  "7 0 -3 1 0\n",
  "5 1 0 2 0",
  "",
  "5  1 0 2 0\n",
  "5 1 0 2 0 \n",
  "5 1 0 2\n",
  "5 d1 0\n",
  "5 1 0 2 0\n\n",
  "x 1 0 2 0\n",
  "5 1 0 -0 0\n"
]

/-- Action arrays rendered by `Std`'s text printer. -/
def printed : List (Array IntAction) := [
  #[.addRup 3 #[1, -2] #[1, 2]],
  #[.addEmpty 9 #[4, 5, 6], .del #[1, 2, 3]],
  #[.addRat 12 #[-4, 5] (4, false) #[1] #[(2, #[3]), (7, #[])]],
  #[.del #[], .addRup 1 #[1] #[]]
]

def cases : List String := corpus ++ printed.map lratProofToString

def failures : List String :=
  cases.filter fun text => Lrat.parse text != stdParse text

#eval do
  let accepted := (cases.filter fun text => (stdParse text).isSome).length
  IO.println s!"LRAT generated vs Std: {cases.length - failures.length}/{cases.length} agree \
    ({accepted} accepted by Std)"
  for text in failures do
    IO.println s!"  mismatch on {repr text}: generated={repr (Lrat.parse text)} \
      Std={repr (stdParse text)}"
  if !failures.isEmpty then
    throw <| IO.userError s!"{failures.length} LRAT conformance failures"

-- Every printed action array is recovered exactly by the generated parser.
#guard printed.all fun actions => Lrat.parse (lratProofToString actions) == some actions

end LratExample.Conformance
