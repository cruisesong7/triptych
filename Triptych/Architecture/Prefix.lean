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

import Triptych.Architecture.Denote

/-!
# Shared prefix recognition

These leaf checks are shared by the runtime scanner and the archived reference decoder. Keeping
them outside the archive makes the scanner executable without importing the list-producing
reference implementation.
-/

namespace Triptych

/-- Does the length-`k` prefix of `cs` satisfy the terminal `tok`/`ls`? -/
def termPrefixOk (tok : TokClass) (ls : LenSpec) (cs : List Char) (k : Nat) : Bool :=
  k ≤ cs.length && decide (matchesTerm tok ls (String.ofList (cs.take k)))

/-- Does the length-`k` prefix of `cs` form a complete quoted string literal? -/
def stringPrefixOk (cs : List Char) (k : Nat) : Bool :=
  k ≤ cs.length && decide (IsStringLiteral (String.ofList (cs.take k)))

end Triptych
