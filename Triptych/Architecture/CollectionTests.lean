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
# Analyzable collection tests

Character sets, separator-free repetition, list comprehensions in `value`, and `forall`
constraints. Kept apart from `SyntaxTests`, whose source the documentation build highlights.
-/

namespace Triptych.Tests

namespace AnalyzableCollectionsExample

/-! Character sets, separator-free repetition, list comprehensions in `value`, and `forall`
    constraints, all inside the analyzable DSL. -/

triptych Rows where
  grammar
    Table ::= Width rep Row +
    Width ::= digit+
    Row   ::= Ws rep CellWs + ";"
    CellWs ::= Cell Ws
    Cell  ::= digit+
    Ws    ::= oneOf " \t"+
  value
    [Row ↦ [Cell ↦ nat Cell]]
  constraints
    forall Cell, nat Cell ≤ nat Width

#guard Rows.parse "9 1 2 ;\t3 ;" = some [[1, 2], [3]]
#guard Rows.parse "2 1 3 ;" = none
#guard Rows.parse "9 1 2;" = none

/--
error: a separator-free repetition `rep X …` needs an item that always consumes input: some required part of every alternative of `X` must be a non-empty literal, a token run of length at least one, or another consuming reference
-/
#guard_msgs in
triptych NullableItems where
  grammar
    Doc  ::= rep Item +
    Item ::= [Cell]
    Cell ::= digit+
  value
    [Item ↦ nat Cell]

end AnalyzableCollectionsExample

end Triptych.Tests
