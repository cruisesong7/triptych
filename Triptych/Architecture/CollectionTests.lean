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


namespace GroupBoundaryExample

/-! Review regressions: a group ends at its occurrence even when a later sibling records the
    same production; `forall` reads count and qualified keys; comprehension bodies are
    validated like scalar values. -/

private def lens (groups : List (List String)) : List Nat := groups.map List.length

triptych Trailing where
  grammar
    S     ::= rep Item sepBy "," + ";" Digit
    Item  ::= Digit
    Digit ::= digit{1}
  value'
    lens [Item ⟨[Digit]⟩]

#guard Trailing.parse "1,2;3" = some [1, 1]

triptych Bounded where
  grammar
    Doc  ::= Max ":" rep Row sepBy ";" +
    Max  ::= digit+
    Row  ::= Head "=" rep Cell sepBy "," +
    Head ::= digit+
    Cell ::= digit+
  value'
    List.length [Row]
  constraints
    forall Row, count Cell ≤ nat Max
    forall Row, nat Row.Head ≤ count Row

#guard Bounded.parse "3:1=4,5;2=6" = some 2
#guard Bounded.parse "1:1=4,5;2=6" = none
#guard Bounded.parse "3:9=4;2=6" = none

/--
error: value references `Cell` bare, which reads its SIGN (±1) — but `Cell` is not a sign capture. Declare `Cell ::= sign`, or use `nat Cell`/`int Cell`/`len Cell` to read its magnitude/length.
-/
#guard_msgs in
triptych BareCell where
  grammar
    Doc  ::= rep Cell sepBy "," +
    Cell ::= digit+
  value
    [Cell ↦ Cell]

end GroupBoundaryExample

end Triptych.Tests
