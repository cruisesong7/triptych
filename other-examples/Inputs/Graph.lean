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
# Sized upper-triangular graph

The decimal `Order` header determines the exact number of adjacency bits:
`n * (n - 1) / 2`. The literal colon fixes the boundary between the header and final payload,
so Triptych can generate the complete readable specification and verified parser.
-/

namespace GraphExample

open Triptych

/-- A graph represented by its vertex count and present upper-triangle edges. -/
structure Graph where
  order : Nat
  edges : List (Nat × Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Exact number of cells in the strict upper triangle of an `n × n` adjacency matrix. -/
def upperTriangleSize (order : String) : Nat :=
  let vertices := readNat order
  vertices * (vertices - 1) / 2

private def upperTrianglePairs (order : Nat) : List (Nat × Nat) :=
  (List.range order).flatMap fun upper =>
    (List.range upper).map fun lower => (lower, upper)

/-- Interpret the exact-width bit payload as a graph. -/
def toGraph (order cells : String) : Graph :=
  let vertices := readNat order
  let edges :=
    ((upperTrianglePairs vertices).zip cells.toList).filterMap fun (edge, present) =>
      if present = '1' then some edge else none
  { order := vertices, edges }

triptych Graph where
  grammar
    Graph ::= Order ":" Cells
    Order ::= digit+
    Cells ::= bit{upperTriangleSize Order}
  value'
    toGraph Order Cells
  to "Outputs/Graph"

end GraphExample
