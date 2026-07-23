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
import Triptych.Architecture.Decode
import Triptych.Theorems.Roundtrip

/-!
# Graph example — the `bit` terminal, a STRUCTURED value, and ARBITRARY order

The SAT-community encoding of a simple graph as the upper triangle of its adjacency matrix,
row-major over the pairs `i < j`, written as a bit string. Crucially this is ONE grammar for
graphs of EVERY order `n` — not a grammar per size:

```
Adj   ::= Cells        -- the whole adjacency string
Cells ::= bit+         -- one or more bits — ANY length, hence any order
```

The trick is the design's grammar-over-approximate / constraints-carve-out split:

* the **grammar** accepts any non-empty bit run (`bit+`) — trivially regular, any length;
* a **constraint** (`isTriangular`) requires the length to be a triangular number
  `T(n) = n(n-1)/2` (else the bits are not a complete upper triangle of any `n`);
* the **value** (`toGraph`, a `value'` escape) *recovers* `n` from the length and decodes the
  bits into a structured `Graph` (vertex count + edge list) — NOT an `Int`.

So the string→graph parser handles `n = 2, 3, 4, …` uniformly. This is the answer to "must we
have an independent grammar for each order?" — no: the length is data, checked by a constraint
and interpreted by the value, exactly what those layers are for. (A format that also had to
*read* `n` from a header before the bits would be data-dependent/non-regular — the
hand-written-`decode` case; here `n` is recovered post-hoc from the length, which stays within
the flat-regular grammar + constraint + value decomposition.)

Notes:
* `bit` is the binary terminal (`0`/`1`) — the natural leaf alphabet here, alongside
  `digit`/`hexDigit` (so `Bit ::= "0" | "1"` per-cell productions are unnecessary).
* `Cells` wraps the `bit+` terminal in a NAMED production so its matched substring is captured
  (a bare top-level terminal records no name-keyed capture; the value/constraint read by name).
* The value is a `value'` ESCAPE because a graph is outside the scalar-arithmetic `value` DSL.

Writes `spec.lean` + `parser.lean` beside this file (no `parser`/`printer` clause, so no
`soundness.lean`).
-/

namespace Triptych.Examples.Graph
open Triptych

/-- A simple graph as a vertex count + the set of present edges (over `{0,…,order-1}`). The
    STRUCTURED value the parser produces — a custom type, not an `Int`. -/
structure Graph where
  order : Nat
  edges : List (Nat × Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Recover the vertex count `n` from the number of upper-triangle cells `L = n(n-1)/2`: the
    `n` with `T(n) = L` (`0` if `L` is not triangular — excluded at valid inputs by the
    `isTriangular` constraint). Bounded search up to `L+1` (since `T(n) ≥ n-1 ≥ L` there). -/
def orderOf (L : Nat) : Nat :=
  ((List.range (L + 2)).find? (fun n => n * (n - 1) / 2 == L)).getD 0

/-- Author-supplied structured decoder (`value'` escape): the upper-triangle bit string →
    the graph. Recovers `n` from the length, enumerates the pairs `i < j` in the same
    row-major order, and keeps a pair iff its bit is `'1'`. -/
def toGraph (cells : String) : Graph :=
  let bs := cells.toList
  let n := orderOf bs.length
  let pairs := (List.range n).flatMap (fun i =>
    (List.range n).filterMap (fun j => if i < j then some (i, j) else none))
  { order := n,
    edges := (pairs.zip bs).filterMap (fun (p, b) => if b = '1' then some p else none) }

/-- The length is a triangular number `n(n-1)/2` for some `n` — i.e. the bits form a complete
    upper triangle. A decidable bounded search; the `constraints'` escape. -/
def isTriangular (cells : String) : Bool :=
  (List.range (cells.length + 2)).any (fun n => n * (n - 1) / 2 == cells.length)

format_spec Graph where
  grammar
    Adj   ::= Cells
    Cells ::= bit+
  value'
    toGraph Cells
  constraints'
    isTriangular Cells
  to "Triptych/Examples/Graph"

#check (Graph.IsWf.Adj      : String → Prop)
#check (Graph.computeValue  : String → Option Graph)   -- STRUCTURED value, any order

#eval Graph.computeValue "1"        -- some { order := 2, edges := [(0,1)] }
#eval Graph.computeValue "101"      -- some { order := 3, edges := [(0,1),(1,2)] }   (path)
#eval Graph.computeValue "111"      -- some { order := 3, edges := [(0,1),(0,2),(1,2)] } (K₃)
#eval Graph.computeValue "111111"   -- some { order := 4, edges := all 6 pairs }        (K₄)
#eval decide (Graph.IsValid "111")     -- true  (T(3) = 3)
#eval decide (Graph.IsValid "111111") -- true  (T(4) = 6)
#eval decide (Graph.IsValid "11")      -- false (2 is not triangular)
#eval decide (Graph.IsValid "1111")    -- false (4 is not triangular)
#eval decide (Graph.IsValid "1a1")     -- false ('a' is not a bit — grammar)

#check (Graph.IsWf_equiv : ∀ s, IsWf Graph.grammar s ↔ Graph.IsWf.Adj s)
example : DecidablePred Graph.IsValid := inferInstance

end Triptych.Examples.Graph
