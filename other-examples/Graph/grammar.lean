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
import Triptych.Theorems.Unambiguity

/-!
# Graph example — the `bit` terminal, a STRUCTURED value, and ARBITRARY order

A simple graph encoded as the upper triangle of its adjacency matrix, written as a bit string.
ONE grammar covers graphs of every order `n`: the grammar accepts any non-empty bit run
(`bit+`), a `constraints'` escape (`isTriangular`) requires the length to be a triangular
number `T(n) = n(n-1)/2`, and a `value'` escape (`toGraph`) recovers `n` from the length and
decodes into a structured `Graph` (not an `Int`). See the docs for the
grammar-over-approximates / constraint-carves-out rationale and the `Cells` wrapping trick.
-/

namespace GraphExample
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

triptych Graph where
  grammar
    Adj   ::= Cells
    Cells ::= bit+
  value'
    toGraph Cells
  constraints'
    isTriangular Cells
  to "Graph"

#eval Graph.computeValue "101"      -- some { order := 3, edges := [(0,1),(1,2)] }   (path)
#eval Graph.computeValue "111111"   -- some { order := 4, edges := all 6 pairs }        (K₄)
#eval decide (Graph.IsValid "11")   -- false (2 is not triangular)
#eval Graph.computeValue "1a1"      -- none ('a' is not a bit — grammar)

-- Static, all-input value coherence: `Adj → Cells → bit+` is a unary deterministic path.
#guard Graph.grammar.staticUnique = true

example : GrammarDecodeUnique Graph.grammar :=
  Graph.grammarDecodeUnique

example : GrammarCaptureFunctional Graph.grammar :=
  Graph.grammarCaptureFunctional

example : GrammarValueCoherent Graph.grammar Graph.valueFn :=
  Graph.grammarValueCoherent

end GraphExample
