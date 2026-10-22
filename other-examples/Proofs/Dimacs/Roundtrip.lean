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

import Outputs.Dimacs.parser
import Std.Sat.CNF.Dimacs

/-!
# DIMACS round trip against `Std`

`Std.Sat.CNF.dimacs` is the DIMACS printer `bv_decide` uses to hand formulas to its SAT solver.
It numbers variables from one, so variable `v` with polarity `b` is printed as `±(v + 1)`. Each
case prints a formula with `Std` and requires the generated verified parser to recover exactly
its clauses.
-/

namespace DimacsExample.Roundtrip

open Std.Sat

/-- The clauses `Std.Sat.CNF.dimacs` writes for `cnf`, as signed DIMACS literals. -/
def expected (cnf : CNF Nat) : List (List Int) :=
  cnf.clauses.toList.map fun clause =>
    clause.map fun (var, positive) => if positive then (var + 1 : Int) else -(var + 1 : Int)

/-- The pigeonhole formula: `holes + 1` pigeons, each in some hole, no two sharing a hole. -/
def pigeonhole (holes : Nat) : CNF Nat :=
  let pigeons := holes + 1
  let var (pigeon hole : Nat) := pigeon * holes + hole
  let somewhere := (List.range pigeons).map fun pigeon =>
    (List.range holes).map fun hole => (var pigeon hole, true)
  let apart := (List.range holes).flatMap fun hole =>
    (List.range pigeons).flatMap fun first =>
      ((List.range pigeons).filter (first < ·)).map fun second =>
        [(var first hole, false), (var second hole, false)]
  { clauses := (somewhere ++ apart).toArray }

def formulas : List (CNF Nat) := [
  { clauses := #[] },
  { clauses := #[[]] },
  { clauses := #[[(0, true)], [(0, false)]] },
  { clauses := #[[(2, true), (0, false)], [], [(9, true), (4, false), (11, true)]] },
  { clauses := #[[(99, false)]] },
  pigeonhole 2,
  pigeonhole 4
]

def failures : List (CNF Nat) :=
  formulas.filter fun cnf => Dimacs.parse (CNF.dimacs cnf) != some (expected cnf)

#eval do
  IO.println s!"DIMACS Std.Sat.CNF.dimacs round trip: \
    {formulas.length - failures.length}/{formulas.length} recovered"
  for cnf in failures do
    IO.println s!"  mismatch on {repr (CNF.dimacs cnf)}: \
      generated={repr (Dimacs.parse (CNF.dimacs cnf))}"
  if !failures.isEmpty then
    throw <| IO.userError s!"{failures.length} DIMACS round-trip failures"

end DimacsExample.Roundtrip
