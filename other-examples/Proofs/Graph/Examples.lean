import Outputs.Graph.parser

/-!
# Graph parser checks

Executable examples and generated-contract checks for the public dependent-width Graph grammar.
-/

namespace GraphExample

open Triptych

#guard Graph.parse "3:101" =
  some { order := 3, edges := [(0, 1), (1, 2)] }
#guard Graph.parse "4:101001" =
  some { order := 4, edges := [(0, 1), (1, 2), (2, 3)] }
#guard Graph.parse "1:" =
  some { order := 1, edges := [] }
#guard Graph.parse "3:10" = none
#guard Graph.parse "3:1010" = none
#guard Graph.parse "3:10a" = none

example (cells order : String) :
    Graph.WfConstraints cells order ↔ cells.length = upperTriangleSize order :=
  Iff.rfl

example (input : String) :
    Graph.parse input = none ↔ ¬Graph.IsValid input :=
  Graph.parse_reject input

example (input : String) :
    (scannerParseMapProfile Graph.grammar Graph.constraints
      Graph.valueFn id input).result = Graph.parse input :=
  Graph.parse_profile_result input

example (input : String) :
    (scannerParseMapProfile Graph.grammar Graph.constraints
      Graph.valueFn id input).candidateChecks ≤
      scannerCandidateBudget Graph.grammar input :=
  Graph.parse_candidateChecks_le input

end GraphExample
