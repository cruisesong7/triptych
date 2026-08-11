import Graph

namespace TriptychBenchmark

def completeGraphInput (order : Nat) : String :=
  String.ofList (List.replicate (order * (order - 1) / 2) '1')

def runCase (label : String) (input : String) (iterations : Nat) : IO Unit := do
  let start ← IO.monoMsNow
  let mut accepted := 0
  for _ in List.range iterations do
    if (GraphExample.Graph.parse input).isSome then
      accepted := accepted + 1
  let elapsed ← IO.monoMsNow
  let budget := Triptych.decodeBudget GraphExample.Graph.grammar input
  IO.println s!"{label}: {iterations} parses, {accepted} accepted, {elapsed - start} ms, \
    reference-depth={budget.referenceDepth}, repetition-depth={budget.repetitionDepth}, \
    terminal-prefixes={budget.terminalPrefixCandidates}"

def run : IO Unit := do
  runCase "K8" (completeGraphInput 8) 250
  runCase "K16" (completeGraphInput 16) 100

end TriptychBenchmark

def main : IO Unit :=
  TriptychBenchmark.run
