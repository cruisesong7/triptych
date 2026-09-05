import Graph.grammar

namespace TriptychBenchmark

open Triptych
open GraphExample

def completeGraphInput (order : Nat) : String :=
  String.ofList (List.replicate (order * (order - 1) / 2) '1')

def measure (engine : String → Option CaptureMap) (input : String)
    (iterations : Nat) : IO (Nat × Nat) := do
  let start ← IO.monoNanosNow
  let mut accepted := 0
  for _ in List.range iterations do
    if (engine input).isSome then
      accepted := accepted + 1
  let stop ← IO.monoNanosNow
  pure (stop - start, accepted)

def formatMicros (nanoseconds : Nat) : String :=
  s!"{nanoseconds / 1000} us"

def runCase (label : String) (input : String) (iterations : Nat) : IO Unit := do
  let (scannerTime, scannerAccepted) ←
    measure (scan Graph.grammar) input iterations
  let (referenceTime, referenceAccepted) ←
    measure (decode Graph.grammar) input iterations
  let speedupTenths := if scannerTime = 0 then 0 else referenceTime * 10 / scannerTime
  let checks := scannerCandidateChecks Graph.grammar input
  let budget := scannerCandidateBudget Graph.grammar input
  IO.println s!"{label}: {iterations} parses, scanner={formatMicros scannerTime}, \
    reference={formatMicros referenceTime}, speedup={speedupTenths / 10}.\
    {speedupTenths % 10}x, accepted={scannerAccepted}/{referenceAccepted}, \
    input={input.length} chars, candidate-checks={checks}/{budget}"

def run : IO Unit := do
  runCase "K8" (completeGraphInput 8) 1000
  runCase "K16" (completeGraphInput 16) 250
  runCase "K32" (completeGraphInput 32) 25

end TriptychBenchmark

def main : IO Unit :=
  TriptychBenchmark.run
