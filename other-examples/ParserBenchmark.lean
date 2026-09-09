import Outputs.Graph.parser

namespace TriptychBenchmark

open Triptych
open GraphExample

def completeGraphInput (order : Nat) : String :=
  s!"{order}:{String.ofList (List.replicate (order * (order - 1) / 2) '1')}"

def measure {α : Type} (engine : String → Option α) (input : String)
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

def runScannerCase (label : String) (input : String) (iterations : Nat) : IO Unit := do
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

def runParserCase (label : String) (input : String) (iterations : Nat) : IO Unit := do
  let (generatedTime, generatedAccepted) ← measure Graph.parse input iterations
  let (legacyTime, legacyAccepted) ←
    measure (gatedParse Graph.IsValid Graph.computeValue) input iterations
  let speedupTenths := if generatedTime = 0 then 0 else legacyTime * 10 / generatedTime
  IO.println s!"{label}: {iterations} parses, one-scan={formatMicros generatedTime}, \
    gated={formatMicros legacyTime}, speedup={speedupTenths / 10}.\
    {speedupTenths % 10}x, accepted={generatedAccepted}/{legacyAccepted}, \
    input={input.length} chars"

def run : IO Unit := do
  let k8 := completeGraphInput 8
  let k16 := completeGraphInput 16
  let k32 := completeGraphInput 32
  runScannerCase "K8 scanner/reference" k8 1000
  runParserCase "K8 generated/gated" k8 1000
  runScannerCase "K16 scanner/reference" k16 250
  runParserCase "K16 generated/gated" k16 250
  runScannerCase "K32 scanner/reference" k32 25
  runParserCase "K32 generated/gated" k32 25

end TriptychBenchmark

def main : IO Unit :=
  TriptychBenchmark.run
