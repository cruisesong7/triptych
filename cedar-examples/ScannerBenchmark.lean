import Outputs.Decimal.spec
import Outputs.IPv6.spec

namespace CedarExamples.ScannerBenchmark

open Triptych

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

def runCase (label input : String) (iterations : Nat) (g : Grammar) : IO Unit := do
  let (scannerTime, scannerAccepted) ← measure (scan g) input iterations
  let (referenceTime, referenceAccepted) ← measure (decode g) input iterations
  let speedupTenths := if scannerTime = 0 then 0 else referenceTime * 10 / scannerTime
  let checks := scannerCandidateChecks g input
  let budget := scannerCandidateBudget g input
  IO.println s!"{label}: {iterations} parses, scanner={formatMicros scannerTime}, \
    reference={formatMicros referenceTime}, speedup={speedupTenths / 10}.\
    {speedupTenths % 10}x, accepted={scannerAccepted}/{referenceAccepted}, \
    candidate-checks={checks}/{budget}"

def run : IO Unit := do
  runCase "Decimal" "-1234567890.1234" 1000 Decimal.grammar
  runCase "IPv6 full" "2001:0db8:0000:0000:0000:ff00:0042:8329" 100 IPv6.grammar
  runCase "IPv6 compressed" "2001:db8::ff00:42:8329/64" 100 IPv6.grammar

end CedarExamples.ScannerBenchmark

def main : IO Unit :=
  CedarExamples.ScannerBenchmark.run
