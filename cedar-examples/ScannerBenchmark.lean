import Outputs.Decimal.parser
import Outputs.IPv6.parser

namespace CedarExamples.ScannerBenchmark

open Triptych

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

def runScannerCase (label input : String) (iterations : Nat) (g : Grammar) : IO Unit := do
  let (scannerTime, scannerAccepted) ← measure (scan g) input iterations
  let (referenceTime, referenceAccepted) ← measure (decode g) input iterations
  let speedupTenths := if scannerTime = 0 then 0 else referenceTime * 10 / scannerTime
  let checks := scannerCandidateChecks g input
  let budget := scannerCandidateBudget g input
  IO.println s!"{label}: {iterations} parses, scanner={formatMicros scannerTime}, \
    reference={formatMicros referenceTime}, speedup={speedupTenths / 10}.\
    {speedupTenths % 10}x, accepted={scannerAccepted}/{referenceAccepted}, \
    candidate-checks={checks}/{budget}"

def runParserCase {α : Type} (label input : String) (iterations : Nat)
    (generated legacy : String → Option α) : IO Unit := do
  let (generatedTime, generatedAccepted) ← measure generated input iterations
  let (legacyTime, legacyAccepted) ← measure legacy input iterations
  let speedupTenths := if generatedTime = 0 then 0 else legacyTime * 10 / generatedTime
  IO.println s!"{label}: {iterations} parses, one-scan={formatMicros generatedTime}, \
    gated={formatMicros legacyTime}, speedup={speedupTenths / 10}.\
    {speedupTenths % 10}x, accepted={generatedAccepted}/{legacyAccepted}"

def run : IO Unit := do
  let decimal := "-1234567890.1234"
  let ipv6Full := "2001:0db8:0000:0000:0000:ff00:0042:8329"
  let ipv6Compressed := "2001:db8::ff00:42:8329/64"
  runScannerCase "Decimal scanner/reference" decimal 1000 Decimal.grammar
  runParserCase "Decimal generated/gated" decimal 1000 Decimal.parse
    (gatedParseOfSpec Decimal.IsValid Decimal.computeValue Int64.ofInt)
  runScannerCase "IPv6 full scanner/reference" ipv6Full 100 IPv6.grammar
  runParserCase "IPv6 full generated/gated" ipv6Full 100 IPv6.parse
    (gatedParse IPv6.IsValid IPv6.computeValue)
  runScannerCase "IPv6 compressed scanner/reference" ipv6Compressed 100 IPv6.grammar
  runParserCase "IPv6 compressed generated/gated" ipv6Compressed 100 IPv6.parse
    (gatedParse IPv6.IsValid IPv6.computeValue)

end CedarExamples.ScannerBenchmark

def main : IO Unit :=
  CedarExamples.ScannerBenchmark.run
