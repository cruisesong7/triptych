import Outputs.Decimal.parser
import Outputs.Duration.parser
import Outputs.Datetime.parser
import Outputs.IPv4.parser
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

def speedComparison (leftName rightName : String) (leftTime rightTime : Nat) : String :=
  if leftTime = 0 ∨ rightTime = 0 then
    "ratio unavailable"
  else if leftTime ≤ rightTime then
    let tenths := rightTime * 10 / leftTime
    s!"{leftName} is {tenths / 10}.{tenths % 10}x faster"
  else
    let tenths := leftTime * 10 / rightTime
    s!"{rightName} is {tenths / 10}.{tenths % 10}x faster"

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

def runParserCase {α : Type} [DecidableEq α] (label leftName rightName input : String)
    (iterations : Nat) (left right : String → Option α) : IO Unit := do
  if left input ≠ right input then
    throw <| IO.userError s!"{label}: parser outputs disagree"
  let (leftTime, leftAccepted) ← measure left input iterations
  let (rightTime, rightAccepted) ← measure right input iterations
  IO.println s!"{label}: {iterations} parses, {leftName}={formatMicros leftTime}, \
    {rightName}={formatMicros rightTime}, {speedComparison leftName rightName leftTime rightTime}, \
    accepted={leftAccepted}/{rightAccepted}"

def decimalPlan : ScanPlan :=
  match compileScanPlan Decimal.grammar with
  | .ok plan => plan
  | .error _ => default

def decimalRecognize (source : String) : Option Unit := do
  let remaining ←
    executeConsumers (consumingOps decimalPlan.operations) source.toList
  if remaining.isEmpty then some () else none

def runRecognitionCase (label input : String) (iterations : Nat) : IO Unit := do
  let (recognitionTime, recognitionAccepted) ← measure decimalRecognize input iterations
  IO.println s!"{label}: {iterations} parses, recognition={formatMicros recognitionTime}, \
    accepted={recognitionAccepted}"

def run : IO Unit := do
  let decimal := "-1234567890.1234"
  let invalidDecimal := "1.23456"
  let duration := "1d2h3m4s5ms"
  let invalidDuration := "1s1d"
  let datetime := "2024-10-15T11:38:02.101+1134"
  let invalidDatetime := "2024-01-01T31:02:03Z"
  let ipv4 := "192.168.0.1/32"
  let invalidIPv4 := "256.0.0.1"
  let ipv6Full := "2001:0db8:0000:0000:0000:ff00:0042:8329"
  let ipv6Compressed := "2001:db8::ff00:42:8329/64"
  let invalidIPv6 := "1:2:3:4:5:6:7::8"
  runScannerCase "Decimal scanner/reference" decimal 1000 Decimal.grammar
  runParserCase "Decimal generated/gated" "generated" "gated" decimal 1000 Decimal.parse
    (gatedParseOfSpec Decimal.IsValid Decimal.computeValue Int64.ofInt)
  runParserCase "Decimal generated/Cedar valid" "generated" "Cedar" decimal 10000
    Decimal.parse Cedar.Spec.Ext.Decimal.parse
  runParserCase "Decimal generated/Cedar invalid" "generated" "Cedar" invalidDecimal 10000
    Decimal.parse Cedar.Spec.Ext.Decimal.parse
  runRecognitionCase "Decimal recognition only valid" decimal 10000
  runRecognitionCase "Decimal recognition only invalid" invalidDecimal 10000
  runParserCase "Duration generated/Cedar valid" "generated" "Cedar" duration 1000
    Duration.parse Cedar.Spec.Ext.Datetime.Duration.parse
  runParserCase "Duration generated/Cedar invalid" "generated" "Cedar" invalidDuration 1000
    Duration.parse Cedar.Spec.Ext.Datetime.Duration.parse
  runParserCase "Datetime generated/Cedar valid" "generated" "Cedar" datetime 200
    Datetime.parse Cedar.Spec.Ext.Datetime.parse
  runParserCase "Datetime generated/Cedar invalid" "generated" "Cedar" invalidDatetime 200
    Datetime.parse Cedar.Spec.Ext.Datetime.parse
  runParserCase "IPv4 generated/Cedar valid" "generated" "Cedar" ipv4 1000
    IPv4.parse IPv4.ipv4Only
  runParserCase "IPv4 generated/Cedar invalid" "generated" "Cedar" invalidIPv4 1000
    IPv4.parse IPv4.ipv4Only
  runScannerCase "IPv6 full scanner/reference" ipv6Full 100 IPv6.grammar
  runParserCase "IPv6 full generated/gated" "generated" "gated" ipv6Full 100 IPv6.parse
    (gatedParseOfSpec IPv6.IsValid IPv6.computeValue IPv6.ipv6CodeToNet)
  runScannerCase "IPv6 compressed scanner/reference" ipv6Compressed 100 IPv6.grammar
  runParserCase "IPv6 compressed generated/gated" "generated" "gated" ipv6Compressed 100 IPv6.parse
    (gatedParseOfSpec IPv6.IsValid IPv6.computeValue IPv6.ipv6CodeToNet)
  runParserCase "IPv6 generated/Cedar valid" "generated" "Cedar" ipv6Compressed 100
    IPv6.parse IPv6.ipv6Only
  runParserCase "IPv6 generated/Cedar invalid" "generated" "Cedar" invalidIPv6 100
    IPv6.parse IPv6.ipv6Only

end CedarExamples.ScannerBenchmark

def main : IO Unit :=
  CedarExamples.ScannerBenchmark.run
