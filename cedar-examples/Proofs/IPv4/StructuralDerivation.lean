import Outputs.IPv4.parser

/-! Executable smoke test for generated shared-prefix alternatives. -/

open Triptych

namespace CedarExamples.IPv4

def ipv4AddressDerivation : IPv4.Derivation.V4Addr :=
  .alt0 (.alt0 "192") (.alt0 "168") (.alt0 "1") (.alt0 "100")

def ipv4BareDerivation : IPv4.Derivation.V4Net :=
  .alt0 ipv4AddressDerivation

def ipv4PrefixDerivation : IPv4.Derivation.V4Net :=
  .alt1 ipv4AddressDerivation (.alt0 "24")

#guard IPv4.Derivation.V4Net.render ipv4BareDerivation = "192.168.1.100"
#guard IPv4.Derivation.V4Net.render ipv4PrefixDerivation = "192.168.1.100/24"

example : IPv4.Derivation.V4Net.Valid ipv4PrefixDerivation := by
  decide

example :
    IPv4.Derivation.V4Net.capturesWith "" ipv4PrefixDerivation ∈
      fullParses IPv4.grammar (IPv4.Derivation.V4Net.render ipv4PrefixDerivation) :=
  IPv4.Derivation.V4Net.mem_fullParses ipv4PrefixDerivation (by decide)

end CedarExamples.IPv4
