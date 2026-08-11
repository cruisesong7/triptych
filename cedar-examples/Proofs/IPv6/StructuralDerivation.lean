import Outputs.IPv6.parser

/-! Executable smoke test for generated optional and repeated derivations. -/

open Triptych

namespace CedarExamples.IPv6

def ipv6CompressedDerivation : IPv6.Derivation.V6Net :=
  .alt1
    (.alt1
      (.alt0
        (some (.alt0 [.alt0 "2001", .alt0 "db8"]))
        (some (.alt0 [.alt0 "1"]))))
    (.alt0 "64")

#guard IPv6.Derivation.V6Net.render ipv6CompressedDerivation = "2001:db8::1/64"

example : IPv6.Derivation.V6Net.Valid ipv6CompressedDerivation := by
  decide

example :
    (IPv6.Derivation.V6Net.capturesWith "" ipv6CompressedDerivation).toEnv
        "H16L#count" =
      some "2" := by
  decide

example :
    IPv6.Derivation.V6Net.capturesWith "" ipv6CompressedDerivation ∈
      fullParses IPv6.grammar (IPv6.Derivation.V6Net.render ipv6CompressedDerivation) :=
  IPv6.Derivation.V6Net.mem_fullParses ipv6CompressedDerivation (by decide)

end CedarExamples.IPv6
