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

import Triptych.Architecture.Syntax
import Triptych.Theorems.Roundtrip
import Triptych.Theorems.Coherence
import Cedar.Spec.Ext.IPAddr

/-!
# Full IPv6/CIDR example with analyzable value reconstruction

Transcribes Cedar's IPv6 language, including both eight-group addresses and `::` compression,
plus the optional CIDR prefix `/N`. The compressed form is ordinary grammar structure:

```
Compressed ::= [Left] "::" [Right]
```

Each present side is captured as its complete colon-separated substring. `segments Left +
segments Right < 8` says that `::` replaces at least one group, while `hexSeq` concatenates
the groups as base-65536 digits. The resulting 128-bit address and prefix are packed into the
injective DSL code `address·129 + prefix`, so the full value path is translated to Verus without
an opaque `value'` escape.
-/

namespace CedarExamples.IPv6
open Triptych
open Cedar.Spec.Ext.IPAddr

export Cedar.Spec.Ext.IPAddr (IPv6Addr IPNet)

abbrev IPv6Net := CIDR V6_WIDTH

/-- Unsigned value of a hexadecimal string, retained as a proof-facing bridge to Cedar's
    existing IPv6 parser implementation. The Triptych value clause uses `hexSeq` directly. -/
def readHex (s : String) : Nat :=
  s.foldl (fun n c =>
    n * 16 +
      (if c.isDigit then c.toNat - '0'.toNat
       else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
       else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
       else 0)) 0

/-- Convert eight proof-facing hexadecimal groups to Cedar's 128-bit address type. -/
def toV6Addr (groups : List String) : IPv6Addr :=
  let g (i : Nat) : BitVec 16 := BitVec.ofNat 16 (readHex (groups.getD i ""))
  IPv6Addr.mk (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7)

/-- Reconstruct Cedar's CIDR value from the component view used by the bridge proofs. -/
def toIPv6Net (full left right : List String) (pre : String) : IPv6Net :=
  let groups :=
    if full.isEmpty then
      let omitted := 8 - (left.length + right.length)
      left ++ List.replicate omitted "" ++ right
    else
      full
  let preValue : IPv6Prefix :=
    if pre == "" then (ADDR_SIZE V6_WIDTH : IPv6Prefix) else (readNat pre : IPv6Prefix)
  { addr := toV6Addr groups, pre := preValue }

/-- Decode the DSL code `address·129 + prefix` into Cedar's IPv6 CIDR domain. -/
def ipv6CodeToNet (code : Int) : IPv6Net :=
  let encoded := code.toNat
  { addr := BitVec.ofNat 128 (encoded / 129)
    pre := ((encoded % 129 : Nat) : IPv6Prefix) }

/-- Inject Cedar's IPv6 CIDR domain back into the DSL integer domain. -/
def ipv6NetToCode (net : IPv6Net) : Int :=
  (net.addr.toNat : Int) * 129 + net.pre.toNat

/-- Canonical serializer for the V6-only domain; reuses Cedar's `ToString IPNet`. -/
def ipNetToStr (n : IPv6Net) : String := toString (IPNet.V6 n)

/-- Cedar's public IP parser restricted to the underlying IPv6 CIDR result. -/
def ipv6Only (s : String) : Option IPv6Net :=
  match ip s with
  | some (.V6 cidr) => some cidr
  | _ => none

  triptych IPv6 where
  grammar
    V6Net       ::= V6Addr | V6Addr "/" Prefix
    V6Addr      ::= Full | Compressed
    Full        ::= rep H16 sepBy ":" {8}
    Compressed  ::= [Left] "::" [Right]
    Left        ::= rep H16L sepBy ":" {1,7}
    Right       ::= rep H16R sepBy ":" {1,7}
    H16         ::= hexDigit{1,4}
    H16L        ::= hexDigit{1,4}
    H16R        ::= hexDigit{1,4}
    Prefix      ::= digit{1,3}
  value
    (ifEmpty(Full,
        hexSeq Left * 65536 ^ (8 - segments Left) + hexSeq Right,
        hexSeq Full) * 129
      + ifEmpty(Prefix, 128, nat Prefix))
    ofSpec ipv6CodeToNet
    toSpec ipv6NetToCode
  constraints
    segments Left + segments Right < 8
    noLeadingZero Prefix
    nat Prefix ∈ [0, 128]
  parser ipv6Only
  printer ipNetToStr
  verus "../verus-experiments/cedar-ext/ipaddr/src/ipv6/spec.rs"
  to "Outputs/IPv6"

#eval IPv6.parse "1:2:3:4:5:6:7:8"
#eval IPv6.parse "2001:db8::1"
#eval IPv6.parse "::"
#eval IPv6.parse "::1/128"
#eval IPv6.parse "1::/64"
#eval IPv6.parse "1:2:3:4:5:6:7::8" -- none: `::` must omit at least one group
#eval IPv6.parse "1:2:3:4"           -- none: neither full nor compressed
#eval IPv6.parse "::1/129"           -- none: prefix exceeds 128
#eval IPv6.parse "::1/01"            -- none: non-canonical prefix

-- Executable agreement checks against Cedar's parser on representative cases.
#eval IPv6.parse "2001:db8::1" == ipv6Only "2001:db8::1"
#eval IPv6.parse "::1/128" == ipv6Only "::1/128"
#eval IPv6.parse "1:2:3:4:5:6:7::8" == ipv6Only "1:2:3:4:5:6:7::8"

end CedarExamples.IPv6
