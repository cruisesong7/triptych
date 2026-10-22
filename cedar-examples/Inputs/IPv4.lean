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

import Triptych.Elab.Syntax
import Triptych.Reference.Roundtrip
import Cedar.Spec.Ext.IPAddr

/-!
# IPv4 example — CIDR grammar and an injective integer value encoding

Transcribes the IPv4 fragment of Cedar's `Cedar/Spec/Ext/IPAddr.lean` (`parseIPv4Net`). Beyond
the bare dotted-quad it models the full Cedar surface:

* the optional CIDR **prefix** `/N` (an `A.B.C.D` address is Cedar's `/32`), as a start-symbol
  alternation (like Datetime's optional `Time`/`Offset`) — so the grammar accepts exactly the
  strings Cedar's `parseIPv4Net` does;
* the canonical-nat rules on every octet AND the prefix (`noLeadingZero`), plus numeric bounds
  (octet ≤ 255, prefix ≤ 32) — the `256.0.0.1` / `/33` / `/01` rejects;
* a structured Cedar `CIDR` result represented inside the analyzable DSL by the injective code
  `address·33 + prefix`, then converted at the generated parser boundary;
* the `parser`/`printer` clauses validating Cedar's own parser (`ipv4Only`, a thin public wrapper
  over the real `Cedar.Spec.Ext.IPAddr.ip`) and serializer (`ToString IPNet`) against this spec —
  giving `soundness.lean` the translation-validation obligations, as in Decimal/Duration.

The octets get distinct names `Oct1..Oct4` because the capture model would collapse a reused
nonterminal (see the docs).
-/

namespace CedarExamples.IPv4
open Triptych
open Cedar.Spec.Ext.IPAddr

abbrev IPv4Net := CIDR V4_WIDTH

/-- Decode the DSL code `address·33 + prefix` into Cedar's IPv4 CIDR domain. Grammar and
    constraints guarantee `address < 2^32` and `prefix ≤ 32`. -/
def ipv4CodeToNet (code : Int) : IPv4Net :=
  let encoded := code.toNat
  { addr := BitVec.ofNat 32 (encoded / 33)
    pre := ((encoded % 33 : Nat) : IPv4Prefix) }

/-- Inject Cedar's IPv4 CIDR domain back into the DSL integer domain. -/
def ipv4NetToCode (net : IPv4Net) : Int :=
  (net.addr.toNat : Int) * 33 + net.pre.toNat

/-- Canonical serializer for the V4-only domain; reuses Cedar's `ToString IPNet`. -/
def ipNetToStr (n : IPv4Net) : String := toString (IPNet.V4 n)

/-- External parser for the `parser` clause: Cedar's REAL `ip`, restricted to its IPv4 answers.
    `ip` tries IPv4 then IPv6, so the family match rejects its V6 answers while returning the
    underlying V4 `CIDR`. -/
def ipv4Only (s : String) : Option IPv4Net :=
  match ip s with
  | some (.V4 cidr) => some cidr
  | _ => none

  triptych IPv4 where
  grammar
    -- An address with an optional CIDR prefix (`A.B.C.D` means Cedar's `A.B.C.D/32`).
    V4Net       ::= V4Addr | V4Addr "/" Prefix
    V4Addr      ::= Oct1 "." Oct2 "." Oct3 "." Oct4
    Oct1        ::= digit{1,3}
    Oct2        ::= digit{1,3}
    Oct3        ::= digit{1,3}
    Oct4        ::= digit{1,3}
    Prefix      ::= digit{1,2}
  value
    ((((nat Oct1 * 256 + nat Oct2) * 256 + nat Oct3) * 256 + nat Oct4) * 33
      + ifEmpty(Prefix, 32, nat Prefix))
    ofSpec ipv4CodeToNet
    toSpec ipv4NetToCode
  constraints
    -- canonical decimal per octet: no leading zeros (unless exactly "0"), and value ≤ 255.
    noLeadingZero Oct1     nat Oct1 ∈ [0, 255]
    noLeadingZero Oct2     nat Oct2 ∈ [0, 255]
    noLeadingZero Oct3     nat Oct3 ∈ [0, 255]
    noLeadingZero Oct4     nat Oct4 ∈ [0, 255]
    -- The prefix, when present: no leading zeros ("/01" rejected) and ≤ 32.
    -- An absent prefix (the bare-address alternative) is encoded as /32.
    noLeadingZero Prefix   nat Prefix ∈ [0, 32]
    value ∈ [0, 2 ^ 32 * 33 - 1]
  parser ipv4Only
  printer ipNetToStr
  verus "../verus-experiments/cedar-ext/ipaddr/src/ipv4/spec.rs"
  to "Outputs/IPv4"

-- The generated verified parser (`String → Option IPNet`), run on sample strings:
#eval IPv4.parse "192.168.1.100"     -- some (V4 192.168.1.100/32)
#eval IPv4.parse "8.8.8.8/24"        -- some (V4 8.8.8.8/24)      (CIDR prefix)
#eval IPv4.parse "256.0.0.1"         -- none  (256 > 255)
#eval IPv4.parse "127.0.0.1/33"      -- none  (prefix > 32)
#eval IPv4.parse "01.0.0.1"          -- none  (leading zero)
#eval IPv4.parse "1.2.3"             -- none  (only 3 octets — grammar)

end CedarExamples.IPv4
