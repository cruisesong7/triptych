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
import Triptych.Architecture.Decode
import Triptych.Theorems.Roundtrip
import Cedar.Spec.Ext.IPAddr

/-!
# IPv4 example — CIDR grammar, a STRUCTURED `IPNet` value, against Cedar's real `ip` parser

Transcribes the IPv4 fragment of Cedar's `Cedar/Spec/Ext/IPAddr.lean` (`parseIPv4Net`). Beyond
the bare dotted-quad it models the full Cedar surface:

* the optional CIDR **`/prefix`** (an `A.B.C.D` address is Cedar's `/32`), as a start-symbol
  alternation (like Datetime's optional `Time`/`Offset`) — so the grammar accepts exactly the
  strings Cedar's `parseIPv4Net` does;
* the canonical-nat rules on every octet AND the prefix (`noLeadingZero`), plus the numeric
  bounds (octet ≤ 255, prefix ≤ 32) — the `256.0.0.1` / `/33` / `/01` reject cases;
* a **structured value** — Cedar's `IPNet.V4 ⟨addr, pre⟩`, not just accept/reject — via the
  `value'` escape (`toIPNet`), exactly as the Graph example produces a `Graph`. IPv4's value is
  a 32-bit address + prefix, not an affine `Int`, so it lives in the escape tier;
* the `parser`/`printer` clauses validating Cedar's own parser (`ipv4Only`, a thin public wrapper
  over the real `Cedar.Spec.Ext.IPAddr.ip`) and serializer (`ToString IPNet`) against this spec —
  giving `soundness.lean` the translation-validation obligations, as in Decimal/Duration.

The octets get distinct names `Oct1..Oct4` because the capture model would collapse a reused
nonterminal (see the docs).
-/

namespace CedarExamples.IPv4
open Triptych
open Cedar.Spec.Ext.IPAddr

-- The value type `IPNet` lives in Cedar's namespace, but the value's a `value'` escape, so the
-- generated `parser.lean`/`soundness.lean` state their contracts over `IPNet` while opening only
-- THIS (caller) namespace. Re-export it here so that short name resolves in the generated files
-- (the caller open is the sanctioned hook — like Graph's own-namespace `Graph` type).
export Cedar.Spec.Ext.IPAddr (IPNet)

/-- Structured value (`value'` escape): the four octet strings + the CIDR prefix string →
    Cedar's `IPNet.V4 ⟨addr, pre⟩`. An absent prefix (empty string, the bare-address
    alternative) is Cedar's full `/32` (`ADDR_SIZE V4_WIDTH`, which `IPv4Prefix` encodes as
    `none`). Reuses Cedar's own `IPv4Addr.mk`, `IPv4Prefix` coercion, and `readNat` — the same
    digit reader the value/`IsWf` layer uses — so the reconstruction is Cedar's `parseSegsV4` /
    `parseIPv4Net` on the already-validated components. -/
def toIPNet (o1 o2 o3 o4 pre : String) : IPNet :=
  let oct (s : String) : BitVec 8 := BitVec.ofNat 8 (readNat s)
  let p : IPv4Prefix :=
    if pre == "" then (ADDR_SIZE V4_WIDTH : IPv4Prefix) else (readNat pre : IPv4Prefix)
  IPNet.V4 { addr := IPv4Addr.mk (oct o1) (oct o2) (oct o3) (oct o4), pre := p }

/-- Canonical serializer for the `printer` clause, over the domain type `IPNet`; reuses Cedar's
    own `ToString IPNet` (renders `a.b.c.d/pre`). -/
def ipNetToStr (n : IPNet) : String := toString n

/-- External parser for the `parser` clause: Cedar's REAL `ip`, restricted to its IPv4 answers.
    `ip` tries IPv4 then IPv6 (`parse`), so on a V6 string it returns `some (.V6 …)`; filtering to
    `IPNet.isV4` keeps this spec's language exactly the V4 one — without it the `extparse_reject`
    obligation (`ipv4Only s = none ↔ ¬ IsValid s`) would be false on every V6 string. On V4 inputs
    `ipv4Only` IS Cedar's `parseIPv4Net`, so the obligations validate the real parser. -/
def ipv4Only (s : String) : Option IPNet := (ip s).filter (·.isV4)

triptych IPv4 where
  grammar
    -- An address, optionally with a CIDR prefix (`A.B.C.D` ⟺ Cedar's `A.B.C.D/32`).
    V4Net  ::= V4Addr | V4Addr "/" Prefix
    V4Addr ::= Oct1 "." Oct2 "." Oct3 "." Oct4
    Oct1   ::= digit{1,3}
    Oct2   ::= digit{1,3}
    Oct3   ::= digit{1,3}
    Oct4   ::= digit{1,3}
    Prefix ::= digit{1,2}
  value'
    toIPNet Oct1 Oct2 Oct3 Oct4 Prefix
  constraints
    -- canonical decimal per octet: no leading zeros (unless exactly "0"), and value ≤ 255.
    noLeadingZero Oct1     nat Oct1 ∈ [0, 255]
    noLeadingZero Oct2     nat Oct2 ∈ [0, 255]
    noLeadingZero Oct3     nat Oct3 ∈ [0, 255]
    noLeadingZero Oct4     nat Oct4 ∈ [0, 255]
    -- the CIDR prefix, when present: no leading zeros ("/01" rejected) and ≤ 32.
    -- Absent (bare-address alternative) ⟹ vacuous, and `toIPNet` reads "" as /32.
    noLeadingZero Prefix   nat Prefix ∈ [0, 32]
  parser ipv4Only projection id
  printer ipNetToStr
  to "IPv4"

-- The generated verified parser (`String → Option IPNet`), run on sample strings:
#eval IPv4.parse "192.168.1.100"     -- some (V4 192.168.1.100/32)
#eval IPv4.parse "8.8.8.8/24"        -- some (V4 8.8.8.8/24)      (CIDR prefix)
#eval IPv4.parse "256.0.0.1"         -- none  (256 > 255)
#eval IPv4.parse "127.0.0.1/33"      -- none  (prefix > 32)
#eval IPv4.parse "01.0.0.1"          -- none  (leading zero)
#eval IPv4.parse "1.2.3"             -- none  (only 3 octets — grammar)

end CedarExamples.IPv4
