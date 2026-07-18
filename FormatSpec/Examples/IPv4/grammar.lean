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

import FormatSpec.Syntax
import FormatSpec.Decode
import FormatSpec.Roundtrip

/-!
# IPv4 example — `noLeadingZero` + numeric bounds on reused octets

Transcribes the IPv4 fragment of `doc/CedarDoc/IPAddr.lean`:
```
V4Addr ::= NumV4 '.' NumV4 '.' NumV4 '.' NumV4
NumV4  ::= Digit{1,3}     -- value ≤ 255, no leading zeros unless "0"
```
Exercises the `noLeadingZero` canonical-nat constraint (the pervasive IPAddr rule, unused by
the other examples) and per-octet numeric bounds. NOTE: the four octets are given DISTINCT
nonterminals `Oct1..Oct4` (each `Digit{1,3}`) rather than one reused `NumV4`. That is not
cosmetic: the capture model keys by (qualified) production name, so four reuses of a single
`NumV4` would collapse to ONE capture — the constraints would then bind only the first octet
(a real under-specification). Distinct names give each octet its own capture, so each is
constrained independently. The optional CIDR `/prefix` is omitted for brevity (affine; would
add a `noLeadingZero`/`≤ 32` bound the same way). Writes `spec.lean` beside this file.
-/

namespace FormatSpec.Examples.IPv4
open FormatSpec

format_spec IPv4 where
  grammar
    V4Addr ::= Oct1 "." Oct2 "." Oct3 "." Oct4
    Oct1   ::= digit{1,3}
    Oct2   ::= digit{1,3}
    Oct3   ::= digit{1,3}
    Oct4   ::= digit{1,3}
  constraints
    -- canonical decimal per octet: no leading zeros (unless exactly "0"), and value ≤ 255.
    noLeadingZero Oct1     nat Oct1 ∈ [0, 255]
    noLeadingZero Oct2     nat Oct2 ∈ [0, 255]
    noLeadingZero Oct3     nat Oct3 ∈ [0, 255]
    noLeadingZero Oct4     nat Oct4 ∈ [0, 255]
  to "FormatSpec/Examples/IPv4"

#check (IPv4.IsWf.V4Addr : String → Prop)
#check (IPv4.IsValid     : String → Prop)
#eval decide (IPv4.IsValid "192.168.1.100")    -- true
#eval decide (IPv4.IsValid "255.255.255.255")  -- true
#eval decide (IPv4.IsValid "256.0.0.1")        -- false (256 > 255)
#eval decide (IPv4.IsValid "01.0.0.1")         -- false (leading zero)
#eval decide (IPv4.IsValid "1.2.3")            -- false (only 3 octets — grammar)

#check (IPv4.IsWf_equiv : ∀ s, IsWf IPv4.grammar s ↔ IPv4.IsWf.V4Addr s)
example : DecidablePred IPv4.IsValid := inferInstance

end FormatSpec.Examples.IPv4
