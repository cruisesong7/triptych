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

/-!
# IPv4 example — `noLeadingZero` + numeric bounds on distinct octets

Transcribes the IPv4 fragment of `doc/CedarDoc/IPAddr.lean`. Exercises the `noLeadingZero`
canonical-nat constraint and per-octet numeric bounds. See the docs for why the octets get
distinct names `Oct1..Oct4` (the capture model would collapse a reused nonterminal).
-/

namespace Triptych.Examples.IPv4
open Triptych

triptych IPv4 where
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
  to "Triptych/Examples/IPv4"

#eval decide (IPv4.IsValid "192.168.1.100")    -- true
#eval decide (IPv4.IsValid "256.0.0.1")        -- false (256 > 255)
#eval decide (IPv4.IsValid "01.0.0.1")         -- false (leading zero)
#eval decide (IPv4.IsValid "1.2.3")            -- false (only 3 octets — grammar)

end Triptych.Examples.IPv4
