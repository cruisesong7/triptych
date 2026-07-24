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
# IPv6 example — `hexDigit` and GROUP repetition (`rep … sepBy …`)

Transcribes the eight-group IPv6 form from `doc/CedarDoc/IPAddr.lean`, expressed with the
`rep` combinator: `rep H16 sepBy ":" {8}` is a single repeated-group node (not eight unrolled
refs), so it decodes and proves at fixed cost. The `H16 ≤ 0xffff` bound is automatic from
`hexDigit{1,4}`. The `::` (gap) form is omitted — a two-sided variable-arity split that needs
a hand-written `decode`; see the docs.
-/

namespace Triptych.Examples.IPv6
open Triptych

triptych IPv6 where
  grammar
    V6Addr ::= rep H16 sepBy ":" {8}
    H16    ::= hexDigit{1,4}
  to "Triptych/Examples/IPv6"

#eval decide (IPv6.IsWf.V6Addr "1:2:3:4:5:6:7:8")          -- true (8 groups)
#eval decide (IPv6.IsWf.V6Addr "1:2:3:4")                  -- false (4 groups ≠ 8)
#eval decide (IPv6.IsWf.V6Addr "1:2:3:4:5:6:7:12345")      -- false (5 hex digits > 4)
#eval decide (IPv6.IsWf.V6Addr "1::4")                     -- false (`::` out of scope)

end Triptych.Examples.IPv6
