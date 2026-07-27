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
# IPv6 example — GROUP repetition (`rep … sepBy …`) with a STRUCTURED, list-captured value

Transcribes the eight-group IPv6 form from `doc/CedarDoc/IPAddr.lean`, expressed with the
`rep` combinator: `rep H16 sepBy ":" {8}` is a single repeated-group node (not eight unrolled
refs), so it decodes and proves at fixed cost. The `H16 ≤ 0xffff` bound is automatic from
`hexDigit{1,4}`.

Beyond mere recognition, this example produces a **structured value** — Cedar's `IPv6Addr` (a
`BitVec 128`), not just accept/reject — via the `value'` escape reading the repeated `H16`
group as a LIST: `value' toV6Addr [H16]`. The `[H16]` marker hands the escape EVERY matched
`H16` span (all eight groups), where the scalar reader would collapse them to the first. This is
the "addressable repetition" increment: a `rep`-repeated capture, exposed to the value layer as
`List String`.

The `::` (gap) form is omitted — a two-sided variable-arity split that needs a hand-written
`decode`; see the docs.
-/

namespace Triptych.Examples.IPv6
open Triptych
open Cedar.Spec.Ext.IPAddr

-- The value type `IPv6Addr` lives in Cedar's namespace; re-export so the short name resolves in
-- the generated `spec.lean`/`parser.lean` (which open only THIS caller namespace), as in IPv4.
export Cedar.Spec.Ext.IPAddr (IPv6Addr)

/-- Unsigned value of a hex-digit string (`"1a" ↦ 26`). PRECONDITION: `s` is a run of 1–4 hex
    digits, guaranteed by the grammar's `hexDigit{1,4}` (via `decode`); a non-hex char folds to
    a total-but-unspecified value, exactly as `readNat` treats non-decimal input. -/
def readHex (s : String) : Nat :=
  s.foldl (fun n c =>
    n * 16 +
      (if c.isDigit then c.toNat - '0'.toNat
       else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
       else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
       else 0)) 0

/-- Structured value (`value'` escape): the eight `H16` group strings → Cedar's `IPv6Addr` (a
    128-bit number, `a₀ ++ … ++ a₇`). Takes the groups as a `List String` (the `[H16]` list
    capture) and reads each as a 16-bit hex group via `readHex`. On the grammar-guaranteed
    eight-group input the list has exactly eight entries; a defensive `getD 0` pads a short list
    (unreachable on well-formed input, where `rep … {8}` pins the count). Reuses Cedar's own
    `IPv6Addr.mk`. -/
def toV6Addr (groups : List String) : IPv6Addr :=
  let g (i : Nat) : BitVec 16 := BitVec.ofNat 16 (readHex (groups.getD i ""))
  IPv6Addr.mk (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7)

triptych IPv6 where
  grammar
    V6Addr ::= rep H16 sepBy ":" {8}
    H16    ::= hexDigit{1,4}
  value'
    toV6Addr [H16]
  to "Triptych/Examples/IPv6"

-- The generated verified parser (`String → Option IPv6Addr`), built from the eight list-captured
-- `H16` groups, run on sample strings:
#eval IPv6.parse "1:2:3:4:5:6:7:8"          -- some 0x0001000200030004…0008  (8 groups)
#eval IPv6.parse "dead:beef:0:0:0:0:0:1"     -- some … (hex groups)
#eval IPv6.parse "1:2:3:4"                    -- none  (4 groups ≠ 8)
#eval IPv6.parse "1:2:3:4:5:6:7:12345"        -- none  (5 hex digits > 4)
#eval IPv6.parse "1::4"                        -- none  (`::` out of scope)

end Triptych.Examples.IPv6
