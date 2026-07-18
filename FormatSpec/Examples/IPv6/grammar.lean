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
# IPv6 example — `hexDigit` and GROUP repetition (`rep … sepBy …`)

Transcribes the IPv6 fragment of `doc/CedarDoc/IPAddr.lean`. The full grammar is
```
V6Addr ::= H16 (':' H16){7}                        -- 8 groups, no '::'
         | [H16 (':' H16)*] '::' [H16 (':' H16)*]  -- one '::', sides total < 8
H16    ::= HexDigit{1,4}     -- value ≤ 0xffff (automatic from ≤ 4 hex digits)
```

The first alternative — the full **eight-group** form — is now expressed DIRECTLY with the
`rep` combinator: `rep H16 sepBy ":" {8}` = eight `H16`s joined by `":"`. This is a single
grammar node (a repeated *group*, not eight unrolled refs), so it decodes, reconciles, and
proves at a fixed cost independent of the count — the earlier 4-group truncation (a scaling
wall in the old unroll-everything closer) is GONE. The `H16 ≤ 0xffff` bound is automatic from
`hexDigit{1,4}` (≤ 4 hex digits), so the grammar alone captures it.

ONE honest truncation remains vs the full grammar:

* **The `::` (gap) form is OMITTED.** It is a two-sided variable-arity form
  (`[H16 (':' H16)*] '::' [H16 (':' H16)*]`) whose split point across the fixed `::` boundary
  is not a single separated list — it needs the item counts on BOTH sides plus the "sides
  total < 8" cross-constraint. `rep` covers one separated list; the two-sided `::` split is
  the case the design (§5–§6) flags for a hand-written `decode`. Expressing it would need
  either an alternation of fixed splits or a second repetition primitive; out of scope here.

Note the `rep` well-formedness side conditions the generator enforces (see `Sym.repOk` /
`FormatSpec.decodeSome_iff_IsWf`): the separator must be non-empty and the lower bound ≥ 1.
Both hold here (`":"`, `{8}`); the DSL rejects violations at parse time. Writes `spec.lean`
beside this file.
-/

namespace FormatSpec.Examples.IPv6
open FormatSpec

format_spec IPv6 where
  grammar
    V6Addr ::= rep H16 sepBy ":" {8}
    H16    ::= hexDigit{1,4}
  to "FormatSpec/Examples/IPv6"

#check (IPv6.IsWf.V6Addr : String → Prop)

#eval decide (IPv6.IsWf.V6Addr "1:2:3:4:5:6:7:8")          -- true (8 groups)
#eval decide (IPv6.IsWf.V6Addr "2001:db8:0:0:0:0:0:1")     -- true (case-insensitive hex)
#eval decide (IPv6.IsWf.V6Addr "1:2:3:4")                  -- false (4 groups ≠ 8)
#eval decide (IPv6.IsWf.V6Addr "1:2:3:4:5:6:7:12345")      -- false (5 hex digits > 4)
#eval decide (IPv6.IsWf.V6Addr "1::4")                     -- false (`::` out of scope)

#check (IPv6.IsWf_equiv : ∀ s, IsWf IPv6.grammar s ↔ IPv6.IsWf.V6Addr s)
example : DecidablePred IPv6.IsWf.V6Addr := inferInstance

end FormatSpec.Examples.IPv6
