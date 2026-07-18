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

import FormatSpec.Grammar
import FormatSpec.Classify

/-!
# Example grammars (validation of the core type)

Hand-written `Grammar` values transcribing the `::=` grammars from
`doc/CedarDoc/*.lean`, to check the core type expresses the intended class before the
DSL is built. These double as classifier fixtures. Value functions are NOT here — they
are supplied separately (as arbitrary Lean terms) when generating the spec.
-/

namespace FormatSpec.Examples

open FormatSpec

/-- Helper: a required symbol item. -/
private def req (s : Sym) : SymItem := { sym := s }
/-- Helper: an optional symbol item (`[X]`). -/
private def opt (s : Sym) : SymItem := { sym := s, optional := true }

/-- Cedar `Decimal`, transcribing the doc grammar:
```
Decimal  ::= Integer '.' Fraction
Integer  ::= ['-'] Digit⁺
Fraction ::= Digit{1,4}
```
(`Digit` is inlined as a `term` rather than a named production.) -/
def decimal : Grammar where
  start := "Decimal"
  prods := [
    { name := "Decimal", alts := [[req (.ref "Integer"), req (.lit "."), req (.ref "Fraction")]] },
    { name := "Integer", alts := [[opt (.lit "-"), req (.term .digit .atLeastOne)]] },
    { name := "Fraction", alts := [[req (.term .digit (.between 1 4))]] }
  ]

/-- IPv4 (no prefix, first cut): four decimal groups separated by `.`.
```
IPv4  ::= Group '.' Group '.' Group '.' Group
Group ::= Digit{1,3}
``` -/
def ipv4 : Grammar where
  start := "IPv4"
  prods := [
    { name := "IPv4", alts := [[
        req (.ref "Group"), req (.lit "."), req (.ref "Group"), req (.lit "."),
        req (.ref "Group"), req (.lit "."), req (.ref "Group") ]] },
    { name := "Group", alts := [[req (.term .digit (.between 1 3))]] }
  ]

/-- A deliberately cyclic grammar, to exercise the acyclicity check. -/
def cyclic : Grammar where
  start := "A"
  prods := [
    { name := "A", alts := [[req (.ref "B")]] },
    { name := "B", alts := [[req (.ref "A")]] }
  ]

-- The doc-transcribed grammars are in-class: references resolve and graph is acyclic.
-- (`#guard`: build-time computational checks, no theorem, no axiom.)
#guard decimal.ok = true
#guard ipv4.ok = true
#guard decimal.isAcyclic = true
#guard ipv4.refsResolve = true
-- The cyclic grammar is correctly rejected by the acyclicity check.
#guard cyclic.isAcyclic = false
#guard cyclic.ok = false

end FormatSpec.Examples
