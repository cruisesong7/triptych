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

import Triptych.Architecture.Grammar

/-!
# Conservative static unambiguity analysis

`Grammar.unaryUnique` recognizes a small, useful deterministic grammar fragment:

* the start production contains exactly one required symbol;
* every production reached through a reference also contains exactly one required symbol;
* the path ends in one literal or token run.

Token runs may have any `LenSpec`, including `atLeastOne`: although they enumerate several
prefixes, at most one consumes the complete input. Fuel bounds reference traversal by the
number of productions, so cyclic and overlong paths are rejected.

This is deliberately a sufficient check, not a complete ambiguity decision procedure.
Sequences, optionals, alternatives, and separated repetitions currently return `false`.
`Triptych.Theorems.Unambiguity` proves that `true` implies `GrammarDecodeUnique`.
-/

namespace Triptych

/-- Check that `sym` starts a unary reference path ending in one literal or token run. -/
def Grammar.unaryUniqueFrom (g : Grammar) : Nat → Sym → Bool
  | _, .lit _ => true
  | _, .term _ _ => true
  | _, .rep _ _ _ _ => false
  | 0, .ref _ => false
  | fuel + 1, .ref name =>
      match g.prod? name with
      | some { name := _, alts := [[{ sym := inner, optional := false }]] } =>
          g.unaryUniqueFrom fuel inner
      | _ => false

/-- Conservative grammar-level uniqueness check. A missing start production returns `true`
    because it has no parses; otherwise the start must be a unary deterministic path. -/
def Grammar.unaryUnique (g : Grammar) : Bool :=
  match g.startProd? with
  | none => true
  | some { name := _, alts := [[{ sym := inner, optional := false }]] } =>
      g.unaryUniqueFrom g.prods.length inner
  | _ => false

end Triptych
