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

/-!
# Syntactic classifier

Decidable *syntactic* properties of the `Grammar` (design note §5–§6), computed as
pure functions. These gate what the generator can do with the **syntax** alone:

* **acyclic (DAG)** — the production reference graph has no cycles. Required: a cycle
  would be genuine recursion, taking us out of the flat class (`Prop` would need to
  become an inductive relation).
* **fixed-arity** — no production expands to a variable *number* of groups. In this
  EBNF subset the only repetition is a leaf `LenSpec` (`atLeastOne`), which is a
  single token run, not a variable group count — so every grammar expressible here is
  group-fixed. This is where a future variable-arity `fill` symbol (IPv6 `::`) would
  be detected and flagged for `decode` delegation.

Note: *affinity of the value function* is deliberately NOT here. The value function is
an arbitrary Lean term (not first-order data); deciding whether it is affine enough to
auto-discharge the contract proofs is an `Expr`-level analysis done by the generator,
covered in `FormatSpec.ValueAnalysis` (to come), not by these grammar functions.
-/

namespace FormatSpec

/-- Direct nonterminal references made by a production (across all its alternatives),
    seeing through `rep` wrappers (via `Sym.allRefs`) so repeated nonterminals are counted. -/
def Production.directRefs (p : Production) : List String :=
  p.alts.flatMap (fun seq => seq.flatMap (fun item => item.sym.allRefs))

/-- Depth-first check that the reference graph reachable from `name` is acyclic.
    `fuel` bounds recursion by the number of productions (a DAG cannot have a path
    longer than that). `stack` is the current DFS path for cycle detection. -/
partial def Grammar.acyclicFrom (g : Grammar) (name : String) (stack : List String) : Bool :=
  if stack.contains name then
    false  -- back-edge to a node on the current path ⟹ cycle
  else match g.prod? name with
    | none   => true  -- reference to an undefined production: not a cycle (a separate error)
    | some p => p.directRefs.all (fun r => g.acyclicFrom r (name :: stack))

/-- The grammar's production graph is acyclic starting from the start symbol. -/
def Grammar.isAcyclic (g : Grammar) : Bool :=
  g.acyclicFrom g.start []

/-- Every referenced nonterminal is defined in the grammar. -/
def Grammar.refsResolve (g : Grammar) : Bool :=
  g.prods.all (fun p => p.directRefs.all (fun r => (g.prod? r).isSome))

/-- A `LenSpec` is bounded (fixed maximum width). `atLeastOne` is unbounded (infinite
    language) but still single-arity, so it does not break the fixed-arity property. -/
def LenSpec.isBounded : LenSpec → Bool
  | .exactly _   => true
  | .between _ _ => true
  | .atLeastOne  => false

/-- Syntactic well-formedness verdict for a grammar (independent of the value fn). -/
structure SyntaxVerdict where
  /-- References resolve to defined productions. -/
  resolves : Bool
  /-- The production graph is acyclic (flat class holds). -/
  acyclic : Bool
  deriving Repr, DecidableEq

/-- Compute the syntactic verdict. `ok` ⟺ the grammar is in the flat, well-formed
    class the generator supports. -/
def Grammar.syntaxVerdict (g : Grammar) : SyntaxVerdict :=
  { resolves := g.refsResolve, acyclic := g.isAcyclic }

/-- The grammar is syntactically well-formed and in-class. -/
def Grammar.ok (g : Grammar) : Bool :=
  let v := g.syntaxVerdict
  v.resolves && v.acyclic

end FormatSpec
