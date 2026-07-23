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
# Grammar denotation → `IsWf`

The interpreter that gives the deep `Grammar` AST its meaning as a well-formedness
predicate `IsWf : String → Prop`, matching the doc's `∃ components, str = asString`
shape (e.g. `IsWfV4`, `IsWfDatetime`).

Design (note §2): the grammar is a non-recursive DAG, so its denotation is a **flat
`Prop`** — an existential over the substrings matched by each symbol, conjoined with
per-terminal token predicates and the concatenation `str = s₁ ++ s₂ ++ …`. There is no
`inductive` derivation relation. Ref-recursion (a nonterminal referencing another) is
bounded by **fuel** = the number of productions (a DAG cannot chain refs longer than
that); the fuel is a definitional device, not an operational one — this is a `Prop`,
not a parser.

Scope of this increment: the recognition predicate `IsWf` only. The computational
inverse `decode : String → Option Env` (with its roundtrip lemma) and decidability of
`IsWf` are follow-on milestones.
-/

namespace Triptych

/-- A character satisfies a token class. -/
def TokClass.mem : TokClass → Char → Prop
  | .digit,    c => '0' ≤ c ∧ c ≤ '9'
  | .hexDigit, c => ('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'f') ∨ ('A' ≤ c ∧ c ≤ 'F')
  | .bit,      c => c = '0' ∨ c = '1'

instance (tok : TokClass) : DecidablePred tok.mem := by
  intro c; cases tok <;> unfold TokClass.mem <;> infer_instance

/-- Every character of `s` is in the token class (and `s` is nonempty is handled by
    `LenSpec`, which always requires ≥ 1 char in this grammar class). -/
def TokClass.all (tok : TokClass) (s : String) : Prop :=
  ∀ c ∈ s.toList, tok.mem c

instance (tok : TokClass) (s : String) : Decidable (tok.all s) := by
  unfold TokClass.all; infer_instance

/-- A length `n` satisfies a `LenSpec`. -/
def LenSpec.sat : LenSpec → Nat → Prop
  | .exactly k,    n => n = k
  | .between lo hi, n => lo ≤ n ∧ n ≤ hi
  | .atLeastOne,   n => 1 ≤ n

instance (len : LenSpec) (n : Nat) : Decidable (len.sat n) := by
  cases len <;> unfold LenSpec.sat <;> infer_instance

/-- A string matches a terminal `term tok len`: all chars in `tok`, length per `len`. -/
def matchesTerm (tok : TokClass) (len : LenSpec) (s : String) : Prop :=
  tok.all s ∧ len.sat s.length

instance (tok : TokClass) (len : LenSpec) (s : String) : Decidable (matchesTerm tok len s) := by
  unfold matchesTerm; infer_instance

/-! ## Readable leaf predicates

Named predicates matching the hand-written specs' vocabulary (`IsDigits`,
`IsFixedDigits`, …), so the generated `term`-symbol conditions read like the doc
(`IsDigits s`) instead of `(TokClass.digit).all s ∧ (LenSpec.atLeastOne).sat s.length`.
The synthesizer (`Triptych.symPred`) emits these. Definitionally, each is `matchesTerm`
at the corresponding `TokClass`/`LenSpec`, so the denotation semantics is unchanged. -/

/-- `Digit⁺`: a non-empty run of decimal digits. (= `matchesTerm .digit .atLeastOne`.) -/
def IsDigits (s : String) : Prop := TokClass.digit.all s ∧ 1 ≤ s.length
/-- `HexDigit⁺`: a non-empty run of hex digits. -/
def IsHexDigits (s : String) : Prop := TokClass.hexDigit.all s ∧ 1 ≤ s.length
/-- `Bit⁺`: a non-empty run of binary digits. -/
def IsBits (s : String) : Prop := TokClass.bit.all s ∧ 1 ≤ s.length
/-- `Digit{n}`: a decimal-digit string of exactly `n` characters. -/
def IsFixedDigits (n : Nat) (s : String) : Prop := TokClass.digit.all s ∧ s.length = n
/-- `HexDigit{n}`. -/
def IsFixedHexDigits (n : Nat) (s : String) : Prop := TokClass.hexDigit.all s ∧ s.length = n
/-- `Bit{n}`: a binary string of exactly `n` bits. -/
def IsFixedBits (n : Nat) (s : String) : Prop := TokClass.bit.all s ∧ s.length = n
/-- `Digit{lo,hi}`: a decimal-digit string of `lo`–`hi` characters. -/
def IsDigitsBetween (lo hi : Nat) (s : String) : Prop :=
  TokClass.digit.all s ∧ lo ≤ s.length ∧ s.length ≤ hi
/-- `HexDigit{lo,hi}`. -/
def IsHexDigitsBetween (lo hi : Nat) (s : String) : Prop :=
  TokClass.hexDigit.all s ∧ lo ≤ s.length ∧ s.length ≤ hi
/-- `Bit{lo,hi}`: a binary string of `lo`–`hi` bits. -/
def IsBitsBetween (lo hi : Nat) (s : String) : Prop :=
  TokClass.bit.all s ∧ lo ≤ s.length ∧ s.length ≤ hi

instance (s : String) : Decidable (IsDigits s) := by unfold IsDigits; infer_instance
instance (s : String) : Decidable (IsHexDigits s) := by unfold IsHexDigits; infer_instance
instance (s : String) : Decidable (IsBits s) := by unfold IsBits; infer_instance
instance (n : Nat) (s : String) : Decidable (IsFixedDigits n s) := by unfold IsFixedDigits; infer_instance
instance (n : Nat) (s : String) : Decidable (IsFixedHexDigits n s) := by unfold IsFixedHexDigits; infer_instance
instance (n : Nat) (s : String) : Decidable (IsFixedBits n s) := by unfold IsFixedBits; infer_instance
instance (lo hi : Nat) (s : String) : Decidable (IsDigitsBetween lo hi s) := by unfold IsDigitsBetween; infer_instance
instance (lo hi : Nat) (s : String) : Decidable (IsHexDigitsBetween lo hi s) := by unfold IsHexDigitsBetween; infer_instance
instance (lo hi : Nat) (s : String) : Decidable (IsBitsBetween lo hi s) := by unfold IsBitsBetween; infer_instance

mutual

/-- Denotation of a symbol against a string, with `fuel` bounding ref-recursion. -/
def matchesSym (g : Grammar) : Nat → Sym → String → Prop
  | _,      .lit l,        s => s = l
  | _,      .term tok len, s => matchesTerm tok len s
  | fuel,   .rep sep item lo hi, s =>
      -- `item (sep item)*`, item-count in `[lo, hi]`: some list of `parts`, each matching
      -- `item`, joined by `sep`, equals `s`, with the count within bounds.
      ∃ parts : List String,
        lo ≤ parts.length
          ∧ (∀ h, hi = some h → parts.length ≤ h)
          ∧ (∀ p ∈ parts, matchesSym g fuel item p)
          ∧ s = String.intercalate sep parts
  | 0,      .ref _,        _ => False          -- out of fuel (cannot happen in a DAG)
  | fuel+1, .ref name,     s =>
      match g.prod? name with
      | none   => False                        -- unresolved reference
      | some p => matchesProd g fuel p s

/-- Denotation of a sequence (concatenation) against a string: split `s` so each item
    matches its piece in order. An optional item may instead be absent. -/
def matchesSeq (g : Grammar) : Nat → Seq → String → Prop
  | _,    [],           s => s = ""
  | fuel, item :: rest, s =>
      if item.optional then
        (∃ s1 s2, s = s1 ++ s2 ∧ matchesSym g fuel item.sym s1 ∧ matchesSeq g fuel rest s2)
          ∨ matchesSeq g fuel rest s                              -- present ∨ absent
      else
        ∃ s1 s2, s = s1 ++ s2 ∧ matchesSym g fuel item.sym s1 ∧ matchesSeq g fuel rest s2

/-- Denotation of a production (alternation): some alternative matches. -/
def matchesProd (g : Grammar) (fuel : Nat) (p : Production) (s : String) : Prop :=
  ∃ alt ∈ p.alts, matchesSeq g fuel alt s

end

/-- Well-formedness: the string matches the start production. Fuel = number of
    productions (DAG-depth backstop). `False` if the start symbol is undefined. -/
def IsWf (g : Grammar) (s : String) : Prop :=
  match g.startProd? with
  | none   => False
  | some p => matchesProd g g.prods.length p s

/-- Per-production well-formedness: `s` matches production named `name` in `g`. `False`
    if the name is undefined. This is the *named handle* the command emits one of per
    production (as `<Name>.<Production>.isWf`), so contract-theorem proofs can decompose
    along productions (mirroring the hand specs' `DateComponents.syntaxWf`,
    `IsWfV4`, …). Fuel = #productions, the same DAG-depth backstop as `IsWf`; since the
    reference graph is acyclic this never runs out on well-formed grammars. -/
def IsWfProd (g : Grammar) (name : String) (s : String) : Prop :=
  match g.prod? name with
  | none   => False
  | some p => matchesProd g g.prods.length p s

/-- The top-level `IsWf` is exactly the start production's `IsWfProd`. -/
theorem isWf_eq_isWfProd_start (g : Grammar) (s : String) :
    IsWf g s = IsWfProd g g.start s := by
  unfold IsWf IsWfProd Grammar.startProd?
  rfl

end Triptych
