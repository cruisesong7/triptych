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

import Triptych
import Std.Tactic.BVDecide.LRAT.Parser

/-!
# LRAT text proofs

The text LRAT format accepted by `Std.Tactic.BVDecide.LRAT.Parser.Text`, the parser behind
`bv_decide`'s proof checking. Lean's LRAT *checker* is verified; this parser is not. The
generated parser below returns the same `Array IntAction`, so the two are compared by equality in
`Proofs/Lrat/Conformance.lean`.

Each line is an addition `id lits… 0 rupHints… ratSteps… 0` or a deletion `id d ids… 0`, and
every list element is followed by one space, exactly as the `Std` parser reads them. Identifiers
and literals are decimal numerals with value at least one; leading zeros are accepted, as `Std`
accepts them.

The `value'` section reads one tuple per `Line` with a nested group per RAT step, so the value
function sees the proof's structure rather than flat lists of spans.

Not covered: comment lines (`c …`), which need a negated character class, and the binary
format.
-/

namespace LratExample

open Triptych
open Std.Tactic.BVDecide.LRAT

/-- A decimal numeral of value at least one, possibly with leading zeros. -/
def readPos (text : String) : Nat :=
  text.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

/-- A literal: a positive numeral or `-` followed by one. -/
def readLit (text : String) : Int :=
  if text.startsWith "-" then -(readPos (text.drop 1).toString : Int) else (readPos text : Int)

/-- The RAT pivot: the first literal of the added clause, as `Std` selects it. -/
def pivotOf (clause : Array Int) : Std.Sat.Literal Nat :=
  let lit := clause[0]!
  (lit.natAbs, decide (lit > 0))

/-- The fields read from one proof line: its id, its deletion text (empty for an addition), the
    deleted ids, the clause literals, the RUP hints, and each RAT step's pivot and hints. -/
abbrev LineFields :=
  String × String × List String × List String × List String × List (String × List String)

/-- Build one action exactly as `Std.Tactic.BVDecide.LRAT.Parser.Text.parseAction` does. -/
def toAction : LineFields → IntAction
  | (id, delete, deleted, lits, rup, rat) =>
      let rupHints := (rup.map readPos).toArray
      if !delete.isEmpty then
        .del (deleted.map readPos).toArray
      else
        let clause := (lits.map readLit).toArray
        match clause.size, rat with
        | 0, _ => .addEmpty (readPos id) rupHints
        | _, [] => .addRup (readPos id) clause rupHints
        | _, _ =>
            .addRat (readPos id) clause (pivotOf clause) rupHints
              ((rat.map fun (pivot, hints) =>
                ((readLit pivot).natAbs, (hints.map readPos).toArray)).toArray)

def toActions (lines : List LineFields) : Array IntAction :=
  (lines.map toAction).toArray

/-- `Std` rejects RAT hints on the empty clause. -/
def ratNeedsClause (lines : List (List String × List String)) : Bool :=
  lines.all fun (lits, pivots) => !lits.isEmpty || pivots.isEmpty

-- ANCHOR: lratTriptychSource
triptych Lrat where
  grammar
    Proof    ::= rep Line sepBy "\n" + "\n"
    Line     ::= Id " " Body Cr
    Cr       ::= ["\r"]
    Body     ::= Delete | Add
    Delete   ::= "d " [DelIds] "0"
    DelIds   ::= rep DelId sepBy " " + " "
    DelId    ::= Pos
    Add      ::= [Lits] "0 " [RupHints] [RatSteps] "0"
    Lits     ::= rep Lit sepBy " " + " "
    Lit      ::= Neg | Pos
    RupHints ::= rep RupHint sepBy " " + " "
    RupHint  ::= Pos
    RatSteps ::= rep RatStep sepBy " " + " "
    RatStep  ::= RatPivot [RatTail]
    RatTail  ::= " " RatHints
    RatHints ::= rep RatHint sepBy " " +
    RatHint  ::= Pos
    RatPivot ::= Neg
    Neg      ::= "-" Pos
    Id       ::= Pos
    Pos      ::= [Zeros] NonZero [Digits]
    Zeros    ::= ascii[48,48]+
    NonZero  ::= ascii[49,57]{1}
    Digits   ::= digit+
  value'
    toActions [Line ⟨Id, Delete, [DelId], [Lit], [RupHint], [RatStep ⟨RatPivot, [RatHint]⟩]⟩]
  constraints'
    ratNeedsClause [Line ⟨[Lit], [RatPivot]⟩]
  to "Outputs/Lrat"
-- ANCHOR_END: lratTriptychSource

#eval Lrat.parse "5 1 -2 0 3 4 0\n6 d 1 2 0\n"
#eval Lrat.parse "7 1 2 0 5 -3 1 2 -4 6 0\n"
#eval Lrat.parse "7 0 -3 1 0\n"

end LratExample
