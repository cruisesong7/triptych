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

import Triptych.Architecture.Denote
import Triptych.Theorems.Roundtrip
import Triptych.Architecture.Assemble

/-!
# Reconciliation: engine `IsWf` ⟺ inlined surface `IsWf.<Prod>`

The generator emits two well-formedness artifacts for each grammar (design note §16; see
`Docs/DESIGN.md`):

* the **engine** `IsWf g` — the generic `Grammar`-interpreter denotation (`Denote`), which
  carries `DecidablePred` (via the `decode` roundtrip, `Roundtrip`) and drives `decode`; and
* the **surface** `<Name>.IsWf.<Prod>` — readable, inlined per-production predicates
  (`Emit`) that read like the hand-written specs (`∃ integer fraction, s = integer ++ …`).

Keeping both is only sound if they denote the *same* predicate. This module supplies the
reusable lemmas the generator's emitted equivalence proof (`<Name>.IsWf_equiv`) is built
from, so the two can never silently drift: readability for the human auditor, decidability
+ execution for the machine, PROVEN identical.

The lemmas here are grammar-generic (about `matchesProd`/`matchesSeq`). The emitted proof
per production is a fixed skeleton — reduce `IsWfProd`/`matchesProd` to the sequence form,
resolve nonterminal refs to their sibling equivalence lemmas, unfold the surface predicate,
then close with a uniform normalize-then-`grind` step. The skeleton branches only on the
sequence shape the emitter itself chose (`seqPeel` vs `seqAllOptional`) and on single- vs
multi-alternative productions.
-/

namespace Triptych

/-- A single-alternative production matches iff its one sequence matches. -/
theorem matchesProd_single (g : Grammar) (fuel : Nat) (nm : String) (alt : Seq) (s : String) :
    matchesProd g fuel (Production.mk nm [alt]) s ↔ matchesSeq g fuel alt s := by
  simp [matchesProd]

/-- Peel one OPTIONAL item off a sequence into the surface "empty-or-well-formed" form:
    the engine's `present ∨ absent` becomes a single split whose head piece is either empty
    or matches the symbol. This is exactly the shape `Emit.seqAllOptional` produces, so it
    turns the engine's `O(2ⁿ)` present/absent tree into the surface's flat `O(n)` chain. -/
theorem matchesSeq_opt_cons (g : Grammar) (fuel : Nat) (item : SymItem) (rest : Seq) (s : String)
    (hopt : item.optional = true) :
    matchesSeq g fuel (item :: rest) s ↔
    ∃ p r, s = p ++ r ∧ (p = "" ∨ matchesSym g fuel item.sym p) ∧ matchesSeq g fuel rest r := by
  rw [matchesSeq.eq_2]; simp only [hopt, if_true]
  constructor
  · rintro (⟨s1, s2, hs, hP, hQ⟩ | hQ)
    · exact ⟨s1, s2, hs, Or.inr hP, hQ⟩
    · exact ⟨"", s, by simp, Or.inl rfl, hQ⟩
  · rintro ⟨p, r, hs, (hp | hP), hQ⟩
    · subst hp; right; rw [hs]; simpa using hQ
    · exact Or.inl ⟨p, r, hs, hP, hQ⟩

/-! ## Repetition bridge

The engine `matchesSym … (Sym.rep …)` denotation states the upper bound as
`∀ h, hi = some h → parts.length ≤ h` (uniform over `Option`), while the emitted surface
predicate (`Emit.symPred`) reads it in the branch the emitter already knows: `True` when
`hi = none`, `parts.length ≤ h` when `hi = some h`. This lemma normalizes the engine form
to that readable branch, so the emitted `matchesRef` proof reconciles a `rep`-containing
production. (The inner `∀ p ∈ parts, matchesSym … item …` collapses to the item's surface
predicate via the sibling `matchesRef`/leaf lemmas, fired under the binder by `simp only`.) -/
theorem matchesSym_rep_iff (g : Grammar) (fuel : Nat) (sep : String) (item : Sym)
    (lo : Nat) (hi : Option Nat) (s : String) :
    matchesSym g fuel (Sym.rep sep item lo hi) s ↔
      ∃ parts : List String,
        lo ≤ parts.length
          ∧ (match hi with | none => True | some h => parts.length ≤ h)
          ∧ (∀ p ∈ parts, matchesSym g fuel item p)
          ∧ s = String.intercalate sep parts := by
  simp only [matchesSym]
  constructor <;> rintro ⟨parts, hlo, hhi, hitem, hs⟩ <;> refine ⟨parts, hlo, ?_, hitem, hs⟩
  · cases hi with
    | none => trivial
    | some h => exact hhi h rfl
  · cases hi with
    | none => intro h hcon; exact absurd hcon (by simp)
    | some h => intro h' heq; cases heq; exact hhi

/-! ## Leaf-collapse bridges

Each readable leaf predicate (`IsDigits`, `IsFixedDigits`, …) is *definitionally* the
`matchesTerm` at its `TokClass`/`LenSpec` (see `Denote`). These lemmas state that equation
so the emitted proof can feed it to `simp`/`grind`, bridging the engine's `matchesTerm` to
the surface leaf vocabulary. All hold by `rfl`. -/

theorem IsDigits_matchesTerm (s : String) :
    matchesTerm TokClass.digit LenSpec.atLeastOne s = IsDigits s := rfl
theorem IsHexDigits_matchesTerm (s : String) :
    matchesTerm TokClass.hexDigit LenSpec.atLeastOne s = IsHexDigits s := rfl
theorem IsFixedDigits_matchesTerm (n : Nat) (s : String) :
    matchesTerm TokClass.digit (LenSpec.exactly n) s = IsFixedDigits n s := rfl
theorem IsFixedHexDigits_matchesTerm (n : Nat) (s : String) :
    matchesTerm TokClass.hexDigit (LenSpec.exactly n) s = IsFixedHexDigits n s := rfl
theorem IsDigitsBetween_matchesTerm (lo hi : Nat) (s : String) :
    matchesTerm TokClass.digit (LenSpec.between lo hi) s = IsDigitsBetween lo hi s := rfl
theorem IsHexDigitsBetween_matchesTerm (lo hi : Nat) (s : String) :
    matchesTerm TokClass.hexDigit (LenSpec.between lo hi) s = IsHexDigitsBetween lo hi s := rfl
theorem IsBits_matchesTerm (s : String) :
    matchesTerm TokClass.bit LenSpec.atLeastOne s = IsBits s := rfl
theorem IsFixedBits_matchesTerm (n : Nat) (s : String) :
    matchesTerm TokClass.bit (LenSpec.exactly n) s = IsFixedBits n s := rfl
theorem IsBitsBetween_matchesTerm (lo hi : Nat) (s : String) :
    matchesTerm TokClass.bit (LenSpec.between lo hi) s = IsBitsBetween lo hi s := rfl

/-! ## Reader agreement (surface component-string readers ⟺ `Env` readers)

The generated surface `<Name>.value`/`Constraints` read each captured component as a STRING
via `natOf`/`intOf`/`lenOf`/`signOf` applied to `(envOf g s c).getD ""`, while the engine's
`ValExpr.eval`/`Constraint.eval` read the same capture via `Env.natVal`/… on the `Env`
directly. These agree — an absent capture (`none`) and the surface's `""` fallback denote the
same value by construction of the readers. Fed to the emitted `<Name>.IsValid_equiv` proof so
the surface `SatisfiesConstraints` reconciles with the engine `satisfiesConstraints`. -/

theorem readInt_empty : readInt "" = 0 := by unfold readInt; simp [readNat]

@[simp] theorem natOf_getD (env : Env) (f : String) : natOf ((env f).getD "") = env.natVal f := by
  unfold natOf Env.natVal; cases env f <;> simp [readNat]
@[simp] theorem intOf_getD (env : Env) (f : String) : intOf ((env f).getD "") = env.intVal f := by
  unfold intOf Env.intVal; cases h : env f <;> simp; rintro rfl; exact readInt_empty.symm
@[simp] theorem lenOf_getD (env : Env) (f : String) : lenOf ((env f).getD "") = env.lenVal f := by
  unfold lenOf Env.lenVal; cases env f <;> simp
@[simp] theorem signOf_getD (env : Env) (f : String) : signOf ((env f).getD "") = env.signVal f := by
  unfold signOf Env.signVal; cases env f <;> simp

end Triptych
