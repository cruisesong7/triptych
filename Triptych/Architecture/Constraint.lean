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

import Triptych.Architecture.Value

/-!
# The constraint-DSL: deep-embedded predicates, auto-classified

The `constraints` section of `format_spec` lists predicates. Like the value-DSL this is
a **deep embedding**: each constraint elaborates to an inspectable `Constraint` AST, so
the tool can (design note §16.1/§16.3):

* **auto-classify** each constraint by value-dependence:
  - references only capture strings (e.g. `noLeadingZero X`) → folds into `IsWf`;
  - references a value expression (e.g. `nat X ≤ 255`, the `Int64` bound) → folds into
    `SatisfiesConstraints`.
* keep the two layers separate so `IsWf` stays value-free (decidable unconditionally).

This is the "dynamic input validation" layer (CoStar++'s semantic predicates), made
first-class and possibly non-context-free (bounds on computed values, cross-field).

Scope of this increment: the `Constraint` AST + its denotation + the classifier
(`isValueDependent`). Wiring into the `format_spec` command's `constraints` section
(replacing the raw-term capture) is the following step.
-/

namespace Triptych

/-- A cardinality operator over the presence of a set of captures — the SAT-community
    "≥ k / ≤ k / = k of these hold" over the presence booleans (a capture is *present* iff
    its matched string is nonempty). -/
inductive CardOp where
  | atLeast   -- `≥ k` present
  | atMost    -- `≤ k` present
  | exactlyK  -- `= k` present  (`exactly` clashes with `LenSpec.exactly` naming; use `exactlyK`)
  deriving Repr, Inhabited, DecidableEq

/-- A constraint predicate over the capture environment. Two syntactic flavors:
    *string* predicates (over one capture's matched substring) and *value* predicates
    (comparisons of `ValExpr` value expressions). -/
inductive Constraint where
  /-- `noLeadingZero X` — capture `X` has no leading zero unless it is exactly `"0"`
      (`startsWith "0" → s = "0"`). The pervasive IPAddr canonical-nat rule. STRING. -/
  | noLeadingZero (field : String)
  /-- `X = <lit>` — capture `X`'s matched string equals a literal. STRING. -/
  | strEq (field : String) (lit : String)
  /-- Cardinality over presence: the number of the given captures that are *present*
      (nonempty) is `≥/≤/= k` (per `op`). STRING (no computed value). ASSERTS presence, so an
      absent/empty capture contributes 0. Surface forms use SET braces: `atLeast k {Xs}`,
      `atMost k {Xs}`, `exactly k {Xs}`; `nonempty X` = `atLeast 1 {X}`. The generalization of
      the "at least one component present" rule over an all-optional run (Duration/IPAddr). -/
  | card (op : CardOp) (k : Nat) (fields : List String)
  /-- `a ≤ b` — value comparison of two value expressions (e.g. `nat X ≤ 255`). VALUE. -/
  | le (a b : ValExpr)
  /-- `a < b`. VALUE. -/
  | lt (a b : ValExpr)
  /-- `a = b` — value equality. VALUE. -/
  | eq (a b : ValExpr)
  /-- Conjunction. -/
  | and (a b : Constraint)
  deriving Repr, Inhabited, DecidableEq

/-- Whether a constraint depends on a computed *value* (vs. only capture strings).
    Value-dependent ⟹ folds into `SatisfiesConstraints`; otherwise into `IsWf`. -/
def Constraint.isValueDependent : Constraint → Bool
  | .noLeadingZero _ => false
  | .strEq _ _       => false
  | .card _ _ _      => false
  | .le _ _          => true
  | .lt _ _          => true
  | .eq _ _          => true
  | .and a b         => a.isValueDependent || b.isValueDependent

/-- Denotation of a constraint against a capture environment. Absent captures: a
    string predicate on an absent capture is vacuously true (the symbol wasn't present,
    so its rule does not apply); value predicates read absent captures as `0` via
    `ValExpr.eval`. -/
def Constraint.eval (env : Env) : Constraint → Prop
  | .noLeadingZero f =>
      -- Phrased over `(env f).getD ""` (not `match … none => True`) so it is DEFEQ to the
      -- surface rendering `(x.startsWith "0" → x = "0")`. Equivalent on an absent capture:
      -- `"".startsWith "0"` is `false`, so the implication is vacuously `True` either way.
      (((env f).getD "").startsWith "0" = true → (env f).getD "" = "0")
  | .strEq f l =>
      match env f with
      | some s => s = l
      | none   => True
  | .card op k fields =>
      -- Count present (nonempty) captures; absent optional ⟹ "" ⟹ contributes 0.
      let n := presentCount (fields.map (fun f => (env f).getD ""))
      match op with
      | .atLeast  => k ≤ n
      | .atMost   => n ≤ k
      | .exactlyK => n = k
  | .le a b => a.eval env ≤ b.eval env
  | .lt a b => a.eval env < b.eval env
  | .eq a b => a.eval env = b.eval env
  | .and a b => a.eval env ∧ b.eval env

instance instDecidableEval (env : Env) : (c : Constraint) → Decidable (c.eval env)
  | .noLeadingZero f => by unfold Constraint.eval; infer_instance
  | .strEq f l       => by unfold Constraint.eval; split <;> infer_instance
  | .card op k fs    => by unfold Constraint.eval; split <;> infer_instance
  | .le a b          => by unfold Constraint.eval; infer_instance
  | .lt a b          => by unfold Constraint.eval; infer_instance
  | .eq a b          => by unfold Constraint.eval; infer_instance
  | .and a b         =>
      have := instDecidableEval env a
      have := instDecidableEval env b
      by unfold Constraint.eval; infer_instance

/-- The `IsWf`-side conjunction: only the string (non-value-dependent) constraints. -/
def Constraint.wfPart (env : Env) : Constraint → Prop
  | .and a b => a.wfPart env ∧ b.wfPart env
  | c        => if c.isValueDependent then True else c.eval env

/-- The `SatisfiesConstraints`-side conjunction: only the value-dependent constraints. -/
def Constraint.valPart (env : Env) : Constraint → Prop
  | .and a b => a.valPart env ∧ b.valPart env
  | c        => if c.isValueDependent then c.eval env else True

instance instDecidableWfPart (env : Env) : (c : Constraint) → Decidable (c.wfPart env)
  | .and a b =>
      have := instDecidableWfPart env a
      have := instDecidableWfPart env b
      by unfold Constraint.wfPart; infer_instance
  | .noLeadingZero f => by unfold Constraint.wfPart; split <;> infer_instance
  | .strEq f l       => by unfold Constraint.wfPart; split <;> infer_instance
  | .card op k fs    => by
      unfold Constraint.wfPart; split
      · infer_instance
      · unfold Constraint.eval; split <;> infer_instance
  | .le a b          => by unfold Constraint.wfPart; split <;> infer_instance
  | .lt a b          => by unfold Constraint.wfPart; split <;> infer_instance
  | .eq a b          => by unfold Constraint.wfPart; split <;> infer_instance

instance instDecidableValPart (env : Env) : (c : Constraint) → Decidable (c.valPart env)
  | .and a b =>
      have := instDecidableValPart env a
      have := instDecidableValPart env b
      by unfold Constraint.valPart; infer_instance
  | .noLeadingZero f => by unfold Constraint.valPart; split <;> infer_instance
  | .strEq f l       => by unfold Constraint.valPart; split <;> infer_instance
  | .card op k fs    => by unfold Constraint.valPart; split <;> infer_instance
  | .le a b          => by unfold Constraint.valPart; split <;> infer_instance
  | .lt a b          => by unfold Constraint.valPart; split <;> infer_instance
  | .eq a b          => by unfold Constraint.valPart; split <;> infer_instance

/-- A constraint *entry* in the `constraints` section: either a structured, analyzable
    `Constraint` (the DSL), or the ESCAPE HATCH — an arbitrary decidable predicate on the
    environment with a declared classification (design note §16.7). The escape keeps the
    analyzable `Constraint` AST pure (deriving `Repr`/`DecidableEq`) while never blocking
    a constraint outside the DSL vocabulary. -/
inductive ConstraintEntry where
  /-- A DSL constraint (analyzable). -/
  | dsl (c : Constraint)
  /-- Opaque escape (`opaqueConstraints`): an arbitrary boolean check on the environment,
      carrying its own decision procedure (so no `DecidablePred` plumbing), for constraints
      outside the DSL vocabulary. Always folds into the value side (`valPart`); the earlier
      `IsWf`-vs-value distinction was dropped because for the combined acceptance predicate
      `wfPart ∧ valPart` an opaque entry contributes exactly `check` either way, so the
      classification never affected the result. -/
  | opaque (check : Env → Bool)

/-- Value-dependence of an entry (opaque escapes fold into the value side). -/
def ConstraintEntry.isValueDependent : ConstraintEntry → Bool
  | .dsl c        => c.isValueDependent
  | .opaque _     => true

/-- `IsWf`-side contribution of an entry. -/
def ConstraintEntry.wfPart (env : Env) : ConstraintEntry → Prop
  | .dsl c       => c.wfPart env
  | .opaque _    => True

/-- `SatisfiesConstraints`-side contribution of an entry. -/
def ConstraintEntry.valPart (env : Env) : ConstraintEntry → Prop
  | .dsl c       => c.valPart env
  | .opaque check => check env = true

instance (env : Env) : (e : ConstraintEntry) → Decidable (e.wfPart env)
  | .dsl c        => by unfold ConstraintEntry.wfPart; infer_instance
  | .opaque _     => by unfold ConstraintEntry.wfPart; infer_instance

instance (env : Env) : (e : ConstraintEntry) → Decidable (e.valPart env)
  | .dsl c        => by unfold ConstraintEntry.valPart; infer_instance
  | .opaque _     => by unfold ConstraintEntry.valPart; infer_instance

/-! ## Surface syntax → `Constraint`

A `constraintExpr` category reusing the `valExpr` category
(from `Triptych.Architecture.Value`) for the arithmetic sides of comparisons. -/

open Lean

declare_syntax_cat constraintExpr
syntax "noLeadingZero " ident            : constraintExpr
-- Cardinality over presence (SAT-style): how many of a SET of captures are present. Braces
-- `{X, Y, …}` signal it is a set (not an argument list). `nonempty X` = sugar `atLeast 1 {X}`.
syntax "nonempty " ident                 : constraintExpr
syntax "atLeast " num " {" ident,+ "}"   : constraintExpr
syntax "atMost "  num " {" ident,+ "}"   : constraintExpr
syntax "exactly " num " {" ident,+ "}"   : constraintExpr
syntax ident " = " str                   : constraintExpr   -- string equality
syntax valExpr " ≤ " valExpr             : constraintExpr
syntax valExpr " < " valExpr             : constraintExpr
syntax valExpr " == " valExpr            : constraintExpr   -- value equality (`==` to avoid clash)
-- Closed-interval sugar: `e ∈ [lo, hi]` desugars to `lo ≤ e ∧ e ≤ hi` (no new AST node).
-- Matches the doc's `value ∈ [Int64.MIN, Int64.MAX]`. (Sets/half-open intervals are out
-- of scope — use the `opaque` escape for those.)
syntax valExpr " ∈ " "[" valExpr ", " valExpr "]" : constraintExpr
-- NOTE: the ESCAPE HATCH for constraints outside the DSL vocabulary is NOT a `constraintExpr`
-- form — it is the separate `constraints'` section of `format_spec`
-- (see `Triptych.Architecture.Syntax`),
-- whose entries are raw-Lean `f X Y …` applications built via `opaqueEnvClosure` below.

/-- The comma-separated capture names of a cardinality constraint's `[X, Y, …]` list, as a
    `term` sep-array of quoted strings (for splicing into a `[…]` `List String` literal). -/
private def cardFieldList (is : Syntax.TSepArray `ident ",") : Syntax.TSepArray `term "," :=
  .ofElems (is.getElems.map (fun i => Syntax.mkStrLit i.getId.toString))

/-- The same capture names as `cardFieldList` but as surface-binder *identifiers* (`Days` →
    `days`), for the READABLE `presentCount [days, hours, …]` rendering. -/
private def cardBinderList (is : Syntax.TSepArray `ident ",") : Syntax.TSepArray `term "," :=
  .ofElems (is.getElems.map (fun i =>
    ⟨(mkIdent (Name.mkSimple (surfaceBinder i.getId.toString))).raw⟩))

/-- Translate a `constraintExpr` into a `Constraint` term (DSL forms only). `valueSub`,
    if provided, is substituted for a `value` reference in the arithmetic sides. -/
def elabConstraintWith (valueSub : Option (TSyntax `term)) :
    TSyntax `constraintExpr → MacroM (TSyntax `term)
  | `(constraintExpr| noLeadingZero $i:ident) =>
      `(Constraint.noLeadingZero $(quote i.getId.toString))
  | `(constraintExpr| nonempty $i:ident) =>
      `(Constraint.card CardOp.atLeast 1 [$(quote i.getId.toString)])
  | `(constraintExpr| atLeast $k:num { $is,* }) =>
      `(Constraint.card CardOp.atLeast $k [$(cardFieldList is),*])
  | `(constraintExpr| atMost $k:num { $is,* }) =>
      `(Constraint.card CardOp.atMost $k [$(cardFieldList is),*])
  | `(constraintExpr| exactly $k:num { $is,* }) =>
      `(Constraint.card CardOp.exactlyK $k [$(cardFieldList is),*])
  | `(constraintExpr| $i:ident = $l:str) =>
      `(Constraint.strEq $(quote i.getId.toString) $l)
  | `(constraintExpr| $a:valExpr ≤ $b:valExpr) => do
      `(Constraint.le $(← elabValExprWith valueSub a) $(← elabValExprWith valueSub b))
  | `(constraintExpr| $a:valExpr < $b:valExpr) => do
      `(Constraint.lt $(← elabValExprWith valueSub a) $(← elabValExprWith valueSub b))
  | `(constraintExpr| $a:valExpr == $b:valExpr) => do
      `(Constraint.eq $(← elabValExprWith valueSub a) $(← elabValExprWith valueSub b))
  | `(constraintExpr| $e:valExpr ∈ [ $lo:valExpr , $hi:valExpr ]) => do
      -- desugar to `lo ≤ e ∧ e ≤ hi`
      let et ← elabValExprWith valueSub e
      let lot ← elabValExprWith valueSub lo
      let hit ← elabValExprWith valueSub hi
      `(Constraint.and (Constraint.le $lot $et)
                                  (Constraint.le $et $hit))
  | _ => Macro.throwUnsupported

/-- Translate a `constraintExpr` into a `Constraint` term with no `value` substitution. -/
def elabConstraint (c : TSyntax `constraintExpr) : MacroM (TSyntax `term) :=
  elabConstraintWith none c

/-- Build the engine's `Env → Bool` closure from the author's function `f` applied to
    capture names `is`: `fun env => f ((env "X").getD "") ((env "Y").getD "") …`. The
    `envOf`/`getD ""` plumbing lives HERE, so the author's `f` sees only plain component
    strings — the surface `constraints'` entry `f X Y` reads as an ordinary Lean application.
    Used by the `constraints'` escape section (see `Triptych.Architecture.Syntax`). -/
def opaqueEnvClosure (f : TSyntax `ident) (is : Array (TSyntax `ident)) :
    MacroM (TSyntax `term) := do
  let args : Array (TSyntax `term) ← is.mapM (fun i =>
    `(((env : Env) $(Syntax.mkStrLit i.getId.toString)).getD ""))
  `(fun env : Env => $f $args*)

/-- Translate a `constraintExpr` into a `ConstraintEntry` term (all DSL forms wrap in
    `.dsl`; the raw-Lean escape lives in the separate `constraints'` section, not here).
    `valueSub` threads `value` references. -/
def elabEntryWith (valueSub : Option (TSyntax `term)) :
    TSyntax `constraintExpr → MacroM (TSyntax `term)
  | c => do `(ConstraintEntry.dsl $(← elabConstraintWith valueSub c))

/-- `elabEntry` with no `value` substitution. -/
def elabEntry (c : TSyntax `constraintExpr) : MacroM (TSyntax `term) :=
  elabEntryWith none c

/-- Translate a `constraintExpr` into a READABLE `Prop` term over environment `env`,
    using the readable value readers (`env.intVal "X" ≤ 255`, etc.) — the surface/pretty
    counterpart of the `Constraint` AST, just as `<Name>.value` is for `ValExpr`. Emitted
    as the generated `<Name>.SatisfiesConstraints`. `valueSub` substitutes a readable term
    for a `value` reference. -/
def elabConstraintReadable (valueSub : Option (TSyntax `term)) :
    TSyntax `constraintExpr → MacroM (TSyntax `term)
  | `(constraintExpr| noLeadingZero $i:ident) =>
      let b := mkIdent (Name.mkSimple (surfaceBinder i.getId.toString))
      `(($b).startsWith "0" → $b = "0")
  | `(constraintExpr| nonempty $i:ident) =>
      let b := mkIdent (Name.mkSimple (surfaceBinder i.getId.toString))
      `($b ≠ "")
  | `(constraintExpr| atLeast $k:num { $is,* }) =>
      `(presentCount [$(cardBinderList is),*] ≥ $k)
  | `(constraintExpr| atMost $k:num { $is,* }) =>
      `(presentCount [$(cardBinderList is),*] ≤ $k)
  | `(constraintExpr| exactly $k:num { $is,* }) =>
      `(presentCount [$(cardBinderList is),*] = $k)
  | `(constraintExpr| $i:ident = $l:str) =>
      let b := mkIdent (Name.mkSimple (surfaceBinder i.getId.toString))
      `($b = $l)
  | `(constraintExpr| $a:valExpr ≤ $b:valExpr) => do
      `($(← elabValReadableWith valueSub a) ≤ $(← elabValReadableWith valueSub b))
  | `(constraintExpr| $a:valExpr < $b:valExpr) => do
      `($(← elabValReadableWith valueSub a) < $(← elabValReadableWith valueSub b))
  | `(constraintExpr| $a:valExpr == $b:valExpr) => do
      `($(← elabValReadableWith valueSub a) = $(← elabValReadableWith valueSub b))
  | `(constraintExpr| $e:valExpr ∈ [ $lo:valExpr , $hi:valExpr ]) => do
      let et  ← elabValReadableWith valueSub e
      let lot ← elabValReadableWith valueSub lo
      let hit ← elabValReadableWith valueSub hi
      `($lot ≤ $et ∧ $et ≤ $hit)
  | _ => Macro.throwUnsupported

/-- Does a `valExpr` reference the `value` keyword? -/
partial def valExprUsesValue : TSyntax `valExpr → Bool
  | `(valExpr| value) => true
  | `(valExpr| ( $e:valExpr )) => valExprUsesValue e
  | `(valExpr| $a:valExpr + $b:valExpr) => valExprUsesValue a || valExprUsesValue b
  | `(valExpr| $a:valExpr - $b:valExpr) => valExprUsesValue a || valExprUsesValue b
  | `(valExpr| $a:valExpr * $b:valExpr) => valExprUsesValue a || valExprUsesValue b
  | `(valExpr| $a:valExpr ^ $b:valExpr) => valExprUsesValue a || valExprUsesValue b
  | _ => false

/-- Does a `constraintExpr` reference `value`? -/
def constraintUsesValue : TSyntax `constraintExpr → Bool
  | `(constraintExpr| $a:valExpr ≤ $b:valExpr) => valExprUsesValue a || valExprUsesValue b
  | `(constraintExpr| $a:valExpr < $b:valExpr) => valExprUsesValue a || valExprUsesValue b
  | `(constraintExpr| $a:valExpr == $b:valExpr) => valExprUsesValue a || valExprUsesValue b
  | `(constraintExpr| $e:valExpr ∈ [ $lo:valExpr , $hi:valExpr ]) =>
      valExprUsesValue e || valExprUsesValue lo || valExprUsesValue hi
  | _ => false

/-- Capture names referenced by a `constraintExpr` (for surface parameter binders). -/
def constraintCaptures : TSyntax `constraintExpr → List String
  | `(constraintExpr| noLeadingZero $i:ident) => [i.getId.toString]
  | `(constraintExpr| nonempty $i:ident)      => [i.getId.toString]
  | `(constraintExpr| atLeast $_:num { $is,* }) => (is.getElems.map (·.getId.toString)).toList
  | `(constraintExpr| atMost $_:num { $is,* })  => (is.getElems.map (·.getId.toString)).toList
  | `(constraintExpr| exactly $_:num { $is,* }) => (is.getElems.map (·.getId.toString)).toList
  | `(constraintExpr| $i:ident = $_:str)      => [i.getId.toString]
  | `(constraintExpr| $a:valExpr ≤ $b:valExpr) => (valExprCaptures a ++ valExprCaptures b).eraseDups
  | `(constraintExpr| $a:valExpr < $b:valExpr) => (valExprCaptures a ++ valExprCaptures b).eraseDups
  | `(constraintExpr| $a:valExpr == $b:valExpr) => (valExprCaptures a ++ valExprCaptures b).eraseDups
  | `(constraintExpr| $e:valExpr ∈ [ $lo:valExpr , $hi:valExpr ]) =>
      (valExprCaptures e ++ valExprCaptures lo ++ valExprCaptures hi).eraseDups
  | _ => []

/-- `cstr% <predicate>` : a `Constraint` value from the constraint-DSL. -/
macro "cstr% " c:constraintExpr : term => elabConstraint c

end Triptych
