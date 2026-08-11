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
# The constraint DSL: deep-embedded predicates with an explicit phase

The `constraints` section of `triptych` lists predicates. Like the value-DSL this is
a **deep embedding**: each constraint elaborates to an inspectable `Constraint` AST, so
the tool can (design note §16.1/§16.3):

* classify each constraint before elaboration by whether its surface syntax explicitly
  references the format's final `value`:
  - capture-only constraints (including `nat X ≤ 255`) fold into `IsWf`;
  - constraints that mention `value` fold into `SatisfiesConstraints`.
* preserve that phase in `ConstraintEntry`, because substituting the format's `ValExpr` for
  `value` would otherwise erase the distinction.

This is the "dynamic input validation" layer (CoStar++'s semantic predicates), made
first-class and possibly non-context-free (bounds on computed values, cross-field).

The phase is intentionally a property of an entry, not of the `Constraint` AST: the same
arithmetic comparison node may constrain a capture-derived number (well-formedness) or the
final computed value (value validity).

**The phase boundary is an author-chosen presentation rule, not a semantic invariant.**
"Mentions the final `value`" is a *syntactic* test on the surface expression, so two
extensionally-equivalent checks can land in different phases: `nat X ∈ [1, 12]` folds into
`IsWf`, while a mathematically-equal bound written through `value` folds into
`SatisfiesConstraints`. This is deliberate, not an inconsistency — the phase records the
author's INTENT ("is this part of what 'well-formed' means, or a constraint on the
interpreted value?"), which cannot be recovered after `value` is substituted by its
`ValExpr` (that is exactly why the phase is stored on the entry rather than re-derived).
The two phases carve the same accepted language either way. When both are present,
`IsValid = IsWf ∧ SatisfiesConstraints`; an absent phase is omitted rather than represented
by a predicate equal to `True`. The split only affects how the spec reads, never which
strings it accepts.
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

/-- A constraint predicate over the capture environment. Classification into format
    well-formedness versus final-value validity is stored by `ConstraintEntry`. -/
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
  /-- `a ≤ b` — comparison of two value expressions (e.g. `nat X ≤ 255`). -/
  | le (a b : ValExpr)
  /-- `a < b`. -/
  | lt (a b : ValExpr)
  /-- `a = b` — arithmetic value equality. -/
  | eq (a b : ValExpr)
  /-- Conjunction. -/
  | and (a b : Constraint)
  deriving Repr, Inhabited, DecidableEq

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

/-- The phase at which a constraint contributes to acceptance. -/
inductive ConstraintPhase where
  /-- Intrinsic format well-formedness; the constraint does not mention the final `value`. -/
  | wellFormed
  /-- A constraint on the format's final computed `value`. -/
  | value
  deriving Repr, Inhabited, DecidableEq

/-- A constraint entry with its phase preserved. Opaque `constraints'` entries are assigned to
    `.wellFormed`; the map form additionally supports repeated-capture list arguments. -/
inductive ConstraintEntry where
  /-- A structured DSL constraint. -/
  | dsl (phase : ConstraintPhase) (c : Constraint)
  /-- An arbitrary scalar-capture predicate supplied through `constraints'`. -/
  | opaque (phase : ConstraintPhase) (check : Env → Bool)
  /-- An arbitrary predicate over the complete capture map. -/
  | opaqueMap (phase : ConstraintPhase) (check : CaptureMap → Bool)

/-- Whether an entry explicitly constrains the final computed value. -/
def ConstraintEntry.isValueDependent : ConstraintEntry → Bool
  | .dsl .wellFormed _    => false
  | .dsl .value _         => true
  | .opaque .wellFormed _ => false
  | .opaque .value _      => true
  | .opaqueMap .wellFormed _ => false
  | .opaqueMap .value _      => true

/-- `IsWf`-side contribution of an entry. -/
def ConstraintEntry.wfPart (m : CaptureMap) : ConstraintEntry → Prop
  | .dsl .wellFormed c    => c.eval m.toEnv
  | .dsl .value _         => True
  | .opaque .wellFormed p => p m.toEnv = true
  | .opaque .value _      => True
  | .opaqueMap .wellFormed p => p m = true
  | .opaqueMap .value _      => True

/-- `SatisfiesConstraints`-side contribution of an entry. -/
def ConstraintEntry.valPart (m : CaptureMap) : ConstraintEntry → Prop
  | .dsl .wellFormed _    => True
  | .dsl .value c         => c.eval m.toEnv
  | .opaque .wellFormed _ => True
  | .opaque .value p      => p m.toEnv = true
  | .opaqueMap .wellFormed _ => True
  | .opaqueMap .value p      => p m = true

instance (m : CaptureMap) : (e : ConstraintEntry) → Decidable (e.wfPart m)
  | .dsl phase c   => by cases phase <;> unfold ConstraintEntry.wfPart <;> infer_instance
  | .opaque phase p => by cases phase <;> unfold ConstraintEntry.wfPart <;> infer_instance
  | .opaqueMap phase p => by cases phase <;> unfold ConstraintEntry.wfPart <;> infer_instance

instance (m : CaptureMap) : (e : ConstraintEntry) → Decidable (e.valPart m)
  | .dsl phase c   => by cases phase <;> unfold ConstraintEntry.valPart <;> infer_instance
  | .opaque phase p => by cases phase <;> unfold ConstraintEntry.valPart <;> infer_instance
  | .opaqueMap phase p => by cases phase <;> unfold ConstraintEntry.valPart <;> infer_instance

/-! ## Surface syntax → `Constraint`

A `constraintExpr` category reusing the `valExpr` category
(from `Triptych.Architecture.Value`) for the arithmetic sides of comparisons. -/

open Lean

declare_syntax_cat constraintExpr
syntax "noLeadingZero " rawIdent         : constraintExpr
-- Cardinality over presence (SAT-style): how many of a SET of captures are present. Braces
-- `{X, Y, …}` signal it is a set (not an argument list). `nonempty X` = sugar `atLeast 1 {X}`.
syntax "nonempty " rawIdent              : constraintExpr
syntax "atLeast " num " {" rawIdent,+ "}" : constraintExpr
syntax "atMost "  num " {" rawIdent,+ "}" : constraintExpr
syntax "exactly " num " {" rawIdent,+ "}" : constraintExpr
syntax rawIdent " = " str                : constraintExpr   -- string equality
syntax valExpr " ≤ " valExpr             : constraintExpr
syntax valExpr " < " valExpr             : constraintExpr
syntax valExpr " == " valExpr            : constraintExpr   -- value equality (`==` to avoid clash)
-- Closed-interval sugar: `e ∈ [lo, hi]` desugars to `lo ≤ e ∧ e ≤ hi` (no new AST node).
-- Matches the doc's `value ∈ [Int64.MIN, Int64.MAX]`. (Sets/half-open intervals are out
-- of scope — use the `opaque` escape for those.)
syntax valExpr " ∈ " "[" valExpr ", " valExpr "]" : constraintExpr
-- NOTE: the ESCAPE HATCH for constraints outside the DSL vocabulary is NOT a `constraintExpr`
-- form — it is the separate `constraints'` section of `triptych`
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

/-- Build a `CaptureMap → α` closure from the author's `f` applied to capture args, where each
    arg is either SCALAR (its matched string, `(m.toEnv "X").getD ""` — same as `opaqueEnvClosure`
    reads) or a LIST (`CaptureMap.toEnvList m "X"`, every substring `X` matched, in order). The
    `isList` flag per arg comes from the surface `[X]` marker. The `value'` escape uses this
    (via `computeValueMap`) so it can consume a `rep`-repeated capture as `List String` — the
    individual repeated elements the scalar `Env` reader collapses. -/
def opaqueMapClosure (f : TSyntax `ident) (is : Array (TSyntax `ident × Bool)) :
    MacroM (TSyntax `term) := do
  -- `mkIdent` (not a literal in the quotation) so these carry NO macro scope — the generated
  -- `def valueFn` elaborates cleanly both in-place and in the written file (which `open Triptych`).
  let toEnvListId := mkIdent `Triptych.CaptureMap.toEnvList
  let toEnvId     := mkIdent `Triptych.CaptureMap.toEnv
  let capMapId    := mkIdent `Triptych.CaptureMap
  let args : Array (TSyntax `term) ← is.mapM (fun (i, isList) =>
    let key := Syntax.mkStrLit i.getId.toString
    if isList then `($toEnvListId m $key)
    else `(($toEnvId m $key).getD ""))
  `(fun m : $capMapId => $f $args*)

/-- Does a `valExpr` reference the final `value` keyword? -/
partial def valExprUsesValue : TSyntax `valExpr → Bool
  | `(valExpr| value) => true
  | `(valExpr| ( $e:valExpr )) => valExprUsesValue e
  | `(valExpr| $a:valExpr + $b:valExpr) => valExprUsesValue a || valExprUsesValue b
  | `(valExpr| $a:valExpr - $b:valExpr) => valExprUsesValue a || valExprUsesValue b
  | `(valExpr| $a:valExpr * $b:valExpr) => valExprUsesValue a || valExprUsesValue b
  | `(valExpr| $a:valExpr ^ $b:valExpr) => valExprUsesValue a || valExprUsesValue b
  | _ => false

/-- Does a constraint reference the format's final `value`? This is the authoritative
    phase classifier and must run before `value` is substituted by its `ValExpr`. -/
def constraintUsesValue : TSyntax `constraintExpr → Bool
  | `(constraintExpr| $a:valExpr ≤ $b:valExpr) => valExprUsesValue a || valExprUsesValue b
  | `(constraintExpr| $a:valExpr < $b:valExpr) => valExprUsesValue a || valExprUsesValue b
  | `(constraintExpr| $a:valExpr == $b:valExpr) => valExprUsesValue a || valExprUsesValue b
  | `(constraintExpr| $e:valExpr ∈ [ $lo:valExpr , $hi:valExpr ]) =>
      valExprUsesValue e || valExprUsesValue lo || valExprUsesValue hi
  | _ => false

/-- Translate a constraint into an entry, preserving whether its original surface syntax
    referenced the final `value` before `valueSub` replaces that reference. -/
def elabEntryWith (valueSub : Option (TSyntax `term)) :
    TSyntax `constraintExpr → MacroM (TSyntax `term)
  | c => do
      let phase ← if constraintUsesValue c then `(ConstraintPhase.value)
        else `(ConstraintPhase.wellFormed)
      `(ConstraintEntry.dsl $phase $(← elabConstraintWith valueSub c))

/-- `elabEntry` with no `value` substitution. -/
def elabEntry (c : TSyntax `constraintExpr) : MacroM (TSyntax `term) :=
  elabEntryWith none c

/-- Translate a `constraintExpr` into a READABLE `Prop` term over environment `env`,
    using the readable value readers (`env.intVal "X" ≤ 255`, etc.) — the surface/pretty
    counterpart of the `Constraint` AST, just as `<Name>.value` is for `ValExpr`. Emitted
    in either `<Name>.WfConstraints` or `<Name>.Constraints` according to the preserved
    phase. `valueSub` substitutes a readable term for a `value` reference. -/
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

/-- Repetition item names referenced through `count X` in a constraint. -/
def constraintCountCaptures : TSyntax `constraintExpr → List String
  | `(constraintExpr| $a:valExpr ≤ $b:valExpr) =>
      (valExprCountCaptures a ++ valExprCountCaptures b).eraseDups
  | `(constraintExpr| $a:valExpr < $b:valExpr) =>
      (valExprCountCaptures a ++ valExprCountCaptures b).eraseDups
  | `(constraintExpr| $a:valExpr == $b:valExpr) =>
      (valExprCountCaptures a ++ valExprCountCaptures b).eraseDups
  | `(constraintExpr| $e:valExpr ∈ [ $lo:valExpr , $hi:valExpr ]) =>
      (valExprCountCaptures e ++ valExprCountCaptures lo ++
        valExprCountCaptures hi).eraseDups
  | _ => []

/-- `cstr% <predicate>` : a `Constraint` value from the constraint-DSL. -/
macro "cstr% " c:constraintExpr : term => elabConstraint c

end Triptych
