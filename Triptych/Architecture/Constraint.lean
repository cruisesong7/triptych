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

* classify each constraint while parsing by whether its surface syntax explicitly
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

/-- A parsed constraint together with its source-determined acceptance phase. -/
structure ParsedConstraint where
  phase : ConstraintPhase
  constraint : Constraint
  deriving Inhabited

private def phaseFor (usesValue : Bool) : ConstraintPhase :=
  if usesValue then .value else .wellFormed

/-- Parse a constraint once, retaining whether its source explicitly constrained `value`. -/
def parseConstraintEntryWith (valueSub : Option ValExpr) :
    TSyntax `constraintExpr → MacroM ParsedConstraint
  | `(constraintExpr| noLeadingZero $i:ident) =>
      pure ⟨.wellFormed, .noLeadingZero i.getId.toString⟩
  | `(constraintExpr| nonempty $i:ident) =>
      pure ⟨.wellFormed, .card .atLeast 1 [i.getId.toString]⟩
  | `(constraintExpr| atLeast $k:num { $is,* }) =>
      pure ⟨.wellFormed,
        .card .atLeast k.getNat (is.getElems.map (·.getId.toString)).toList⟩
  | `(constraintExpr| atMost $k:num { $is,* }) =>
      pure ⟨.wellFormed,
        .card .atMost k.getNat (is.getElems.map (·.getId.toString)).toList⟩
  | `(constraintExpr| exactly $k:num { $is,* }) =>
      pure ⟨.wellFormed,
        .card .exactlyK k.getNat (is.getElems.map (·.getId.toString)).toList⟩
  | `(constraintExpr| $i:ident = $l:str) =>
      pure ⟨.wellFormed, .strEq i.getId.toString l.getString⟩
  | `(constraintExpr| $a:valExpr ≤ $b:valExpr) => do
      let a ← parseValExprWithUsage valueSub a
      let b ← parseValExprWithUsage valueSub b
      return ⟨phaseFor (a.usesValue || b.usesValue), .le a.expression b.expression⟩
  | `(constraintExpr| $a:valExpr < $b:valExpr) => do
      let a ← parseValExprWithUsage valueSub a
      let b ← parseValExprWithUsage valueSub b
      return ⟨phaseFor (a.usesValue || b.usesValue), .lt a.expression b.expression⟩
  | `(constraintExpr| $a:valExpr == $b:valExpr) => do
      let a ← parseValExprWithUsage valueSub a
      let b ← parseValExprWithUsage valueSub b
      return ⟨phaseFor (a.usesValue || b.usesValue), .eq a.expression b.expression⟩
  | `(constraintExpr| $e:valExpr ∈ [ $lo:valExpr , $hi:valExpr ]) => do
      let expression ← parseValExprWithUsage valueSub e
      let lower ← parseValExprWithUsage valueSub lo
      let upper ← parseValExprWithUsage valueSub hi
      let usesValue := expression.usesValue || lower.usesValue || upper.usesValue
      return ⟨phaseFor usesValue,
        .and (.le lower.expression expression.expression)
          (.le expression.expression upper.expression)⟩
  | _ => Macro.throwUnsupported

/-- Parse a constraint and return its semantic AST. -/
def parseConstraintWith (valueSub : Option ValExpr) (c : TSyntax `constraintExpr) :
    MacroM Constraint :=
  return (← parseConstraintEntryWith valueSub c).constraint

/-- Parse a constraint expression with no `value` substitution. -/
def parseConstraint (c : TSyntax `constraintExpr) : MacroM Constraint :=
  parseConstraintWith none c

private def quoteCardOp : CardOp → MacroM (TSyntax `term)
  | .atLeast => `(CardOp.atLeast)
  | .atMost => `(CardOp.atMost)
  | .exactlyK => `(CardOp.exactlyK)

private def quoteConstraintPhase : ConstraintPhase → MacroM (TSyntax `term)
  | .wellFormed => `(ConstraintPhase.wellFormed)
  | .value => `(ConstraintPhase.value)

private def quoteStringList (fields : List String) : MacroM (TSyntax `term) := do
  let terms : Syntax.TSepArray `term "," :=
    .ofElems <| fields.toArray.map fun field => ⟨Syntax.mkStrLit field⟩
  `([$terms,*])

/-- Reify a parsed constraint as a Lean term, optionally preserving the generated `valueExpr`
    name for subexpressions equal to the format's value AST. -/
partial def quoteConstraintWith
    (valueRef : Option (ValExpr × TSyntax `term)) : Constraint → MacroM (TSyntax `term)
  | .noLeadingZero field => `(Constraint.noLeadingZero $(quote field))
  | .strEq field literal => `(Constraint.strEq $(quote field) $(quote literal))
  | .card op k fields => do
      `(Constraint.card $(← quoteCardOp op) $(quote k) $(← quoteStringList fields))
  | .le a b => do
      `(Constraint.le $(← quoteValExprWith valueRef a) $(← quoteValExprWith valueRef b))
  | .lt a b => do
      `(Constraint.lt $(← quoteValExprWith valueRef a) $(← quoteValExprWith valueRef b))
  | .eq a b => do
      `(Constraint.eq $(← quoteValExprWith valueRef a) $(← quoteValExprWith valueRef b))
  | .and a b => do
      `(Constraint.and $(← quoteConstraintWith valueRef a) $(← quoteConstraintWith valueRef b))

/-- Reify a parsed constraint with no named value substitution. -/
partial def quoteConstraint (constraint : Constraint) : MacroM (TSyntax `term) :=
  quoteConstraintWith none constraint

/-- Reify a parsed, phased constraint as a generated `ConstraintEntry`. -/
def quoteConstraintEntryWith (valueRef : Option (ValExpr × TSyntax `term))
    (entry : ParsedConstraint) : MacroM (TSyntax `term) := do
  let valueRef := if entry.phase == .value then valueRef else none
  `(ConstraintEntry.dsl $(← quoteConstraintPhase entry.phase)
      $(← quoteConstraintWith valueRef entry.constraint))

/-- Reify a parsed constraint entry with no named value substitution. -/
def quoteConstraintEntry (entry : ParsedConstraint) : MacroM (TSyntax `term) :=
  quoteConstraintEntryWith none entry

/-- Parse once and reify the resulting constraint AST as Lean syntax. -/
def elabConstraintWith (valueSub : Option ValExpr) (c : TSyntax `constraintExpr) :
    MacroM (TSyntax `term) := do
  quoteConstraint (← parseConstraintWith valueSub c)

/-- Translate a constraint with no `value` substitution. -/
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

/-- Parse a constraint once and reify its AST and source-determined phase. -/
def elabEntryWith (valueSub : Option ValExpr) (c : TSyntax `constraintExpr) :
    MacroM (TSyntax `term) := do
  quoteConstraintEntry (← parseConstraintEntryWith valueSub c)

/-- `elabEntry` with no `value` substitution. -/
def elabEntry (c : TSyntax `constraintExpr) : MacroM (TSyntax `term) :=
  elabEntryWith none c

/-- Render a parsed constraint as the readable Lean predicate over component-string binders. -/
partial def quoteConstraintReadable
    (valueRef : Option (ValExpr × TSyntax `term)) : Constraint → MacroM (TSyntax `term)
  | .noLeadingZero field =>
      let binder := mkIdent (Name.mkSimple (surfaceBinder field))
      `(($binder).startsWith "0" → $binder = "0")
  | .strEq field literal =>
      let binder := mkIdent (Name.mkSimple (surfaceBinder field))
      `($binder = $(quote literal))
  | .card .atLeast 1 [field] =>
      let binder := mkIdent (Name.mkSimple (surfaceBinder field))
      `($binder ≠ "")
  | .card op k fields => do
      let terms : Syntax.TSepArray `term "," := .ofElems <| fields.toArray.map fun field =>
        ⟨(mkIdent (Name.mkSimple (surfaceBinder field))).raw⟩
      match op with
      | .atLeast => `(presentCount [$terms,*] ≥ $(quote k))
      | .atMost => `(presentCount [$terms,*] ≤ $(quote k))
      | .exactlyK => `(presentCount [$terms,*] = $(quote k))
  | .le a b => do
      `($(← quoteValReadableWith valueRef a) ≤ $(← quoteValReadableWith valueRef b))
  | .lt a b => do
      `($(← quoteValReadableWith valueRef a) < $(← quoteValReadableWith valueRef b))
  | .eq a b => do
      `($(← quoteValReadableWith valueRef a) = $(← quoteValReadableWith valueRef b))
  | .and a b => do
      `($(← quoteConstraintReadable valueRef a) ∧ $(← quoteConstraintReadable valueRef b))

/-- Compatibility wrapper: parse once, then render the resulting constraint AST readably. -/
def elabConstraintReadable (valueSub : Option (ValExpr × TSyntax `term))
    (c : TSyntax `constraintExpr) : MacroM (TSyntax `term) := do
  let parsed ← parseConstraintWith (valueSub.map (·.1)) c
  quoteConstraintReadable valueSub parsed

/-- Capture names referenced by a parsed constraint. -/
partial def Constraint.captures : Constraint → List String
  | .noLeadingZero field
  | .strEq field _ => [field]
  | .card _ _ fields => fields.eraseDups
  | .le a b
  | .lt a b
  | .eq a b => (a.captures ++ b.captures).eraseDups
  | .and a b => (a.captures ++ b.captures).eraseDups

/-- Repetition item names referenced through `count` by a parsed constraint. -/
partial def Constraint.countCaptures : Constraint → List String
  | .le a b
  | .lt a b
  | .eq a b => (a.countCaptures ++ b.countCaptures).eraseDups
  | .and a b => (a.countCaptures ++ b.countCaptures).eraseDups
  | _ => []

/-- `cstr% <predicate>` : a `Constraint` value from the constraint-DSL. -/
macro "cstr% " c:constraintExpr : term => elabConstraint c

end Triptych
