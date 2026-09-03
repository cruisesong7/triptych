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

import Lean

/-!
# The value-DSL: a deep-embedded value expression language

The `value` section of `triptych` is written in a small, readable, math-style
formula language transcribing the doc's `value(X) = …` notation. Crucially this is a
**deep embedding**: the DSL elaborates into an inspectable `ValExpr` AST, NOT directly
into an opaque Lean term.

Why deep (design note §16.4, and the CoStar++ contrast): CoStar++ consumes the value
function as a black box (`f vs`), which is why its value is stuck at *definitional*.
Owning the AST lets us (a) *translate* it to a Lean computation via the `eval`
denotation, and later (b) *analyze* it for affinity to auto-generate roundtrip /
soundness proofs. `eval e` IS the value function (a total Lean function), so the
"translation into Lean" is just the denotation.

Scope of this first increment: scalar `Int`-valued formulas (covers decimal, duration).
Deferred: structured / non-`Int` output (IPAddr's `IPNet`), non-recursive `where`
helpers (datetime's `isLeapYear`/`daysInMonth`), and the affinity analysis pass.
-/

namespace Triptych

/-- Deep-embedded value-expression AST. Field references (`nat`/`int`/`len`/`sign`)
    read a named capture from the environment; the rest is closed-form arithmetic. -/
inductive ValExpr where
  /-- Integer literal. -/
  | lit    (n : Int)
  /-- `nat X` — unsigned decimal value of capture `X` (0 if absent). -/
  | nat    (field : String)
  /-- `int X` — signed decimal value of capture `X` (leading `-` ⟹ negative; 0 if absent). -/
  | int    (field : String)
  /-- `len X` — character length of capture `X` (0 if absent). -/
  | len    (field : String)
  /-- `count X` — number of elements matched by a `rep X ...` (0 if absent). The decoder
      records this under the derived capture key `X#count`. -/
  | count  (field : String)
  /-- `sign X` — `-1` if capture `X` starts with `-`, else `+1` (used for the doc's
      `sign` helper; `+1` if absent). -/
  | signOf (field : String)
  | add    (a b : ValExpr)
  | sub    (a b : ValExpr)
  | mul    (a b : ValExpr)
  /-- `base ^ exp` — exponent is evaluated then truncated to `Nat` (always ≥ 0 here). -/
  | pow    (base exp : ValExpr)
  | neg    (a : ValExpr)
  deriving Repr, Inhabited, DecidableEq

/-- Reader: unsigned decimal value of a digit string (`"345" ↦ 345`).

    PRECONDITION: `s` is a run of ASCII digits `'0'..'9'` — guaranteed at every real call
    site by the grammar's `TokClass.digit`/`IsWf` (via `decode`). On a non-digit char the
    `Nat` truncated subtraction yields an unspecified (but total, non-crashing) value;
    *well-formedness*, not this reader, rejects non-digit inputs. The fold is left
    unguarded deliberately: the `else` branch would be dead code on valid input and would
    only add an `if` to discharge in the affinity/roundtrip proofs (the happy path).

    Why a Cedar-local reader, NOT stdlib `String.toNat?`/`toNat!`: the reader is part of
    the *spec's meaning*, so it must be pinned by us — (1) stdlib's contract can drift
    across Lean versions (cf. this repo's `toNat?'` and the datetime workaround), and
    (2) stdlib is more permissive than our grammar (accepts leading zeros, possibly
    Unicode digits), which would let the value function diverge from `IsWf`. Owning the
    reader keeps its digit-rule identical to `TokClass.digit` and version-stable. -/
def readNatChars (characters : List Char) : Nat :=
  characters.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def readNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

@[simp]
theorem readNat_empty : readNat "" = 0 := by
  simp [readNat]

theorem readNat_eq_readNatChars (s : String) : readNat s = readNatChars s.toList := by
  unfold readNat readNatChars
  rw [String.foldl_eq_foldl_toList]

/-- Reader: signed decimal value (leading `-` ⟹ negative; `"-12" ↦ -12`).
    PRECONDITION: `s` is optionally a leading `-` then a digit run, per the grammar's
    `['-'] Digit⁺`. Note `+` is not accepted (the grammar has no `+` sign), matching the
    doc — unlike stdlib `String.toInt?`. See `readNat` for why we own this reader. -/
def readInt (s : String) : Int :=
  if s.startsWith "-" then -(readNat (s.drop 1).toString : Int) else (readNat s : Int)

/-- Evaluation environment: capture name ↦ its matched substring (absent ⟹ `none`).
    In the full pipeline this comes from `decode`; here it is supplied directly. -/
abbrev Env := String → Option String

/-- A complete capture assignment: nonterminal name ↦ matched substring. Unlike `Env`, this
    representation preserves every occurrence of a repeated capture. It lives with the value
    readers rather than the decoder so both values and constraints can consume collections
    without introducing an architecture import cycle. -/
abbrev CaptureMap := List (String × String)

/-- Collapse a `CaptureMap` to its legacy scalar view, keeping the first span for each name. -/
def CaptureMap.toEnv (m : CaptureMap) : Env :=
  fun k => (m.find? (·.1 == k)).map (·.2)

/-- Read every span recorded under `k`, in match order. -/
def CaptureMap.toEnvList (m : CaptureMap) (k : String) : List String :=
  (m.filter (·.1 == k)).map (·.2)

/-! ## Readable field readers

These are the per-field-reference cases of `ValExpr.eval`, named to read like the doc's
`int(X)`, `nat(X)`, `|X|`, `sign`. The generated *surface* value function (`<Name>.value`)
is written in terms of these — the readable counterpart of the `ValExpr` AST engine, just
as the inlined `IsWf` is the readable counterpart of the interpreter. `eval` is defined
via them, so the surface value is DEFINITIONALLY `valueExpr.eval` (no equivalence gap).
Absent field gives `0` (`nat`/`int`/`len`/`count`) or `+1` (`sign`), matching the doc's
"0 if omitted". -/
def Env.natVal  (env : Env) (f : String) : Int := match env f with | some s => (readNat s : Int) | none => 0
def Env.intVal  (env : Env) (f : String) : Int := match env f with | some s => readInt s          | none => 0
def Env.lenVal  (env : Env) (f : String) : Int := match env f with | some s => (s.length : Int)   | none => 0
def Env.countVal (env : Env) (f : String) : Int := env.natVal (f ++ "#count")
def Env.signVal (env : Env) (f : String) : Int := match env f with | some s => if s.startsWith "-" then -1 else 1 | none => 1

/-! ### String-level readers (surface API)

The SURFACE value/constraint functions are phrased directly over the captured component
*strings* (matching the doc's `int(Integer)`, `nat(Fraction)`, `|Fraction|`, `sign`),
NOT over an `Env` — so the generated spec never mentions the internal capture map. An
absent optional component is passed as `""`, and each reader maps `""` to the doc's
"0 if omitted" (`natOf "" = 0`, `countOf "" = 0`, `signOf "" = 1`). -/
def natOf  (s : String) : Int := (readNat s : Int)
def intOf  (s : String) : Int := if s == "" then 0 else readInt s
def lenOf  (s : String) : Int := (s.length : Int)
def countOf (s : String) : Int := (readNat s : Int)
def signOf (s : String) : Int := if s.startsWith "-" then -1 else 1

/-- Count how many of the captured component strings are *present* (nonempty). The base of
    the cardinality constraints (`atLeast`/`atMost`/`exactlyK` over a set of optional
    captures), matching the SAT-community "≥ k of these hold" over the presence booleans:
    each capture contributes 1 iff its matched string is nonempty (absent optional ⟹ `""` ⟹
    0). `presentCount ["1d", "", "3m"] = 2`. -/
def presentCount (ss : List String) : Nat :=
  ss.foldl (fun acc s => if s == "" then acc else acc + 1) 0

/-- Denotation of a value expression against a capture environment — this IS the
    translation to a Lean computation, defined via the readable field readers above. -/
def ValExpr.eval (env : Env) : ValExpr → Int
  | .lit n    => n
  | .nat f    => env.natVal f
  | .int f    => env.intVal f
  | .len f    => env.lenVal f
  | .count f  => env.countVal f
  | .signOf f => env.signVal f
  | .add a b  => a.eval env + b.eval env
  | .sub a b  => a.eval env - b.eval env
  | .mul a b  => a.eval env * b.eval env
  | .pow b e  => (b.eval env) ^ (e.eval env).toNat
  | .neg a    => -(a.eval env)

/-! ## Surface syntax: math-style formulas → `ValExpr`

A dedicated syntax category `valExpr` with its own operator precedences
(`^` > `*` > `+`/`-`), so the DSL owns the parse and builds a `ValExpr` term. The
`val%` wrapper turns a formula into a `ValExpr` value. -/

open Lean

declare_syntax_cat valExpr

syntax:max num             : valExpr
syntax:max "nat " rawIdent    : valExpr
syntax:max "int " rawIdent    : valExpr
syntax:max "len " rawIdent    : valExpr
syntax:max "count " rawIdent  : valExpr
-- A BARE capture name denotes its SIGN (±1): `Sign` ⟺ the old `sign Sign`. Reserved for
-- productions declared `Sign ::= sign` (a dedicated sign capture); the `"nat "`/`"int "`/`"len "`
-- atoms above are keywords, so a bare ident never collides with them. See `elabTriptych`,
-- which validates that every bare-ident ref names an actual sign capture.
syntax:max rawIdent        : valExpr
-- Named integer constants (desugar to `ValExpr.lit`, staying fully analyzable).
syntax:max "Int64.MAX"     : valExpr
syntax:max "Int64.MIN"     : valExpr
-- `value` — inside a `constraints` entry, refers to the elaborated value expression
-- (so constraints read like the doc's `value(X) ∈ [MIN, MAX]`). Only meaningful when a
-- value substitution is supplied (see `parseValExprWithUsage`); bare use elsewhere errors.
syntax:max "value"         : valExpr
syntax:max "(" valExpr ")" : valExpr
syntax:65 valExpr:65 " + " valExpr:66 : valExpr
syntax:65 valExpr:65 " - " valExpr:66 : valExpr
syntax:70 valExpr:70 " * " valExpr:71 : valExpr
syntax:75 valExpr:76 " ^ " valExpr:75 : valExpr

/-- A parsed value expression together with the source-level fact that it mentioned the final
    `value` keyword. Constraint phase classification must preserve this fact before substitution
    replaces `value` with the format's `ValExpr`. -/
structure ParsedValExpr where
  expression : ValExpr
  usesValue : Bool
  deriving Inhabited

/-- Parse a value-DSL expression once, preserving whether its source used `value`. -/
partial def parseValExprWithUsage (valueSub : Option ValExpr) :
    TSyntax `valExpr → MacroM ParsedValExpr
  | `(valExpr| $n:num) => pure ⟨.lit (Int.ofNat n.getNat), false⟩
  | `(valExpr| Int64.MAX) => pure ⟨.lit 9223372036854775807, false⟩
  | `(valExpr| Int64.MIN) => pure ⟨.lit (-9223372036854775808), false⟩
  | `(valExpr| value) =>
      match valueSub with
      | some expression => pure ⟨expression, true⟩
      | none => Macro.throwUnsupported
  | `(valExpr| nat $i:ident) => pure ⟨.nat i.getId.toString, false⟩
  | `(valExpr| int $i:ident) => pure ⟨.int i.getId.toString, false⟩
  | `(valExpr| len $i:ident) => pure ⟨.len i.getId.toString, false⟩
  | `(valExpr| count $i:ident) => pure ⟨.count i.getId.toString, false⟩
  | `(valExpr| $i:ident) => pure ⟨.signOf i.getId.toString, false⟩
  | `(valExpr| ( $e:valExpr )) => parseValExprWithUsage valueSub e
  | `(valExpr| $a:valExpr + $b:valExpr) => do
      let a ← parseValExprWithUsage valueSub a
      let b ← parseValExprWithUsage valueSub b
      return ⟨.add a.expression b.expression, a.usesValue || b.usesValue⟩
  | `(valExpr| $a:valExpr - $b:valExpr) => do
      let a ← parseValExprWithUsage valueSub a
      let b ← parseValExprWithUsage valueSub b
      return ⟨.sub a.expression b.expression, a.usesValue || b.usesValue⟩
  | `(valExpr| $a:valExpr * $b:valExpr) => do
      let a ← parseValExprWithUsage valueSub a
      let b ← parseValExprWithUsage valueSub b
      return ⟨.mul a.expression b.expression, a.usesValue || b.usesValue⟩
  | `(valExpr| $a:valExpr ^ $b:valExpr) => do
      let a ← parseValExprWithUsage valueSub a
      let b ← parseValExprWithUsage valueSub b
      return ⟨.pow a.expression b.expression, a.usesValue || b.usesValue⟩
  | _ => Macro.throwUnsupported

/-- Parse a value expression and return its semantic AST. -/
partial def parseValExprWith (valueSub : Option ValExpr) (e : TSyntax `valExpr) :
    MacroM ValExpr :=
  return (← parseValExprWithUsage valueSub e).expression

/-- Parse a value expression with no `value` substitution. -/
partial def parseValExpr (e : TSyntax `valExpr) : MacroM ValExpr :=
  parseValExprWith none e

private def quoteIntLiteral : Int → MacroM (TSyntax `term)
  | .ofNat n =>
      pure ⟨Syntax.mkNumLit (toString n)⟩
  | .negSucc n =>
      let magnitude : TSyntax `term := ⟨Syntax.mkNumLit (toString (n + 1))⟩
      `(-$magnitude)

/-- Reify a parsed `ValExpr` as Lean syntax. `valueRef` preserves the generated `valueExpr`
    declaration inside semantic constraints instead of expanding an equal AST inline. -/
partial def quoteValExprWith
    (valueRef : Option (ValExpr × TSyntax `term)) (expression : ValExpr) :
    MacroM (TSyntax `term) := do
  if let some (valueExpression, reference) := valueRef then
    if expression = valueExpression then
      return reference
  match expression with
  | .lit n => `(ValExpr.lit $(← quoteIntLiteral n))
  | .nat field => `(ValExpr.nat $(quote field))
  | .int field => `(ValExpr.int $(quote field))
  | .len field => `(ValExpr.len $(quote field))
  | .count field => `(ValExpr.count $(quote field))
  | .signOf field => `(ValExpr.signOf $(quote field))
  | .add a b =>
      `(ValExpr.add $(← quoteValExprWith valueRef a) $(← quoteValExprWith valueRef b))
  | .sub a b =>
      `(ValExpr.sub $(← quoteValExprWith valueRef a) $(← quoteValExprWith valueRef b))
  | .mul a b =>
      `(ValExpr.mul $(← quoteValExprWith valueRef a) $(← quoteValExprWith valueRef b))
  | .pow a b =>
      `(ValExpr.pow $(← quoteValExprWith valueRef a) $(← quoteValExprWith valueRef b))
  | .neg a => `(ValExpr.neg $(← quoteValExprWith valueRef a))

/-- Reify a parsed `ValExpr` with no named substitution. -/
partial def quoteValExpr (expression : ValExpr) : MacroM (TSyntax `term) :=
  quoteValExprWith none expression

/-- Parse a value expression and reify that same AST as Lean syntax. -/
partial def elabValExprWith (valueSub : Option ValExpr) (e : TSyntax `valExpr) :
    MacroM (TSyntax `term) := do
  quoteValExpr (← parseValExprWith valueSub e)

/-- Translate a `valExpr` with no `value` substitution. -/
partial def elabValExpr (e : TSyntax `valExpr) : MacroM (TSyntax `term) :=
  elabValExprWith none e

/-- `val% <formula>` : a `ValExpr` value from math-style syntax. -/
macro "val% " e:valExpr : term => elabValExpr e

/-- De-capitalize a capture name into its surface parameter binder, so the readable
    value/constraints refer to components by lowercase name. Two cases, so both all-caps
    acronyms and CamelCase read well:
    * an ALL-UPPERCASE name (an acronym like `YYYY`, `MM`, `SSS`) → fully lowercased
      (`YYYY` → `yyyy`), avoiding the ugly `yYYY`;
    * otherwise only the first character (`Integer` → `integer`, `DDays` → `dDays`),
      preserving internal capitals of CamelCase names.
    A QUALIFIED capture (`Time.hh`, from a nonterminal reused in several parents) has its
    `.` replaced by `_` per segment so the binder is one valid identifier (`Time.hh` →
    `time_hh`). Note: `MM` → `mm` can coincide with a sibling `mm` capture's binder if both
    are referenced *bare* in one function; the datetime grammar avoids this by referencing
    the reused `mm` only qualified (`Time.mm`/`Offset.mm`). -/
def surfaceBinder (capture : String) : String :=
  -- de-capitalize one dot-free segment: fully lower if all-uppercase, else first char only
  let seg (s : String) : String :=
    match s.toList with
    | []      => s
    | c :: cs =>
      if (c :: cs).all (fun ch => !ch.isLower) then s.toLower   -- all-uppercase acronym
      else String.ofList (c.toLower :: cs)                       -- CamelCase: first char only
  String.intercalate "_" (((capture.replace "#" ".").splitOn ".").map seg)

/-- Render a parsed `ValExpr` as the readable Lean surface over component-string binders.
    `valueRef` lets a constraint retain the concise `<Name>.value ...` presentation after its
    source-level `value` reference has been substituted by the format's AST. -/
partial def quoteValReadableWith
    (valueRef : Option (ValExpr × TSyntax `term)) (expression : ValExpr) :
    MacroM (TSyntax `term) := do
  if let some (valueExpression, readable) := valueRef then
    if expression = valueExpression then
      return readable
  match expression with
  | .lit n => do
      let literal ← quoteIntLiteral n
      `(($literal : Int))
  | .nat field =>
      let binder := mkIdent (Name.mkSimple (surfaceBinder field))
      `(natOf $binder)
  | .int field =>
      let binder := mkIdent (Name.mkSimple (surfaceBinder field))
      `(intOf $binder)
  | .len field =>
      let binder := mkIdent (Name.mkSimple (surfaceBinder field))
      `(lenOf $binder)
  | .count field =>
      let binder := mkIdent (Name.mkSimple (surfaceBinder (field ++ "#count")))
      `(countOf $binder)
  | .signOf field =>
      let binder := mkIdent (Name.mkSimple (surfaceBinder field))
      `(signOf $binder)
  | .add a b =>
      `($(← quoteValReadableWith valueRef a) + $(← quoteValReadableWith valueRef b))
  | .sub a b =>
      `($(← quoteValReadableWith valueRef a) - $(← quoteValReadableWith valueRef b))
  | .mul a b => do
      let aTerm ← quoteValReadableWith valueRef a
      let bTerm ← quoteValReadableWith valueRef b
      let aTerm ← match a with
        | .add _ _ | .sub _ _ => `(($aTerm))
        | _ => pure aTerm
      let bTerm ← match b with
        | .add _ _ | .sub _ _ => `(($bTerm))
        | _ => pure bTerm
      `($aTerm * $bTerm)
  | .pow a b => do
      let base ← quoteValReadableWith valueRef a
      let exponent ← quoteValReadableWith valueRef b
      let exponent ← match b with
        | .lit _ | .nat _ | .int _ | .len _ | .count _ | .signOf _ => pure exponent
        | _ => `(($exponent))
      `($base ^ ($exponent).toNat)
  | .neg a => `(-$(← quoteValReadableWith valueRef a))

/-- Render a parsed value AST as the readable Lean surface. -/
partial def quoteValReadable (expression : ValExpr) : MacroM (TSyntax `term) :=
  quoteValReadableWith none expression

/-- Compatibility wrapper: parse once, then render the resulting AST readably. -/
partial def elabValReadableWith (valueSub : Option (ValExpr × TSyntax `term))
    (expression : TSyntax `valExpr) : MacroM (TSyntax `term) := do
  let ast ← parseValExprWith (valueSub.map (·.1)) expression
  quoteValReadableWith valueSub ast

/-- Captures read by a parsed value expression, in first-appearance order. -/
partial def ValExpr.captures : ValExpr → List String
  | .lit _ => []
  | .nat field
  | .int field
  | .len field
  | .signOf field => [field]
  | .count field => [field ++ "#count"]
  | .add a b
  | .sub a b
  | .mul a b
  | .pow a b => (a.captures ++ b.captures).eraseDups
  | .neg a => a.captures

/-- Captures used as bare sign readers by a parsed value expression. -/
partial def ValExpr.signCaptures : ValExpr → List String
  | .signOf field => [field]
  | .add a b
  | .sub a b
  | .mul a b
  | .pow a b => (a.signCaptures ++ b.signCaptures).eraseDups
  | .neg a => a.signCaptures
  | _ => []

/-- Repetition item names read through `count` by a parsed value expression. -/
partial def ValExpr.countCaptures : ValExpr → List String
  | .count field => [field]
  | .add a b
  | .sub a b
  | .mul a b
  | .pow a b => (a.countCaptures ++ b.countCaptures).eraseDups
  | .neg a => a.countCaptures
  | _ => []

end Triptych
