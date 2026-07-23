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
def readNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

/-- Reader: signed decimal value (leading `-` ⟹ negative; `"-12" ↦ -12`).
    PRECONDITION: `s` is optionally a leading `-` then a digit run, per the grammar's
    `['-'] Digit⁺`. Note `+` is not accepted (the grammar has no `+` sign), matching the
    doc — unlike stdlib `String.toInt?`. See `readNat` for why we own this reader. -/
def readInt (s : String) : Int :=
  if s.startsWith "-" then -(readNat (s.drop 1).toString : Int) else (readNat s : Int)

/-- Evaluation environment: capture name ↦ its matched substring (absent ⟹ `none`).
    In the full pipeline this comes from `decode`; here it is supplied directly. -/
abbrev Env := String → Option String

/-! ## Readable field readers

These are the per-field-reference cases of `ValExpr.eval`, named to read like the doc's
`int(X)`, `nat(X)`, `|X|`, `sign`. The generated *surface* value function (`<Name>.value`)
is written in terms of these — the readable counterpart of the `ValExpr` AST engine, just
as the inlined `IsWf` is the readable counterpart of the interpreter. `eval` is defined
via them, so the surface value is DEFINITIONALLY `valueExpr.eval` (no equivalence gap).
Absent field ⟹ `0` (`nat`/`int`/`len`) or `+1` (`sign`), matching the doc's "0 if omitted". -/
def Env.natVal  (env : Env) (f : String) : Int := match env f with | some s => (readNat s : Int) | none => 0
def Env.intVal  (env : Env) (f : String) : Int := match env f with | some s => readInt s          | none => 0
def Env.lenVal  (env : Env) (f : String) : Int := match env f with | some s => (s.length : Int)   | none => 0
def Env.signVal (env : Env) (f : String) : Int := match env f with | some s => if s.startsWith "-" then -1 else 1 | none => 1

/-! ### String-level readers (surface API)

The SURFACE value/constraint functions are phrased directly over the captured component
*strings* (matching the doc's `int(Integer)`, `nat(Fraction)`, `|Fraction|`, `sign`),
NOT over an `Env` — so the generated spec never mentions the internal capture map. An
absent optional component is passed as `""`, and each reader maps `""` to the doc's
"0 if omitted" (`natOf "" = 0`, `signOf "" = 1`). -/
def natOf  (s : String) : Int := (readNat s : Int)
def intOf  (s : String) : Int := if s == "" then 0 else readInt s
def lenOf  (s : String) : Int := (s.length : Int)
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
syntax:max "nat " ident    : valExpr
syntax:max "int " ident    : valExpr
syntax:max "len " ident    : valExpr
-- A BARE capture name denotes its SIGN (±1): `Sign` ⟺ the old `sign Sign`. Reserved for
-- productions declared `Sign ::= sign` (a dedicated sign capture); the `"nat "`/`"int "`/`"len "`
-- atoms above are keywords, so a bare ident never collides with them. See `elabTriptych`,
-- which validates that every bare-ident ref names an actual sign capture.
syntax:max ident           : valExpr
-- Named integer constants (desugar to `ValExpr.lit`, staying fully analyzable).
syntax:max "Int64.MAX"     : valExpr
syntax:max "Int64.MIN"     : valExpr
-- `value` — inside a `constraints` entry, refers to the elaborated value expression
-- (so constraints read like the doc's `value(X) ∈ [MIN, MAX]`). Only meaningful when a
-- value substitution is supplied (see `elabValExprWith`); bare use elsewhere errors.
syntax:max "value"         : valExpr
syntax:max "(" valExpr ")" : valExpr
syntax:65 valExpr:65 " + " valExpr:66 : valExpr
syntax:65 valExpr:65 " - " valExpr:66 : valExpr
syntax:70 valExpr:70 " * " valExpr:71 : valExpr
syntax:75 valExpr:76 " ^ " valExpr:75 : valExpr

/-- Translate a `valExpr` formula into a `ValExpr` term. `valueSub`, if provided, is the
    term substituted for a `value` reference (the format's value expression); `none`
    makes a `value` reference an error. -/
partial def elabValExprWith (valueSub : Option (TSyntax `term)) :
    TSyntax `valExpr → MacroM (TSyntax `term)
  | `(valExpr| $n:num)      => `(ValExpr.lit $n)
  | `(valExpr| Int64.MAX)   => `(ValExpr.lit 9223372036854775807)
  | `(valExpr| Int64.MIN)   => `(ValExpr.lit (-9223372036854775808))
  | `(valExpr| value)       =>
      match valueSub with
      | some t => pure t
      | none   => Macro.throwUnsupported
  | `(valExpr| nat $i:ident)  => `(ValExpr.nat $(quote i.getId.toString))
  | `(valExpr| int $i:ident)  => `(ValExpr.int $(quote i.getId.toString))
  | `(valExpr| len $i:ident)  => `(ValExpr.len $(quote i.getId.toString))
  | `(valExpr| $i:ident)      => `(ValExpr.signOf $(quote i.getId.toString))
  | `(valExpr| ( $e:valExpr )) => elabValExprWith valueSub e
  | `(valExpr| $a:valExpr + $b:valExpr) => do `(ValExpr.add $(← elabValExprWith valueSub a) $(← elabValExprWith valueSub b))
  | `(valExpr| $a:valExpr - $b:valExpr) => do `(ValExpr.sub $(← elabValExprWith valueSub a) $(← elabValExprWith valueSub b))
  | `(valExpr| $a:valExpr * $b:valExpr) => do `(ValExpr.mul $(← elabValExprWith valueSub a) $(← elabValExprWith valueSub b))
  | `(valExpr| $a:valExpr ^ $b:valExpr) => do `(ValExpr.pow $(← elabValExprWith valueSub a) $(← elabValExprWith valueSub b))
  | _ => Macro.throwUnsupported

/-- Translate a `valExpr` with no `value` substitution (the common case). -/
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
  String.intercalate "_" ((capture.splitOn ".").map seg)

/-- Translate a `valExpr` into a READABLE `Int` term over the captured component STRINGS
    (via `natOf`/`intOf`/`lenOf`/`signOf` applied to lowercase-named binders), NOT over an
    `Env`. This is the surface/pretty counterpart of the `ValExpr` AST — the generated
    `<Name>.value` takes the components as string parameters and reads like the doc's
    `int(Integer)·10⁴ + …`. `valueSub` substitutes a readable term for a `value`
    reference (used in constraints). -/
partial def elabValReadableWith (valueSub : Option (TSyntax `term)) :
    TSyntax `valExpr → MacroM (TSyntax `term)
  | `(valExpr| $n:num)        => `(($n : Int))
  | `(valExpr| Int64.MAX)     => `((9223372036854775807 : Int))
  | `(valExpr| Int64.MIN)     => `((-9223372036854775808 : Int))
  | `(valExpr| value)         =>
      match valueSub with
      | some t => pure t
      | none   => Macro.throwUnsupported
  | `(valExpr| nat $i:ident)  => let b := mkIdent (Name.mkSimple (surfaceBinder i.getId.toString)); `(natOf $b)
  | `(valExpr| int $i:ident)  => let b := mkIdent (Name.mkSimple (surfaceBinder i.getId.toString)); `(intOf $b)
  | `(valExpr| len $i:ident)  => let b := mkIdent (Name.mkSimple (surfaceBinder i.getId.toString)); `(lenOf $b)
  | `(valExpr| $i:ident)      => let b := mkIdent (Name.mkSimple (surfaceBinder i.getId.toString)); `(signOf $b)
  | `(valExpr| ( $e:valExpr )) => do `(($(← elabValReadableWith valueSub e)))
  | `(valExpr| $a:valExpr + $b:valExpr) => do `($(← elabValReadableWith valueSub a) + $(← elabValReadableWith valueSub b))
  | `(valExpr| $a:valExpr - $b:valExpr) => do `($(← elabValReadableWith valueSub a) - $(← elabValReadableWith valueSub b))
  | `(valExpr| $a:valExpr * $b:valExpr) => do `($(← elabValReadableWith valueSub a) * $(← elabValReadableWith valueSub b))
  | `(valExpr| $a:valExpr ^ $b:valExpr) => do `($(← elabValReadableWith valueSub a) ^ ($(← elabValReadableWith valueSub b)).toNat)
  | _ => Macro.throwUnsupported

/-- The distinct capture names referenced (as `nat`/`int`/`len`/`sign`) in a `valExpr`,
    in first-appearance order — the surface value function's string parameters. -/
partial def valExprCaptures : TSyntax `valExpr → List String
  | `(valExpr| nat $i:ident)  => [i.getId.toString]
  | `(valExpr| int $i:ident)  => [i.getId.toString]
  | `(valExpr| len $i:ident)  => [i.getId.toString]
  | `(valExpr| $i:ident)      => [i.getId.toString]
  | `(valExpr| ( $e:valExpr )) => valExprCaptures e
  | `(valExpr| $a:valExpr + $b:valExpr) => (valExprCaptures a ++ valExprCaptures b).eraseDups
  | `(valExpr| $a:valExpr - $b:valExpr) => (valExprCaptures a ++ valExprCaptures b).eraseDups
  | `(valExpr| $a:valExpr * $b:valExpr) => (valExprCaptures a ++ valExprCaptures b).eraseDups
  | `(valExpr| $a:valExpr ^ $b:valExpr) => (valExprCaptures a ++ valExprCaptures b).eraseDups
  | _ => []

/-- The capture names referenced BARE (i.e. as a sign, `ValExpr.signOf`) in a `valExpr` — the
    subset of `valExprCaptures` that must name dedicated SIGN productions (`X ::= sign`). Kept
    separate so `elabTriptych` can validate each bare ref actually is a sign capture (else the
    old silent-`+1` trap returns). -/
partial def valExprSignCaptures : TSyntax `valExpr → List String
  | `(valExpr| nat $_:ident)  => []
  | `(valExpr| int $_:ident)  => []
  | `(valExpr| len $_:ident)  => []
  | `(valExpr| $i:ident)      => [i.getId.toString]
  | `(valExpr| ( $e:valExpr )) => valExprSignCaptures e
  | `(valExpr| $a:valExpr + $b:valExpr) => (valExprSignCaptures a ++ valExprSignCaptures b).eraseDups
  | `(valExpr| $a:valExpr - $b:valExpr) => (valExprSignCaptures a ++ valExprSignCaptures b).eraseDups
  | `(valExpr| $a:valExpr * $b:valExpr) => (valExprSignCaptures a ++ valExprSignCaptures b).eraseDups
  | `(valExpr| $a:valExpr ^ $b:valExpr) => (valExprSignCaptures a ++ valExprSignCaptures b).eraseDups
  | _ => []

end Triptych
