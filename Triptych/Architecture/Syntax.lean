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
import Triptych.Architecture.Grammar
import Triptych.Architecture.Classify
import Triptych.Architecture.Value
import Triptych.Architecture.Constraint
import Triptych.Architecture.Assemble
import Triptych.Architecture.Emit
import Triptych.Theorems.RelationalParser
import Triptych.Theorems.Unambiguity
import Triptych.Theorems.Value

/-!
# `triptych` embedded DSL

Surface syntax for flat non-recursive attribute grammars, transcribing the `::=`
grammars written in `doc/CedarDoc/*.lean`. Lean's own `syntax`/`declare_syntax_cat`
framework does all the *parsing* of the notation; this module declares the notation
and elaborates the resulting `Syntax` tree into the generated declarations.

The command starts with a grammar and may add a value function, constraints, parser/printer
bindings, and generated-file output:

```
triptych Decimal where
  grammar
    Decimal  ::= Sign Natural "." Fraction
    Sign     ::= sign
    Natural  ::= digit+
    Fraction ::= digit{1,4}
  value
    Sign * (nat Natural * 10 ^ 4 + nat Fraction * 10 ^ (4 - len Fraction))
  constraints
    value ∈ [Int64.MIN, Int64.MAX]
```

* **`grammar`** (required) — the EBNF productions. Elaborated fully into the core
  `Triptych.Grammar` value bound to `<Name>.grammar`. `grammar` is used rather than
  `syntax` because `syntax` is a reserved Lean keyword.
* **`value`** / **`value'`** (optional) — an analyzable arithmetic expression or an opaque
  capture-to-value function.
* **`constraints`** (optional) — predicates in a small DSL. A predicate belongs to `IsWf`
  unless its original surface syntax explicitly mentions the final `value`; only those
  final-value predicates belong to `SatisfiesConstraints`.
* **`constraints'`** (optional) — opaque Boolean predicates over scalar capture strings and
  repeated-capture lists. Since this escape cannot reference the final `value`, its entries
  belong to `IsWf`.

Grammar notation:
* a production is `Name ::= item item …`
* an item is a string literal, a nonterminal reference (`ident`), a terminal
  (`digit`/`hexDigit`/`bit` with a length suffix), an optional `[item]`, or separated
  repetition
* length suffix: `+` (one-or-more), `{n}` (exactly), `{lo,hi}` (between)

Capture names are Lean identifiers. A name that collides with Lean or Triptych syntax must be
escaped everywhere with guillemets, for example `«bit»`. Triptych preserves the semantic spelling,
quotes generated Lean identifiers automatically, and rejects public surface-binder collisions
instead of silently renaming them.
-/

namespace Triptych

open Lean Elab Command

/-- Length bound for a terminal or repetition: `+`, `{n}`, or `{lo,hi}`. -/
declare_syntax_cat fmtLen
syntax "+"                : fmtLen
syntax "{" num "}"        : fmtLen
syntax "{" num "," num "}" : fmtLen

/-- A grammar item: literal, production reference, terminal, optional item, sign, or repetition. -/
declare_syntax_cat fmtItem
syntax str                : fmtItem  -- literal
syntax "digit" fmtLen     : fmtItem  -- decimal terminal
syntax "hexDigit" fmtLen  : fmtItem  -- hex terminal
syntax "bit" fmtLen       : fmtItem  -- binary terminal (`0`/`1`)
syntax rawIdent           : fmtItem  -- nonterminal reference
syntax "[" fmtItem "]"    : fmtItem  -- optional
-- Dedicated SIGN terminal: an optional leading `"-"`, whose CAPTURE denotes ±1 in `value` (bare
-- name, no `sign` keyword). Sugar for `["-"]` denotationally (so the engine/proofs are unchanged),
-- but only legal as a production's SOLE rhs item (`Sign ::= sign`), so the sign always lives in its
-- own named capture — the fix for the "bare `["-"]` is invisible to `value`" trap.
syntax "sign"             : fmtItem  -- optional '-' sign token (see CAPTURE RULE)
-- separated GROUP repetition: `rep H16 sepBy ":" {8}` = eight `H16`s joined by `":"`
-- (`item (sep item)*`, item-count per the `fmtLen`: `{8}`→exactly, `{1,8}`→range, `+`→≥1).
syntax "rep" fmtItem "sepBy" str fmtLen : fmtItem

/-- One production alternative: a sequence of grammar items. -/
declare_syntax_cat fmtSeq
syntax (colGt fmtItem)+ : fmtSeq

/-- A grammar production with one or more alternatives: `Name ::= seq | seq`. -/
declare_syntax_cat fmtProd
syntax withPosition(atomic(rawIdent " ::= ") sepBy1(fmtSeq, " | ")) : fmtProd

/-- Optional constraints. Capture-only predicates refine `IsWf`; predicates that mention
    `value` refine `SatisfiesConstraints`. -/
syntax fmtConstraints := withPosition("constraints" (colGt constraintExpr)+)

/-- An escape argument: `X` passes its first capture; `[X]` passes every repeated capture. -/
declare_syntax_cat fmtEscArg
syntax rawIdent         : fmtEscArg
syntax "[" rawIdent "]" : fmtEscArg

/-- A Lean function applied to capture arguments in `value'` or `constraints'`. -/
declare_syntax_cat fmtEscEntry
syntax withPosition(ident (ppSpace colGt fmtEscArg)+) : fmtEscEntry

/-- Escape section for Boolean constraints that are not expressible in the constraint DSL. -/
syntax fmtConstraintsEsc := withPosition("constraints'" (colGt fmtEscEntry)+)

/-- `ofSpec f` maps the specification value to the domain value returned by the generated parser.
    Constrain lossy conversions to a range where they are faithful. -/
syntax fmtOfSpec := "ofSpec" term

/-- `toSpec f` maps a parser or printer domain value back to the specification value. -/
syntax fmtToSpec := "toSpec" term

/-- Optional value formula, followed by optional `ofSpec` and `toSpec` conversions. -/
syntax fmtValue :=
  withPosition("value" colGt valExpr (colGt fmtOfSpec)? (colGt fmtToSpec)?)

/-- Escape value section for Lean computations that are not expressible in the value DSL. -/
syntax fmtValueEsc := withPosition("value'" fmtEscEntry (colGt fmtToSpec)?)

/-- `parser p` names an existing parser to validate against the generated specification.
    It emits agreement obligations and a checked wrapper. -/
syntax fmtParser := "parser" term

/-- Printer configuration for a Triptych format. -/
declare_syntax_cat fmtPrinter

/-- Synthesizes a certified printer for a supported grammar and value formula. -/
syntax "printer " "auto" : fmtPrinter

/-- `printer f` names a serializer to verify and use for derived roundtrip results. -/
syntax "printer" term : fmtPrinter

/-- `to "dir"` writes `spec.lean` and `parser.lean`, and creates `soundness.lean` once when
    semantic obligations are required. -/
syntax fmtTo := "to " str

/-- Defines a Triptych format. `grammar` is required; optional sections must follow the order
    `value`, `value'`, `constraints`, `constraints'`, `parser`, `printer`, then `to`. -/
syntax (name := triptychCmd)
  ("#show ")? "triptych " ident " where "
    "grammar" (colGt fmtProd)+
    (fmtValue)?
    (fmtValueEsc)?
    (fmtConstraints)?
    (fmtConstraintsEsc)?
    (fmtParser)?
    (fmtPrinter)?
    (fmtTo)? : command

/-- Elaborate a `fmtLen` into a `LenSpec` term. -/
def elabLen : TSyntax `fmtLen → CommandElabM (TSyntax `term)
  | `(fmtLen| +)                      => `(LenSpec.atLeastOne)
  | `(fmtLen| { $n:num })             => `(LenSpec.exactly $n)
  | `(fmtLen| { $lo:num , $hi:num })  => `(LenSpec.between $lo $hi)
  | s                                 => throwErrorAt s "unrecognized length suffix"

/-- Does this repetition-count `fmtLen` have a ZERO lower bound (`{0}` or `{0,_}`)? Such a
    repetition admits a zero-item match denotationally but the decoder always matches ≥ 1
    item, so the DSL rejects it (mirrors the empty-separator rejection). `+` is `lo = 1`. -/
def repLenLoZero : TSyntax `fmtLen → Bool
  | `(fmtLen| { $n:num })          => n.getNat == 0
  | `(fmtLen| { $lo:num , $_:num }) => lo.getNat == 0
  | _                              => false

/-- A `fmtLen` reused as a repetition COUNT bound → `(lo, hi?)`: `{n}`→exactly `n`,
    `{lo,hi}`→range, `+`→at least one (unbounded). -/
def elabRepBounds : TSyntax `fmtLen → CommandElabM (TSyntax `term × TSyntax `term)
  | `(fmtLen| +)                     => do pure (← `((1 : Nat)), ← `((none : Option Nat)))
  | `(fmtLen| { $n:num })            => do pure (← `($n), ← `(some $n))
  | `(fmtLen| { $lo:num , $hi:num }) => do pure (← `($lo), ← `(some $hi))
  | s                                => throwErrorAt s "unrecognized repetition count"

/-- The first total-printer synthesis shape: a root containing a dedicated sign followed by a
    nonempty decimal digit run, denoting `Sign * nat Digits`. -/
private structure SignedIntegerPrinterShape where
  root : String
  signCapture : String
  digits : String

/-- Check that the grammar has exactly the structural shape required by the signed-integer
    printer rule. The value-expression capture names are supplied separately so the check cannot
    accidentally invert a structurally similar but semantically unrelated production. -/
private def signedIntegerPrinterShape? (g : Grammar) (signName digitsName : String) :
    Option SignedIntegerPrinterShape := do
  let root ← g.startProd?
  guard <| root.alts =
    [[SymItem.mk (.ref signName) false, SymItem.mk (.ref digitsName) false]]
  let signProduction ← g.prod? signName
  guard <| signProduction.alts = [[SymItem.mk (.lit "-") true]]
  let digits ← g.prod? digitsName
  guard <| digits.alts =
    [[SymItem.mk (.term .digit .atLeastOne) false]]
  return ⟨root.name, signName, digitsName⟩

/-- Recognize the analyzable value expression inverted by `signedIntegerPrinterShape?`. -/
private def signedIntegerValueCaptures? (e : TSyntax `valExpr) : Option (String × String) :=
  match e with
  | `(valExpr| $signId:ident * nat $digits:ident) =>
      some (signId.getId.toString, digits.getId.toString)
  | `(valExpr| nat $digits:ident * $signId:ident) =>
      some (signId.getId.toString, digits.getId.toString)
  | _ => none

/-- Emit the total signed-integer presentation certificate and its typed-view witness. -/
private def signedIntegerPrinterCommands (specName : Name)
    (shape : SignedIntegerPrinterShape) :
    CommandElabM (Array (TSyntax `command)) := do
  let rootName := specName ++ `Derivation ++ shape.root.toName
  let signName := specName ++ `Derivation ++ shape.signCapture.toName
  let digitsName := specName ++ `Derivation ++ shape.digits.toName
  let rootTypeId := mkIdent rootName
  let rootCtorId := mkIdent (rootName ++ `alt0)
  let rootValidId := mkIdent (rootName ++ `Valid)
  let rootRenderId := mkIdent (rootName ++ `render)
  let rootCapturesId := mkIdent (rootName ++ `capturesWith)
  let rootToViewId := mkIdent (rootName ++ `toView)
  let rootDecodeViewRenderId := mkIdent (rootName ++ `decodeView_render)
  let signCtorId := mkIdent (signName ++ `alt0)
  let signValidId := mkIdent (signName ++ `Valid)
  let signRenderId := mkIdent (signName ++ `render)
  let signCapturesId := mkIdent (signName ++ `capturesWith)
  let digitsCtorId := mkIdent (digitsName ++ `alt0)
  let digitsValidId := mkIdent (digitsName ++ `Valid)
  let digitsRenderId := mkIdent (digitsName ++ `render)
  let digitsCapturesId := mkIdent (digitsName ++ `capturesWith)
  let viewId := mkIdent (specName ++ `View)
  let viewOfMapId := mkIdent (specName ++ `View ++ `ofMap)
  let viewValidId := mkIdent (specName ++ `View ++ `Valid)
  let denotationId := mkIdent (specName ++ `View ++ `denotation)
  let valueId := mkIdent (specName ++ `value)
  let decodeViewId := mkIdent (specName ++ `decodeView)
  let toDerivationId := mkIdent (specName ++ `toDerivation)
  let printerId := mkIdent (specName ++ `defaultPrinter)
  let toStringId := mkIdent (specName ++ `toString)
  let encodeViewId := mkIdent (specName ++ `encode_view)
  let asSimp (id : TSyntax `ident) :
      CommandElabM (TSyntax `Lean.Parser.Tactic.simpLemma) := do
    let term : TSyntax `term := ⟨id.raw⟩
    `(Lean.Parser.Tactic.simpLemma| $term:term)
  let structuralSimp ←
    #[toDerivationId, rootValidId, signValidId, digitsValidId].mapM asSimp
  let denotationSimp ←
    #[toDerivationId, rootToViewId, rootRenderId, rootCapturesId,
      signRenderId, signCapturesId, digitsRenderId, digitsCapturesId,
      viewOfMapId, denotationId, valueId].mapM asSimp
  let toDerivation ←
    `(def $toDerivationId (i : Int) : $rootTypeId :=
        $rootCtorId
          ($signCtorId (if i < 0 then some () else none))
          ($digitsCtorId (toString i.natAbs)))
  let printerCommand ←
    `(def $printerId :
        Triptych.DerivationPrinter $rootRenderId $rootValidId $rootToViewId
          $viewValidId $denotationId where
        toDerivation := $toDerivationId
        structural i := by
          simp only [$structuralSimp,*]
          exact
            ⟨by split <;> simp [Triptych.OptionalValid],
              Triptych.matchesTerm_digit_toString i.natAbs⟩
        valid _ := by trivial
        rightInverse i := by
          by_cases h : i < 0
          · simp [$denotationSimp,*, Triptych.CaptureMap.toEnv,
              Triptych.referenceCaptures, Triptych.renderOptional,
              Triptych.capturesOptional, h, Triptych.readNat_repr,
              Triptych.signOf, Triptych.natOf]
            exact (Int.eq_neg_natAbs_of_nonpos (a := i) (by omega)).symm
          · simp [$denotationSimp,*, Triptych.CaptureMap.toEnv,
              Triptych.referenceCaptures, Triptych.renderOptional,
              Triptych.capturesOptional, h, Triptych.readNat_repr,
              Triptych.signOf, Triptych.natOf]
            exact Int.natAbs_of_nonneg (a := i) (by omega))
  let toStringCommand ←
    `(def $toStringId : Int → String :=
        Triptych.DerivationPrinter.toString $printerId)
  let encodeView ←
    `(theorem $encodeViewId (i : Int) :
        ∃ v : $viewId,
          $decodeViewId ($toStringId i) = some v ∧
          $viewValidId v ∧ $denotationId v = i :=
        Triptych.DerivationPrinter.encodeView $printerId $rootDecodeViewRenderId i)
  return #[toDerivation, printerCommand, toStringCommand, encodeView]

/-- Reject a bare capture spelling that Lean has registered as syntax. Escaped identifiers retain
    their exact semantic name, while generated Lean identifiers are quoted automatically. -/
private def validateCaptureIdent (i : TSyntax `ident) : CommandElabM Unit := do
  let raw := match i.raw with
    | .ident _ rawVal _ _ => rawVal.toString
    | _ => i.getId.toString
  let tokens := Lean.Parser.getTokenTable (← getEnv)
  for segment in i.getId.toString.splitOn "." do
    if (tokens.find? segment).isSome && !raw.contains s!"«{segment}»" then
      let qualified :=
        if i.getId.toString.contains "." then
          s!" (for example, `{i.getId.toString.replace segment s!"«{segment}»"}`)"
        else
          ""
      throwErrorAt i m!"capture name segment `{segment}` is a reserved Lean/Triptych keyword; \
        escape it as `«{segment}»` everywhere it is used{qualified}. Triptych preserves the \
        semantic capture name and quotes generated Lean identifiers automatically."

/-- Collect identifier leaves from a value or constraint expression. In those syntax categories,
    every identifier leaf denotes a capture. -/
private partial def captureIdents (stx : Syntax) : Array (TSyntax `ident) :=
  match stx with
  | .ident .. => #[⟨stx⟩]
  | .node _ _ args => args.foldl (fun out arg => out ++ captureIdents arg) #[]
  | _ => #[]

/-- Public surface functions use normalized Lean binders. Distinct captures may not collapse to
    the same binder, because silently suffixing a public parameter would obscure the spec. -/
private def validateSurfaceBinders (loc : Syntax) (context : String)
    (captures : List String) (rejectRepeated := false) : CommandElabM Unit := do
  let mut semanticSeen : List String := []
  let mut binders : Std.HashMap String String := {}
  for capture in captures do
    if semanticSeen.contains capture then
      if rejectRepeated then
        throwErrorAt loc m!"capture `{capture}` appears more than once in {context}; Triptych \
          does not silently invent duplicate public binders"
    else
      semanticSeen := capture :: semanticSeen
      let binder := surfaceBinder capture
      if let some previous := binders.get? binder then
        throwErrorAt loc m!"captures `{previous}` and `{capture}` both normalize to the public \
          Lean binder `{binder}` in {context}; rename or qualify one capture. Triptych does not \
          silently rename public binders."
      binders := binders.insert binder capture

/-- Elaborate a non-optional item into a `Sym` term. Errors on a bare `[…]`
    (optionality is handled one level up, in `elabItem`). -/
-- NOTE: the grammar-literal quotations below use UNQUALIFIED constructor names
-- (`Sym.lit`, `Production.mk`, …). The generated file `open`s `Triptych`, so these
-- resolve there and read cleanly; within this module `open Lean Elab Command` + the
-- enclosing `namespace Triptych` also make them resolve.
partial def elabSym : TSyntax `fmtItem → CommandElabM (TSyntax `term)
  | `(fmtItem| $s:str)            => `(Sym.lit $s)
  | `(fmtItem| digit $l:fmtLen)   => do `(Sym.term TokClass.digit $(← elabLen l))
  | `(fmtItem| hexDigit $l:fmtLen) => do `(Sym.term TokClass.hexDigit $(← elabLen l))
  | `(fmtItem| bit $l:fmtLen)     => do `(Sym.term TokClass.bit $(← elabLen l))
  | `(fmtItem| rep $inner:fmtItem sepBy $sep:str $l:fmtLen) => do
      if sep.getString.isEmpty then
        throwErrorAt sep "repetition separator must be non-empty (an empty separator makes the \
          item count unrecoverable — `decode` and `IsWf` would disagree)"
      if repLenLoZero l then
        throwErrorAt l "repetition must require at least one item (lower bound ≥ 1); a \
          zero-item repetition has no separated-list decoding"
      let (lo, hi) ← elabRepBounds l
      `(Sym.rep $sep $(← elabSym inner) $lo $hi)
  | `(fmtItem| $i:ident)          => do
      validateCaptureIdent i
      `(Sym.ref $(Syntax.mkStrLit i.getId.toString))
  | s                             => throwErrorAt s "unrecognized grammar item"

/-- Elaborate an item into a `SymItem` term, setting `optional` for `[…]`. The `sign` terminal
    lowers to the SAME `SymItem` as `["-"]` (an optional literal `-`) — sign is grammar sugar, so
    the engine/denotation/proofs never see a new constructor. -/
def elabItem : TSyntax `fmtItem → CommandElabM (TSyntax `term)
  | `(fmtItem| [ $inner:fmtItem ]) => do
      `(SymItem.mk $(← elabSym inner) true)
  | `(fmtItem| sign) => `(SymItem.mk (Sym.lit "-") true)
  | other => do
      `(SymItem.mk $(← elabSym other) false)

/-- Elaborate one alternative (`fmtSeq`) into a `List SymItem` term. -/
def elabSeq : TSyntax `fmtSeq → CommandElabM (TSyntax `term)
  | `(fmtSeq| $items:fmtItem*) => do
      let itemTerms ← items.mapM elabItem
      let sep : Syntax.TSepArray `term "," := .ofElems itemTerms
      `([$sep,*])
  | s => throwErrorAt s "unrecognized alternative"

/-- Elaborate a production (`Name ::= seq | seq | …`) into a `Production` term. -/
def elabProd : TSyntax `fmtProd → CommandElabM (TSyntax `term)
  | `(fmtProd| $lhs:ident ::= $alts:fmtSeq|*) => do
      validateCaptureIdent lhs
      let altTerms ← alts.getElems.mapM elabSeq
      let sep : Syntax.TSepArray `term "," := .ofElems altTerms
      `(Production.mk $(Syntax.mkStrLit lhs.getId.toString) [$sep,*])
  | s => throwErrorAt s "unrecognized production"

/-! Parse the grammar syntax into `Grammar`/`Production`/`Sym` *values* (not terms), so
    the inlined-predicate synthesizer (`Triptych.prodPred`, `topoOrder`) can run at
    elaboration time. -/

def parseLen : TSyntax `fmtLen → CommandElabM LenSpec
  | `(fmtLen| +)                     => pure .atLeastOne
  | `(fmtLen| { $n:num })            => pure (.exactly n.getNat)
  | `(fmtLen| { $lo:num , $hi:num }) => pure (.between lo.getNat hi.getNat)
  | s                                => throwErrorAt s "unrecognized length suffix"

/-- A `fmtLen` reused as a repetition COUNT bound → `(lo, hi?)` VALUE (mirrors
    `elabRepBounds`): `{n}`→(n, some n), `{lo,hi}`→(lo, some hi), `+`→(1, none). -/
def parseRepBounds : TSyntax `fmtLen → CommandElabM (Nat × Option Nat)
  | `(fmtLen| +)                     => pure (1, none)
  | `(fmtLen| { $n:num })            => pure (n.getNat, some n.getNat)
  | `(fmtLen| { $lo:num , $hi:num }) => pure (lo.getNat, some hi.getNat)
  | s                                => throwErrorAt s "unrecognized repetition count"

partial def parseSym : TSyntax `fmtItem → CommandElabM Sym
  | `(fmtItem| $s:str)             => pure (.lit s.getString)
  | `(fmtItem| digit $l:fmtLen)    => do pure (.term .digit (← parseLen l))
  | `(fmtItem| hexDigit $l:fmtLen) => do pure (.term .hexDigit (← parseLen l))
  | `(fmtItem| bit $l:fmtLen)      => do pure (.term .bit (← parseLen l))
  | `(fmtItem| rep $inner:fmtItem sepBy $sep:str $l:fmtLen) => do
      if sep.getString.isEmpty then
        throwErrorAt sep "repetition separator must be non-empty (an empty separator makes the \
          item count unrecoverable — `decode` and `IsWf` would disagree)"
      if repLenLoZero l then
        throwErrorAt l "repetition must require at least one item (lower bound ≥ 1); a \
          zero-item repetition has no separated-list decoding"
      let (lo, hi) ← parseRepBounds l
      pure (.rep sep.getString (← parseSym inner) lo hi)
  | `(fmtItem| $i:ident)           => do
      validateCaptureIdent i
      pure (.ref i.getId.toString)
  | s                              => throwErrorAt s "unrecognized grammar item"

def parseItem : TSyntax `fmtItem → CommandElabM SymItem
  | `(fmtItem| [ $inner:fmtItem ]) => do pure { sym := ← parseSym inner, optional := true }
  | `(fmtItem| sign)               => pure { sym := .lit "-", optional := true }
  | other                          => do pure { sym := ← parseSym other, optional := false }

def parseSeq : TSyntax `fmtSeq → CommandElabM Seq
  | `(fmtSeq| $items:fmtItem*) => items.toList.mapM parseItem
  | s => throwErrorAt s "unrecognized alternative"

def parseProd : TSyntax `fmtProd → CommandElabM Production
  | `(fmtProd| $lhs:ident ::= $alts:fmtSeq|*) => do
      validateCaptureIdent lhs
      pure { name := lhs.getId.toString, alts := ← alts.getElems.toList.mapM parseSeq }
  | s => throwErrorAt s "unrecognized production"

/-- Destructure an ESCAPE entry `f X [Y] …` into its head function ident and its capture args,
    each paired with a LIST flag (`true` for a bracketed `[X]`, i.e. all repeated spans; `false`
    for a scalar `X`). Shared by `value'` (list args allowed) and `constraints'`. -/
def parseEscEntryArgs :
    TSyntax `fmtEscEntry → CommandElabM (TSyntax `ident × Array (TSyntax `ident × Bool))
  | `(fmtEscEntry| $f:ident $args:fmtEscArg*) => do
      let parsed ← args.mapM fun a => match a with
        | `(fmtEscArg| $i:ident) => do
            validateCaptureIdent i
            pure (i, false)
        | `(fmtEscArg| [ $i:ident ]) => do
            validateCaptureIdent i
            pure (i, true)
        | s => throwErrorAt s "unrecognized escape argument"
      pure (f, parsed)
  | s => throwErrorAt s "unrecognized escape entry"

/-- Destructure an ESCAPE entry into head + scalar capture idents. Kept for callers that require
    a scalar-only escape; collection-aware sections should use `parseEscEntryArgs`. -/
def parseEscEntry (ctx : String := "escape") :
    TSyntax `fmtEscEntry → CommandElabM (TSyntax `ident × Array (TSyntax `ident))
  | e => do
      let (f, args) ← parseEscEntryArgs e
      let is ← args.mapM fun (i, isList) => do
        if isList then
          throwErrorAt i s!"list argument `[{i.getId}]` is not supported in a `{ctx}` entry \
            (this caller accepts scalar captures only); use a scalar `{i.getId}`"
        pure i
      pure (f, is)

/-- Strip macro scopes from every identifier in a syntax tree, so pretty-printing yields
    clean source without hygiene daggers (`✝`). Used when writing generated declarations
    to a file. -/
partial def deHygiene (stx : Syntax) : Syntax :=
  match stx with
  | .ident info rawVal val pre => .ident info rawVal val.eraseMacroScopes pre
  | .node info kind args       => .node info kind (args.map deHygiene)
  | s                          => s

private partial def findLakeRoot (dir : System.FilePath) : IO (Option System.FilePath) := do
  if (← System.FilePath.pathExists (dir / "lakefile.lean")) ||
      (← System.FilePath.pathExists (dir / "lakefile.toml")) then
    return some dir
  match dir.parent with
  | none => return none
  | some parent => findLakeRoot parent

/-- Return the package-local module import for the file containing the `triptych` command.

Lean's language server may name a file relative to the workspace root even when it belongs to
a nested Lake package (`cedar-examples.Inputs.Decimal` instead of `Inputs.Decimal`). Deriving
the name from the source path relative to its nearest Lake root makes generated imports stable
under both direct Lake builds and a language server rooted at an enclosing repository. -/
private def callerModuleForOutput : CommandElabM String := do
  let fallback := (← getMainModule).toString
  let sourcePath ← IO.FS.realPath (System.FilePath.mk (← getFileName))
  let some sourceDir := sourcePath.parent | return fallback
  let some root ← findLakeRoot sourceDir | return fallback
  let rootParts := root.normalize.components
  let sourceParts := (sourcePath.normalize.withExtension "").components
  unless sourceParts.take rootParts.length == rootParts do
    return fallback
  let relativeParts := sourceParts.drop rootParts.length
  if relativeParts.isEmpty then
    return fallback
  return (relativeParts.foldl Name.str .anonymous).toString

/-- Elaborate the `triptych` command: generates + elaborates the declarations, tagged
    into four sections, and — with a `to "<dir>"` clause — writes them as one module
    `<dir>/spec.lean`. `#show` additionally logs each declaration.

    The generated file is ONE module in four `═══`-banner sections (dependency order):
    * **spec** (`emitSpec`) — the reader-facing spec: `grammar`, readable per-production
      `IsWf.*` predicates, `value`, present constraint phases, and `IsValid`.
    * **engine** (`emitEngine`) — the analyzable/executable machinery: deep `valueExpr`/
      `valueFn`/`constraints` ASTs, `computeValue`, and typed decoding support.
    * **soundness** (`emitSound`) — the guarantees tying the two together: the surface⟺engine
      `Internal.matchesRef.*` lemmas + equivalence theorems, and the derived `DecidablePred`
      instances transported from the generic interpreter.
    * **contracts** (`emitContract`, only with a `parser` clause) — the sorried obligations
      against the external parser, stated over the SURFACE `IsValid`/`computeValue`
      (discharged later by bridging to `decode` via `IsWf_equiv`). -/
@[command_elab triptychCmd]
def elabTriptych : CommandElab := fun stx => do
  match stx with
  | `($[#show%$sh]? triptych $name:ident where grammar $prods:fmtProd* $[$v:fmtValue]? $[$ve:fmtValueEsc]? $[$cs:fmtConstraints]? $[$cse:fmtConstraintsEsc]? $[$pr:fmtParser]? $[$pp:fmtPrinter]? $[$to?:fmtTo]?) => do
      let showing := sh.isSome
      -- Buffers, one per GENERATED FILE (the output is split three ways by audience):
      --   spec.lean     ← bufS: the readable surface (cite) — grammar, `IsWf.*`, `value`,
      --                   present constraint phases, `IsValid`. Proof-free.
      --   parser.lean   ← bufE ++ bufP ++ bufR: the runnable + trusted artifact (run + trust)
      --                   — engine bundle, ALL auto-discharged proofs (`IsWf_equiv`,
      --                   `computeValue_eq`, decidability), and the generated verified `parse`
      --                   + its discharged contracts. No `sorry`.
      --   soundness.lean ← bufC: printer and external-parser obligations (`sorry`d), emitted
      --                   when either corresponding clause is present.
      let bufS ← IO.mkRef (#[] : Array String)   -- spec file
      let bufE ← IO.mkRef (#[] : Array String)   -- engine (→ parser file)
      let bufP ← IO.mkRef (#[] : Array String)   -- reconciliation proofs (→ parser file)
      let bufR ← IO.mkRef (#[] : Array String)   -- generated verified parser (→ parser file)
      -- soundness.lean is partitioned into TWO sections, one per parser: `bufCg` holds the
      -- GENERATED parser's `encode_view` obligation + printer theorems (about `<Name>.parse`),
      -- `bufCx` the
      -- EXTERNAL parser's (about the real Cedar `parse`). Written generated-first, because the
      -- external printer theorems reuse its derived encode projections.
      let bufCg ← IO.mkRef (#[] : Array String)  -- generated-parser obligations (→ soundness file)
      let bufCx ← IO.mkRef (#[] : Array String)  -- external-parser obligations (→ soundness file)
      let record (buf : IO.Ref (Array String)) (cmd : TSyntax `command) : CommandElabM Unit := do
        let clean : TSyntax `command := ⟨deHygiene cmd.raw⟩
        let src := (← liftCoreM (Lean.PrettyPrinter.ppCommand clean)).pretty
        if showing then logInfo src
        buf.modify (·.push src)
      -- All sections are elaborated AND recorded (the generated files hold them, split by buffer).
      let emitSpec   (cmd : TSyntax `command) : CommandElabM Unit := do record bufS cmd; elabCommand cmd
      let emitEngine (cmd : TSyntax `command) : CommandElabM Unit := do record bufE cmd; elabCommand cmd
      let emitSound  (cmd : TSyntax `command) : CommandElabM Unit := do record bufP cmd; elabCommand cmd
      let emitParser (cmd : TSyntax `command) : CommandElabM Unit := do record bufR cmd; elabCommand cmd
      -- Two soundness-contract emitters, one per partition (`Gen` = generated parser, `Ext` = external).
      let emitContractGen (cmd : TSyntax `command) : CommandElabM Unit := do record bufCg cmd; elabCommand cmd
      let emitContractExt (cmd : TSyntax `command) : CommandElabM Unit := do record bufCx cmd; elabCommand cmd
      -- Grammar data literal (SPEC): the auditable EBNF transcription; the interpreter,
      -- proofs, and `SatisfiesConstraints`'s decode bridge all reference it. The START symbol
      -- is the FIRST production's name (NOT the `triptych` display name — they may differ,
      -- e.g. `triptych IPv4` whose first production is `V4Addr`); it must name a real
      -- production so `grammar.prod? grammar.start` resolves.
      let prodVals ← prods.toList.mapM parseProd
      let startName := (prodVals.head?.map (·.name)).getD name.getId.toString
      let gval : Triptych.Grammar :=
        { start := startName, prods := prodVals }
      if let some cycle := gval.cycle? then
        let cycleStart := cycle.headD startName
        let mut cycleLoc : Syntax := name
        for prodStx in prods do
          if let `(fmtProd| $lhs:ident ::= $_:fmtSeq|*) := prodStx then
            if lhs.getId.toString == cycleStart then
              cycleLoc := lhs
        throwErrorAt cycleLoc
          m!"recursive grammar productions are unsupported; cycle: \
            {String.intercalate " -> " cycle}"
      -- SIGN CAPTURES: productions whose sole rhs is the dedicated `sign` terminal (`Sign ::= sign`).
      -- Detected SYNTACTICALLY (a `sign` item vs a hand-written `["-"]` lower to the same `Sym`, so
      -- only the surface tells them apart). Their NAMES are exactly the captures a `value` may
      -- reference BARE (denoting ±1); the value-section validation below rejects a bare ref to a
      -- non-sign capture, and `nat`/`int`/`len` OF a sign capture. A `sign` used anywhere but as a
      -- sole rhs is rejected — the sign must own its own capture (the fix for the invisible-sign bug).
      let seqIsSoleSign : TSyntax `fmtSeq → Bool
        | `(fmtSeq| sign) => true
        | _ => false
      let seqMentionsSign : TSyntax `fmtSeq → Bool
        | `(fmtSeq| $items:fmtItem*) => items.any (fun it => it matches `(fmtItem| sign))
        | _ => false
      let mut signCaptures : List String := []
      for pStx in prods do
        if let `(fmtProd| $lhs:ident ::= $alts:fmtSeq|*) := pStx then
          let mut anySign := false
          for sq in alts.getElems do
            if seqIsSoleSign sq then
              anySign := true
            else if seqMentionsSign sq then
              throwErrorAt sq "the `sign` terminal must be a production's SOLE right-hand side \
                (`{lhs.getId} ::= sign`), so the sign owns its own capture; found it mixed with \
                other items. Wrap the sign in its own production and reference that."
          if anySign then
            signCaptures := signCaptures ++ [lhs.getId.toString]
      let prodTerms ← prods.mapM elabProd
      let sep : Syntax.TSepArray `term "," := .ofElems prodTerms
      let grammarIdent := mkIdentFrom name (name.getId ++ `grammar)
      emitSpec (← `(def $grammarIdent : Grammar :=
                    Grammar.mk $(Syntax.mkStrLit startName) [$sep,*]))
      -- A lossless typed syntax tree for every production. Types, renderers, and structural
      -- validity predicates are reader-facing; exact captures and proofs remain in parser.lean.
      for prod in Triptych.topoOrder gval do
        for cmd in ← Triptych.derivationSpecCommands name.getId prod do
          emitSpec cmd
        emitEngine (← Triptych.derivationValidityInstanceCommand name.getId prod)
        emitEngine (← Triptych.derivationCaptureCommand name.getId prod)
      -- Per-production well-formedness (SPEC): `<Name>.IsWf.<Prod>` for each production as
      -- an INLINED structural predicate (∃ named captures, s = … ∧ …) — the readable form,
      -- reading like the hand specs (`IsWfDatetime`, `IsWfV4`). These are reader-facing, so
      -- SPEC section. Emitted in topological (leaf-first) order.
      let rec repeatedRefNames : Sym → List String
        | .rep _ item _ _ => item.refName?.toList ++ repeatedRefNames item
        | _ => []
      let repeatedCaptures :=
        gval.prods.flatMap (fun p =>
          p.alts.flatMap (fun alt => alt.flatMap (repeatedRefNames ·.sym))) |>.eraseDups
      let validateCounts (loc : Syntax) (names : List String) : CommandElabM Unit := do
        for capture in names do
          unless repeatedCaptures.contains capture do
            throwErrorAt loc m!"`count {capture}` does not name a repeated item. Declare \
              `rep {capture} sepBy \"...\" <len>` before reading its count."
      let grammarStaticallyUnique := gval.staticUnique
      if grammarStaticallyUnique then
        let uniqueId := mkIdentFrom name (name.getId ++ `grammarDecodeUnique)
        emitSound (←
          `(theorem $uniqueId : GrammarDecodeUnique $grammarIdent :=
              GrammarDecodeUnique.of_staticUnique $grammarIdent (by decide)))
        let functionalId := mkIdentFrom name (name.getId ++ `grammarCaptureFunctional)
        emitSound (←
          `(theorem $functionalId : GrammarCaptureFunctional $grammarIdent :=
              GrammarCaptureFunctional.of_unique $grammarIdent $uniqueId))
      for prod in Triptych.topoOrder gval do
        emitSound (←
          Triptych.derivationMatchCommand name.getId grammarIdent gval prod)
      for cmd in ←
          Triptych.derivationRootProofCommands
            name.getId grammarIdent gval grammarStaticallyUnique do
        emitSound cmd
      for prod in Triptych.topoOrder gval do
        let pIdent := mkIdentFrom name (name.getId ++ `IsWf ++ prod.name.toName)
        let sVar ← `(s)
        let body ← Triptych.prodPred name.getId prod sVar
        emitSpec (← `(def $pIdent (s : String) : Prop := $body))
      -- Reconcile grammar layout, full well-formedness, and final-value validity independently.
      -- `IsWf.<start>` is grammar-only; top-level `IsWf` additionally contains every constraint
      -- that does not mention the final `value`, and is proved equivalent to the generic
      -- interpreter expression `Triptych.isWf grammar constraints`.
      let emitReconcile (hasWfConstraints hasValueConstraints hasValue : Bool) :
          CommandElabM Unit := do
        let fuelBound := gval.prods.length
        for prod in Triptych.topoOrder gval do
          let depth := Triptych.subtreeDepth gval prod.name fuelBound
          emitSound (← Triptych.matchesRefProof name.getId grammarIdent prod depth)
        if let some startProd := gval.prods.find? (·.name == gval.start) then
          emitSound (← Triptych.isWfGrammarEquivProof name.getId grammarIdent startProd)
          emitSound (← Triptych.isWfEquivProof name.getId hasWfConstraints)
          if hasValueConstraints then
            emitSound (←
              Triptych.satisfiesConstraintsEquivProof name.getId true hasValue)
          emitSound (← Triptych.isValidEquivProof name.getId hasValueConstraints)
          let grammarEquivId := mkIdentFrom name (name.getId ++ `IsWfGrammar_equiv)
          let wfEquivId := mkIdentFrom name (name.getId ++ `IsWf_equiv)
          let startIsWfId := mkIdentFrom name (name.getId ++ `IsWf ++ startProd.name.toName)
          let wfSurfId := mkIdentFrom name (name.getId ++ `IsWf)
          let accSurfId := mkIdentFrom name (name.getId ++ `IsValid)
          let instGrammarId := mkIdentFrom name (name.getId ++ `instDecidableGrammar)
          let instWfId := mkIdentFrom name (name.getId ++ `instDecidableIsWf)
          let instAccId := mkIdentFrom name (name.getId ++ `instDecidableIsValid)
          emitSound (← `(instance $instGrammarId:ident : DecidablePred $startIsWfId := fun s =>
                        @decidable_of_iff _ _ ($grammarEquivId s)
                          (Triptych.decIsWf $grammarIdent (by decide) s)))
          emitSound (← `(instance $instWfId:ident : DecidablePred $wfSurfId := fun s =>
                        @decidable_of_iff _ _ ($wfEquivId s).symm inferInstance))
          if hasValueConstraints then
            let scEquivId := mkIdentFrom name (name.getId ++ `SatisfiesConstraints_equiv)
            let scSurfId := mkIdentFrom name (name.getId ++ `SatisfiesConstraints)
            let instScId :=
              mkIdentFrom name (name.getId ++ `instDecidableSatisfiesConstraints)
            emitSound (← `(instance $instScId:ident : DecidablePred $scSurfId := fun s =>
                          @decidable_of_iff _ _ ($scEquivId s).symm inferInstance))
          emitSound (← `(instance $instAccId:ident : DecidablePred $accSurfId :=
                        fun s => inferInstance))
      -- Value (optional), processed BEFORE constraints so a constraint may refer to `value`.
      -- DSL tier (`value <formula>`, `v`): elaborate the value-DSL to a `ValExpr` (bound as
      -- `valueExpr`) whose `eval` is the value fn; `valueSub` is the `ValExpr` substituted for
      -- a `value` reference in constraints. ESCAPE tier (`value' f X Y …`, `ve`): bind
      -- `valueFn` to the author's fn applied to the decoded captures (no `ValExpr` AST — so
      -- `computeValue`/contracts, which need the AST, are DSL-tier only).
      let mut valueSub : Option (TSyntax `term) := none
      let mut veIdent? : Option (TSyntax `ident) := none
      let mut valueCaps : List String := []
      -- For a `value'` escape: each value capture paired with its LIST flag (`[X]` ⟹ `true`).
      -- Drives the escape's `computeValue_eq` (a list arg reads via `componentList`, a scalar
      -- via `component`). Empty for the DSL tier (all scalar).
      let mut valueCapArgs : List (String × Bool) := []
      let mut hasValueEsc : Bool := false
      -- Capture binders for the two readable constraint phases. `none` means that phase has no
      -- entries and no phase-specific surface predicate is emitted.
      let mut wfConstrCaps : Option (List (String × Bool)) := none
      let mut valueConstrCaps : Option (List (String × Bool)) := none
      if let some vStx := v then
        let ve : TSyntax `valExpr := ⟨vStx.raw[1]⟩
        for i in captureIdents ve.raw do
          validateCaptureIdent i
        -- SIGN-REFERENCE VALIDATION: a BARE capture name in `value` denotes its sign (±1), so it
        -- must name a dedicated sign production (`X ::= sign`). Reject a bare ref to a non-sign
        -- capture (the old silent-`+1` trap), and reject magnitude readers applied to a sign
        -- capture (a sign holds only `""`/`"-"`, so a magnitude reader on it is meaningless).
        let signRefs := Triptych.valExprSignCaptures ve
        let magRefs := (Triptych.valExprCaptures ve).filter (· ∉ signRefs)
        validateCounts ve.raw (Triptych.valExprCountCaptures ve)
        for r in signRefs do
          unless signCaptures.contains r do
            throwError "value references `{r}` bare, which reads its SIGN (±1) — but `{r}` is not \
              a sign capture. Declare `{r} ::= sign`, or use `nat {r}`/`int {r}`/`len {r}` to read \
              its magnitude/length."
        for r in magRefs do
          if signCaptures.contains r then
            throwError "value reads the magnitude/length of `{r}`, but `{r}` is a sign capture \
              (`{r} ::= sign`, holding only \"\" or \"-\"). Reference it BARE (`{r}`) for its ±1 sign."
        let vfnIdent := mkIdentFrom name (name.getId ++ `valueFn)
        -- engine: the analyzable AST + its eval
        let valTerm ← liftMacroM (elabValExpr ve)
        let veIdent := mkIdentFrom name (name.getId ++ `valueExpr)
        emitEngine (← `(def $veIdent : ValExpr := $valTerm))
        emitEngine (← `(def $vfnIdent : Env → Int := ($veIdent).eval))
        -- spec: a READABLE `<Name>.value` taking the captured component STRINGS directly
        -- (no `Env`), via `natOf`/`intOf`/… — reads like `value(Natural, Fraction) = …`.
        let readable ← liftMacroM (elabValReadableWith none ve)
        let capNames := Triptych.valExprCaptures ve
        validateSurfaceBinders ve.raw "the `value` function" capNames
        let binders : Array (TSyntax `ident) :=
          (capNames.map (fun c => mkIdent (Name.mkSimple (Triptych.surfaceBinder c)))).toArray
        let valIdent := mkIdentFrom name (name.getId ++ `value)
        emitSpec (← `(def $valIdent $[($binders : String)]* : Int := $readable))
        valueSub := some (← `($veIdent))
        veIdent? := some veIdent
        valueCaps := capNames
      else if let some veStx := ve then
        -- `value'` escape section: `value' f X Y …` — author fn applied to captures.
        match veStx with
        | `(fmtValueEsc| value' $e:fmtEscEntry $[$_:fmtToSpec]?) =>
          let (f, args) ← parseEscEntryArgs e
          hasValueEsc := true
          let vfnIdent := mkIdentFrom name (name.getId ++ `valueFn)
          -- ARBITRARY value type: no `: Env → Int` ascription — the author's `f` return type
          -- flows through (whatever α `f` produces: Int, SimpleGraph, matrix, IPNet, …), so a
          -- `value'` escape can parse to a STRUCTURED value. Reads the full `CaptureMap` (not the
          -- collapsed `Env`), so a `[X]` list arg gets EVERY repeated span of `X` (via
          -- `toEnvList`) — the eight `H16` groups of an IPv6 address — while a scalar arg gets
          -- the first span string, exactly as the `Env` reader did.
          emitEngine (← `(def $vfnIdent := $(← liftMacroM (Triptych.opaqueMapClosure f args))))
          -- spec: a READABLE `<Name>.value` — the author's call over the surface binders (return
          -- type inferred from `f`; each binder's type inferred too — `String` for a scalar arg,
          -- `List String` for a `[X]` list arg).
          let capArgs := args.toList.map (fun (i, isList) => (i.getId.toString, isList))
          validateSurfaceBinders veStx.raw "the `value'` function" (capArgs.map (·.1)) true
          -- Typed binders: `String` for a scalar arg, `List String` for a `[X]` list arg.
          let tBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) ←
            args.mapM (fun (i, isList) => do
              let b := mkIdent (Name.mkSimple (Triptych.surfaceBinder i.getId.toString))
              if isList then `(bracketedBinder| ($b : List String))
              else `(bracketedBinder| ($b : String)))
          let bArgs : Array (TSyntax `term) := args.map (fun (i, _) =>
            ⟨(mkIdent (Name.mkSimple (Triptych.surfaceBinder i.getId.toString))).raw⟩)
          let valIdent := mkIdentFrom name (name.getId ++ `value)
          emitSpec (← `(def $valIdent $tBinders* := $f $bArgs*))
          valueCaps := capArgs.map (·.1)
          valueCapArgs := capArgs
        | _ => throwUnsupportedSyntax
      if grammarStaticallyUnique && (veIdent?.isSome || hasValueEsc) then
        let coherentId := mkIdentFrom name (name.getId ++ `grammarValueCoherent)
        let functionalId := mkIdentFrom name (name.getId ++ `grammarCaptureFunctional)
        let vfnIdent := mkIdentFrom name (name.getId ++ `valueFn)
        if veIdent?.isSome then
          emitSound (←
            `(theorem $coherentId :
                GrammarValueCoherent $grammarIdent
                  (fun m : CaptureMap => $vfnIdent m.toEnv) :=
                GrammarValueCoherent.of_captureFunctional $grammarIdent
                  (fun m : CaptureMap => $vfnIdent m.toEnv) $functionalId))
        else
          emitSound (←
            `(theorem $coherentId :
                GrammarValueCoherent $grammarIdent $vfnIdent :=
                GrammarValueCoherent.of_captureFunctional $grammarIdent $vfnIdent
                  $functionalId))
      -- Constraints (optional): constraint-DSL predicates, one per line, with `value`
      -- substituted by the value expression. The `fmtConstraints` node is
      -- `"constraints" (colGt constraintExpr)+`; arg 1 is the plain array of exprs.
      -- Always bind `<Name>.constraints` (empty list if the section is absent) so the
      -- bundled predicates below can reference it uniformly.
      let cIdent := mkIdentFrom name (name.getId ++ `constraints)
      -- `constraints'` escape entries (`cse`): each is a raw `f X [Y] …`; every capture carries
      -- its list flag so mixed scalar/collection predicates retain their source types.
      let escEntries :
          Array (TSyntax `ident × Array (TSyntax `ident × Bool)) ← match cse with
        | some cseStx =>
          let lines : Array (TSyntax `fmtEscEntry) := cseStx.raw[1].getArgs.map (⟨·⟩)
          lines.mapM parseEscEntryArgs
        | none => pure #[]
      for (_, args) in escEntries do
        for (i, isList) in args do
          if isList && !repeatedCaptures.contains i.getId.toString then
            throwErrorAt i m!"list argument `[{i.getId}]` does not name a repeated item. \
              Declare `rep {i.getId} sepBy \"...\" <len>` before reading all of its spans."
      let hasOpaque := !escEntries.isEmpty
      -- DSL constraint exprs (may be empty even when `constraints'` is present).
      let dslExprs : Array (TSyntax `constraintExpr) := match cs with
        | some csStx => csStx.raw[1].getArgs.map (⟨·⟩)
        | none       => #[]
      for e in dslExprs do
        for i in captureIdents e.raw do
          unless i.getId == `value do
            validateCaptureIdent i
        validateCounts e.raw (Triptych.constraintCountCaptures e)
      -- The authoritative phase split is whether the ORIGINAL surface expression mentions the
      -- final `value` keyword. Capture arithmetic such as `nat MM ∈ [1, 12]` remains format
      -- well-formedness. This must happen before elaboration substitutes `valueExpr` for `value`.
      let wfExprs := dslExprs.filter (fun e => !(Triptych.constraintUsesValue e))
      let valueExprs := dslExprs.filter Triptych.constraintUsesValue
      if cs.isSome || cse.isSome then
        -- ENGINE list: every entry carries its preserved phase. A `constraints'` escape is
        -- intrinsically a well-formedness constraint and receives the complete capture map.
        let dslTerms ← dslExprs.mapM (fun e => liftMacroM (elabEntryWith valueSub e))
        let escTerms ← escEntries.mapM (fun (f, is) => do
          `(ConstraintEntry.opaqueMap ConstraintPhase.wellFormed
              $(← liftMacroM (Triptych.opaqueMapClosure f is))))
        let csep : Syntax.TSepArray `term "," := .ofElems (dslTerms ++ escTerms)
        emitEngine (← `(def $cIdent : List ConstraintEntry := [$csep,*]))
        -- A final `value` reference renders readably as `<Name>.value <components>`.
        let valSubR : Option (TSyntax `term) ← match veIdent? with
          | some _ =>
            let vId := mkIdentFrom name (name.getId ++ `value)
            let vArgs : Array (TSyntax `term) :=
              (valueCaps.map (fun c => ⟨(mkIdent (Name.mkSimple (Triptych.surfaceBinder c))).raw⟩)).toArray
            pure (some (← `($vId $vArgs*)))
          | none   => pure none
        let wfRTerms ← wfExprs.mapM (fun e => liftMacroM (elabConstraintReadable valSubR e))
        let valueRTerms ← valueExprs.mapM (fun e => liftMacroM (elabConstraintReadable valSubR e))
        let escRTerms ← escEntries.mapM (fun (f, is) => do
          let bArgs : Array (TSyntax `term) := is.map (fun (i, _) =>
            ⟨(mkIdent (Name.mkSimple (Triptych.surfaceBinder i.getId.toString))).raw⟩)
          `($f $bArgs* = true))
        let escCaps := escEntries.toList.flatMap (fun (_, is) =>
          is.toList.map (fun (i, isList) => (i.getId.toString, isList)))
        let wfCaps :=
          ((wfExprs.toList.flatMap Triptych.constraintCaptures).map (·, false) ++ escCaps)
            |>.eraseDups
        let valCaps :=
          (valueExprs.toList.flatMap Triptych.constraintCaptures ++ valueCaps).eraseDups
            |>.map (·, false)
        let constraintLoc := match cs, cse with
          | some constraintsSection, _ => constraintsSection.raw
          | _, some constraintsSection => constraintsSection.raw
          | _, _ => name.raw
        validateSurfaceBinders constraintLoc "the well-formedness constraint function"
          (wfCaps.map (·.1)) true
        validateSurfaceBinders constraintLoc "the value constraint function" (valCaps.map (·.1))
        unless wfRTerms.isEmpty && escRTerms.isEmpty do
          let wfBody ← match (wfRTerms ++ escRTerms).toList with
            | []      => `(True)
            | x :: xs => xs.foldlM (fun acc p => `($acc ∧ $p)) x
          let wfBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) ←
            wfCaps.toArray.mapM (fun (c, isList) => do
              let b := mkIdent (Name.mkSimple (Triptych.surfaceBinder c))
              if isList then `(bracketedBinder| ($b : List String))
              else `(bracketedBinder| ($b : String)))
          let wfRIdent := mkIdentFrom name (name.getId ++ `WfConstraints)
          emitSpec (← `(def $wfRIdent $wfBinders* : Prop := $wfBody))
          wfConstrCaps := some wfCaps
        unless valueRTerms.isEmpty do
          let valueBody ← match valueRTerms.toList with
            | []      => `(True)
            | x :: xs => xs.foldlM (fun acc p => `($acc ∧ $p)) x
          let valueBinders : Array (TSyntax `ident) :=
            (valCaps.map (fun c => mkIdent (Name.mkSimple (Triptych.surfaceBinder c.1)))).toArray
          let cRIdent := mkIdentFrom name (name.getId ++ `Constraints)
          emitSpec (← `(def $cRIdent $[($valueBinders : String)]* : Prop := $valueBody))
          valueConstrCaps := some valCaps
      else
        emitEngine (← `(def $cIdent : List ConstraintEntry := []))
      -- The engine predicates remain the generic applications
      -- `Triptych.isWf grammar constraints` and `Triptych.satisfiesConstraints grammar
      -- constraints`; no format-specific lowercase aliases are added to the public API.
      -- The capitalized readable predicates are proved equivalent to these interpreter
      -- expressions below.
      if let some veIdent := veIdent? then
        -- DSL tier: `computeValue` via the analyzable `ValExpr` (Int-valued).
        let cvIdent := mkIdentFrom name (name.getId ++ `computeValue)
        emitEngine (← `(def $cvIdent (s : String) : Option Int :=
                      Triptych.computeValue $grammarIdent $veIdent s))
      else if hasValueEsc then
        -- ESCAPE tier: `computeValue` via `computeValueMap` and the author's `valueFn` (a
        -- `CaptureMap → α`). The value type is arbitrary (inferred from `valueFn`), so this
        -- parses to whatever structured value `value'` produces (`Option SimpleGraph`, `Option
        -- IPNet`, …). `computeValueMap` (not `computeValueF`) hands `valueFn` the full
        -- `CaptureMap`, so a `[X]` list arg can read every repeated span via `toEnvList`.
        let cvIdent := mkIdentFrom name (name.getId ++ `computeValue)
        let vfnIdent := mkIdentFrom name (name.getId ++ `valueFn)
        emitEngine (← `(def $cvIdent (s : String) :=
                      Triptych.computeValueMap $grammarIdent $vfnIdent s))
      -- SPEC bundle (capitalized): `IsWf.<start>` remains the per-production grammar layout.
      -- Top-level `IsWf` adds every capture-only format constraint; only constraints that
      -- explicitly mention the final `value` remain in `SatisfiesConstraints`.
      let startName : Name := (gval.prods.head?.map (·.name.toName)).getD name.getId
      let grammarWf := mkIdentFrom name (name.getId ++ `IsWf ++ startName)
      let wfScSurf := mkIdentFrom name (name.getId ++ `SatisfiesWfConstraints)
      let wfSurf := mkIdentFrom name (name.getId ++ `IsWf)
      let scSurf := mkIdentFrom name (name.getId ++ `SatisfiesConstraints)
      let accSurf := mkIdentFrom name (name.getId ++ `IsValid)
      match wfConstrCaps with
      | none =>
        emitSpec (← `(abbrev $wfSurf (s : String) : Prop := $grammarWf s))
      | some caps =>
        let wfRIdent := mkIdentFrom name (name.getId ++ `WfConstraints)
        let args : Array (TSyntax `term) ← caps.toArray.mapM (fun (c, isList) =>
          if isList then `(Triptych.componentList $grammarIdent s $(Syntax.mkStrLit c))
          else `(Triptych.component $grammarIdent s $(Syntax.mkStrLit c)))
        emitSpec (← `(def $wfScSurf (s : String) : Prop := $wfRIdent $args*))
        emitSpec (← `(abbrev $wfSurf (s : String) : Prop := $grammarWf s ∧ $wfScSurf s))
      match valueConstrCaps with
      | none =>
        emitSpec (← `(abbrev $accSurf (s : String) : Prop := $wfSurf s))
      | some caps =>
        let cRIdent := mkIdentFrom name (name.getId ++ `Constraints)
        let args : Array (TSyntax `term) ← caps.toArray.mapM (fun (c, _) =>
          `(Triptych.component $grammarIdent s $(Syntax.mkStrLit c)))
        emitSpec (← `(def $scSurf (s : String) : Prop := $cRIdent $args*))
        emitSpec (← `(abbrev $accSurf (s : String) : Prop := $wfSurf s ∧ $scSurf s))
      let hasGeneratedValue := veIdent?.isSome || hasValueEsc
      let resolvedValueCaps : List (String × Bool) :=
        if veIdent?.isSome then valueCaps.map (·, false) else valueCapArgs
      let viewCaps :=
        resolvedValueCaps ++
          wfConstrCaps.getD [] ++ valueConstrCaps.getD []
      let viewFields := Triptych.viewFieldSpecs gval viewCaps
      if hasGeneratedValue || wfConstrCaps.isSome || valueConstrCaps.isSome then
        emitSpec (← Triptych.viewStructureCommand name.getId viewFields)
        for cmd in ←
            Triptych.viewSurfaceCommands name.getId viewFields
              (wfConstrCaps.getD []) (valueConstrCaps.getD [])
              resolvedValueCaps hasGeneratedValue do
          emitSpec cmd
        for cmd in ← Triptych.viewEngineCommands name.getId grammarIdent viewFields do
          emitEngine cmd
        if let some cmd ← Triptych.derivationViewCommand name.getId gval then
          emitEngine cmd
        emitSound (← Triptych.decodeViewInputProof name.getId)
        for cmd in ←
            Triptych.derivationViewProofCommands
              name.getId grammarIdent gval grammarStaticallyUnique do
          emitSound cmd
      if let some caps := wfConstrCaps then
        emitSound (←
          Triptych.constraintsOfDecodeProof name.getId grammarIdent caps true)
      if let some caps := valueConstrCaps then
        emitSound (←
          Triptych.constraintsOfDecodeProof name.getId grammarIdent caps false)
      -- Reconcile both public phases independently, then derive full acceptance equivalence.
      emitReconcile wfConstrCaps.isSome valueConstrCaps.isSome veIdent?.isSome
      if hasGeneratedValue || wfConstrCaps.isSome || valueConstrCaps.isSome then
        if wfConstrCaps.isSome then
          emitSound (←
            Triptych.viewConstraintsOfDecodeProof name.getId grammarIdent true)
        if valueConstrCaps.isSome then
          emitSound (←
            Triptych.viewConstraintsOfDecodeProof name.getId grammarIdent false)
        emitSound (←
          Triptych.isValidViewProof name.getId grammarIdent
            wfConstrCaps.isSome valueConstrCaps.isSome)
      -- VALUE equivalence (SOUNDNESS section): surface `value` ⟺ engine `computeValue`, as a
      -- standalone theorem (the value analogue of `IsWf_equiv`). Emitted whenever a value
      -- section is present — DSL tier (`veIdent?`) or `value'` escape (`hasValueEsc`).
      if veIdent?.isSome || hasValueEsc then
        -- Caps with list flags: DSL tier is all-scalar; the escape tier carries `[X]` flags.
        emitSound (←
          Triptych.computeValueEqProof name.getId grammarIdent
            resolvedValueCaps veIdent?.isSome)
        emitSound (←
          Triptych.computeValueOfDecodeProof name.getId grammarIdent resolvedValueCaps)
        emitSound (← Triptych.computeValueViewProof name.getId grammarIdent)
      -- GENERATED VERIFIED PARSER (→ parser file): whenever a value section exists, emit the
      -- tool's own `<Name>.parse` and its three AUTO-DISCHARGED contracts (`parse_sound`/
      -- `parse_complete`/`parse_reject`). Its public gate is the readable `<Name>.IsValid`;
      -- the generated `DecidablePred` instance executes that predicate through the independently
      -- proved interpreter equivalence. This is the correct-by-construction parser; the external
      -- obligations below are the SEPARATE translation-validation surface. An `ofSpec <f>`
      -- clause converts the output to the domain type `δ` (so `parse : String → Option δ`);
      -- otherwise it returns `β`.
      let (ofSpecTerm?, valueToSpecTerm?) :
          Option (TSyntax `term) × Option (TSyntax `term) ←
        match v with
        | some vStx =>
          match vStx with
          | `(fmtValue| value $_:valExpr ofSpec $ofSpecT:term toSpec $toSpecT:term) =>
            pure (some ofSpecT, some toSpecT)
          | `(fmtValue| value $_:valExpr ofSpec $ofSpecT:term) =>
            pure (some ofSpecT, none)
          | `(fmtValue| value $_:valExpr toSpec $toSpecT:term) =>
            pure (none, some toSpecT)
          | `(fmtValue| value $_:valExpr) =>
            pure (none, none)
          | _ => throwUnsupportedSyntax
        | none => pure (none, none)
      let escapeToSpecTerm? : Option (TSyntax `term) ←
        match ve with
        | some veStx =>
          match veStx with
          | `(fmtValueEsc| value' $_:fmtEscEntry toSpec $toSpecT:term) =>
            pure (some toSpecT)
          | `(fmtValueEsc| value' $_:fmtEscEntry) =>
            pure none
          | _ => throwUnsupportedSyntax
        | none => pure none
      let toSpecTerm? := valueToSpecTerm?.orElse fun _ => escapeToSpecTerm?
      if veIdent?.isSome || hasValueEsc then
        for cmd in ← Triptych.parserContractsProof name.getId veIdent?.isSome ofSpecTerm? do
          emitParser cmd
        emitParser (← Triptych.parseViewProof name.getId ofSpecTerm?)
        emitParser (← Triptych.parseEqSomeIffViewProof name.getId ofSpecTerm?)
        emitParser (← Triptych.parseEqNoneIffViewProof name.getId)
        if grammarStaticallyUnique then
          emitParser (←
            Triptych.relationalParserContractProof name.getId veIdent?.isSome ofSpecTerm?)
      -- CONVERSION GUARD (lint): an `ofSpec` not injective on all of `Int` (e.g.
      -- `Int64.ofInt`, which WRAPS) needs a value constraint carving the accepted language down
      -- to its faithful domain. Otherwise out-of-range inputs are accepted and silently wrap.
      -- The generated `toSpec_ofSpec` obligation catches this when `toSpec` is present.
      -- We cannot inspect the supplied function
      -- (an opaque term), so this is a heuristic WARNING, not an error: no DSL constraint
      -- mentions `value` and no `constraints'` escape is present ⟹ warn. A total injection
      -- (a plain embedding) legitimately needs no constraint — then ignore the warning.
      if let some ofSpecT := ofSpecTerm? then
        unless dslExprs.any Triptych.constraintUsesValue do
          logWarningAt ofSpecT m!"`ofSpec` without a value constraint: if `{ofSpecT}` is not \
            injective on \
            all of Int (e.g. it wraps, like `Int64.ofInt`), out-of-range inputs will be ACCEPTED \
            and silently converted by the generated parser. Add a range constraint matching \
            `ofSpec`'s faithful domain (e.g. `value ∈ [Int64.MIN, Int64.MAX]`) — with a \
            companion `toSpec` clause the emitted `toSpec_ofSpec` obligation is unprovable \
            without it. If `ofSpec` is a total embedding, this warning can be ignored."
      -- CONVERSION FAITHFULNESS (→ soundness file, generated section): with BOTH `ofSpec` and a
      -- `toSpec` clause, emit `toSpec_ofSpec : IsValid s →
      -- computeValue s = some v → toSpec (ofSpec v) = v` on accepted values. The companion
      -- When a printer is present, its `encode_view` witness derives the companion
      -- `ofSpec_toSpec` law below. This proof is what the value range constraint provides, so a
      -- missing/too-loose constraint makes it UNPROVABLE —
      -- the silent-wrap trap surfaces as a permanent `sorry` instead of wrong behavior. Payoff
      -- (discharged): `parse_sound_toSpec`, soundness of the generated domain-valued parser —
      -- the same contract shape as the external `extparse_sound`.
      if let some ofSpecT := ofSpecTerm? then
        if let some toSpecT := toSpecTerm? then
          let toSpecOfSpecId := mkIdentFrom name (name.getId ++ `toSpec_ofSpec)
          let soundToSpecId := mkIdentFrom name (name.getId ++ `parse_sound_toSpec)
          let validSurf   := mkIdentFrom name (name.getId ++ `IsValid)
          let cvIdent     := mkIdentFrom name (name.getId ++ `computeValue)
          let parseId     := mkIdentFrom name (name.getId ++ `parse)
          let (dTy, dNm) ← Triptych.ofSpecCodomainBinder ofSpecT
          let dId := mkIdent dNm
          emitContractGen (← `(theorem $toSpecOfSpecId (s : String) (v : Int) :
              $validSurf s → $cvIdent s = some v →
                $toSpecT ($ofSpecT v) = v := by sorry))
          emitContractGen (← `(theorem $soundToSpecId (s : String) ($dId : $dTy) :
              $parseId s = some $dId →
                $validSurf s ∧ $cvIdent s = some ($toSpecT $dId) :=
            Triptych.gatedParseOfSpec_sound_toSpec
              $validSurf $cvIdent $ofSpecT $toSpecT $toSpecOfSpecId s $dId))
      -- EXTERNAL-PARSER obligations (→ soundness file): with a `parser <p>`
      -- clause naming an EXISTING external parser, emit `<Name>.sound`/`.complete`/`.reject` as
      -- `sorry`d theorems (design §16.1), stated over the SURFACE `<Name>.IsValid`/
      -- `computeValue` — the human-facing "the real parser accepts iff the readable spec is
      -- valid, with matching value". These are the ONLY obligations left to the human; they
      -- reference the external parser, so the soundness file re-imports the caller module.
      if let some prStx := pr then
        if let `(fmtParser| parser $parseT:term) := prStx then
          let toSpecT ←
            match toSpecTerm? with
            | some toSpecT => pure toSpecT
            | none => `(id)
          let cvIdent := mkIdentFrom name (name.getId ++ `computeValue)
          let checkedExternalAvailable ←
            if veIdent?.isSome || hasValueEsc then
              Triptych.hasDecidableEqOptionPayload cvIdent
            else
              pure false
          -- Universal soundness fallback: check each external success against the generated
          -- parser. Unlike the static obligations below, this wrapper and all of its theorems
          -- are discharged without inspecting or trusting the external implementation.
          if veIdent?.isSome || hasValueEsc then
            if checkedExternalAvailable then
              for cmd in ←
                  Triptych.checkedExternalParserProofs name.getId parseT toSpecT do
                emitParser cmd
            else
              logWarningAt toSpecT m!"checked external-parser wrapper not emitted: the codomain \
                of `{toSpecT}` has no `DecidableEq` instance. Static `extparse_*` obligations \
                are still emitted. Add `DecidableEq` for the spec value type to enable \
                runtime soundness-by-checking."
          -- Statements written OUT (not `RejectStmt`/`SoundStmt`/…), so the obligation reads as
          -- the actual proposition to prove for the external parser `parseT`.
          let rejIdent := mkIdentFrom name (name.getId ++ `extparse_reject)
          emitContractExt (← `(theorem $rejIdent (s : String) :
              $parseT s = none ↔ ¬ $accSurf s := by sorry))
          if hasGeneratedValue || wfConstrCaps.isSome || valueConstrCaps.isSome then
            emitContractExt (← Triptych.externalParseEqNoneIffViewProof name.getId parseT)
          -- Concrete type + one-letter binder from the EXTERNAL parser's `Option` payload
          -- (e.g. Cedar `Decimal` → `d`); reused by both obligations and the printer theorems.
          let (extTy, extNm) ← Triptych.optionPayloadBinder parseT
          let extId := mkIdent extNm
          let compIdent  := mkIdentFrom name (name.getId ++ `extparse_complete)
          -- `sound`/`complete` need a value function — emitted whenever a `value` OR `value'`
          -- section is present (both produce `<Name>.computeValue`; the escape tier's value
          -- type is arbitrary, matched by the `toSpec` codomain).
          if veIdent?.isSome || hasValueEsc then
            let soundIdent := mkIdentFrom name (name.getId ++ `extparse_sound)
            -- Both obligations parametrized over the external output `extId` (matching Cedar's
            -- target-parametrized `parse_sound`/`parse_complete`).
            emitContractExt (← `(theorem $soundIdent (s : String) ($extId : $extTy) :
                $parseT s = some $extId →
                  $accSurf s ∧ $cvIdent s = some ($toSpecT $extId) := by sorry))
            if checkedExternalAvailable then
              let checkedId := mkIdentFrom name (name.getId ++ `checkedExtParse)
              let checkedEqId :=
                mkIdentFrom name (name.getId ++ `checkedExtParse_eq_extparse)
              emitContractExt (← `(theorem $checkedEqId :
                  $checkedId = $parseT :=
                Triptych.checkedExternalParse_eq_of_sound
                  $accSurf $cvIdent $parseT $toSpecT $soundIdent))
            emitContractExt (← `(theorem $compIdent (s : String) ($extId : $extTy) :
                $accSurf s → $cvIdent s = some ($toSpecT $extId) →
                  $parseT s = some $extId := by sorry))
            emitContractExt (←
              Triptych.externalParseEqSomeIffViewProof name.getId parseT toSpecT)
      -- PRINTER: `printer auto` synthesizes a certified serializer for a supported analyzable
      -- `value`; `printer <toStr>` names one explicitly. The explicit route leaves one typed-view
      -- obligation in soundness. The automatic route emits the same witness into parser.lean.
      --
      -- The older `encode_accepted` / `encode_value` names are derived from the same witness for
      -- compatibility and for the optional EXTERNAL parser's completeness theorem. With
      -- `ofSpec` + `toSpec`, the accepted-value `toSpec_ofSpec` law also derives
      -- `ofSpec_toSpec`; it is not a second printer obligation. Injectivity and normalization
      -- follow from roundtrip for both parsers. Needs a value section.
      if let some ppStx := pp then
        let (toStrT, printerIsAuto) : TSyntax `term × Bool ←
          match ppStx with
          | `(fmtPrinter| printer auto) => do
              unless veIdent?.isSome && !hasValueEsc do
                throwErrorAt ppStx "`printer auto` requires an analyzable `value` section; \
                  an opaque `value'` function needs an explicit `printer` or \
                  `DerivationPrinter` certificate"
              if ofSpecTerm?.isSome then
                throwErrorAt ppStx "`printer auto` does not yet synthesize through `ofSpec`; \
                  use an explicit `printer` until the domain conversion supplies a proved \
                  inverse"
              if cs.isSome || cse.isSome then
                throwErrorAt ppStx "`printer auto` does not yet synthesize a total printer for \
                  constrained value domains; use an explicit `printer`"
              unless grammarStaticallyUnique do
                throwErrorAt ppStx "`printer auto` requires a statically capture-functional \
                  grammar"
              let some vStx := v
                | throwErrorAt ppStx "`printer auto` requires a `value` section"
              let valueExpr : TSyntax `valExpr := ⟨vStx.raw[1]⟩
              let some (signCapture, digitsCapture) :=
                  signedIntegerValueCaptures? valueExpr
                | throwErrorAt ppStx "`printer auto` currently supports the total signed-decimal \
                    patterns `value Sign * nat Digits` and `value nat Digits * Sign`"
              unless signCaptures.contains signCapture do
                throwErrorAt ppStx m!"automatic signed-decimal printing expected \
                  `{signCapture} ::= sign`"
              let some shape :=
                  signedIntegerPrinterShape? gval signCapture digitsCapture
                | throwErrorAt ppStx m!"automatic signed-decimal printing requires the start \
                    production to be exactly `{signCapture} {digitsCapture}`, with \
                    `{signCapture} ::= sign` and `{digitsCapture} ::= digit+`"
              for cmd in ← signedIntegerPrinterCommands name.getId shape do
                emitParser cmd
              let toStringId := mkIdentFrom name (name.getId ++ `toString)
              pure (⟨toStringId.raw⟩, true)
          | `(fmtPrinter| printer $explicit:term) =>
              pure (explicit, false)
          | _ => throwUnsupportedSyntax
        if veIdent?.isSome || hasValueEsc then
            let emitGeneratedPrinter (cmd : TSyntax `command) : CommandElabM Unit :=
              if printerIsAuto then emitParser cmd else emitContractGen cmd
            let cvIdent := mkIdentFrom name (name.getId ++ `computeValue)
            let encodeViewId := mkIdentFrom name (name.getId ++ `encode_view)
            let encAccId := mkIdentFrom name (name.getId ++ `encode_accepted)
            let encValId := mkIdentFrom name (name.getId ++ `encode_value)
            let ofSpecToSpecId := mkIdentFrom name (name.getId ++ `ofSpec_toSpec)
            let validSurf := mkIdentFrom name (name.getId ++ `IsValid)
            let validViewId := mkIdentFrom name (name.getId ++ `IsValid_view)
            let viewId := mkIdentFrom name (name.getId ++ `View)
            let viewValidId := mkIdentFrom name (name.getId ++ `View ++ `Valid)
            let decodeViewId := mkIdentFrom name (name.getId ++ `decodeView)
            let denotationId := mkIdentFrom name (name.getId ++ `View ++ `denotation)
            let computeValueViewId := mkIdentFrom name (name.getId ++ `computeValue_view)
            let computeValueViewRw ←
              `(Lean.Parser.Tactic.rwRule| $computeValueViewId:ident)
            let parseEqSomeViewId :=
              mkIdentFrom name (name.getId ++ `parse_eq_some_iff_view)
            -- The serializer's domain is the generated parser's result type: δ with `ofSpec`,
            -- β otherwise. Read it (+ a one-letter binder) straight off `toStr`.
            let (dTy, dNm) ← Triptych.serializerDomainBinder toStrT
            let dId := mkIdent dNm; let dId' := mkIdent (dNm.appendAfter "'")
            let parseId  := mkIdentFrom name (name.getId ++ `parse)
            let rtId     := mkIdentFrom name (name.getId ++ `parse_toString_roundtrip)
            let injId    := mkIdentFrom name (name.getId ++ `toString_injective)
            let normId   := mkIdentFrom name (name.getId ++ `normalize_eq_iff_parse_eq)
            -- An external parser is optional. The semantic `toSpec` conversion comes from the
            -- value section and remains available to generated-printer laws without one.
            let extParser? : Option (TSyntax `term) := do
              let prStx ← pr
              match prStx with
              | `(fmtParser| parser $parseT:term) => some parseT
              | _ => none
            -- The sole printer-specific obligation: produce the exact valid view built by the
            -- serializer. `ofSpec` is part of the denotation when the parser returns a
            -- domain type.
            unless printerIsAuto do
              match ofSpecTerm? with
              | some ofSpecT =>
                emitContractGen (← `(theorem $encodeViewId ($dId : $dTy) :
                    ∃ v : $viewId,
                      $decodeViewId ($toStrT $dId) = some v ∧
                      $viewValidId v ∧
                      $ofSpecT ($denotationId v) = $dId := by sorry))
              | none =>
                emitContractGen (← `(theorem $encodeViewId ($dId : $dTy) :
                    ∃ v : $viewId,
                      $decodeViewId ($toStrT $dId) = some v ∧
                      $viewValidId v ∧
                      $denotationId v = $dId := by sorry))
            -- Acceptance is a projection of the valid-view witness, retained under its old name.
            emitGeneratedPrinter (← `(theorem $encAccId ($dId : $dTy) :
                $validSurf ($toStrT $dId) := by
              obtain ⟨v, hview, hvalidView, _⟩ := $encodeViewId $dId
              exact ($validViewId ($toStrT $dId)).mpr ⟨v, hview, hvalidView⟩))
            -- Derive the old value/conversion names from the same view, then expose roundtrip.
            match ofSpecTerm?, toSpecTerm? with
            | some ofSpecT, some toSpecT =>
              let toSpecOfSpecId := mkIdentFrom name (name.getId ++ `toSpec_ofSpec)
              emitGeneratedPrinter (← `(theorem $encValId ($dId : $dTy) :
                  $cvIdent ($toStrT $dId) = some ($toSpecT $dId) := by
                obtain ⟨v, hview, _, hresult⟩ := $encodeViewId $dId
                have hvalue :
                    $cvIdent ($toStrT $dId) = some ($denotationId v) := by
                  rw [$computeValueViewRw, hview]
                  rfl
                have hinverse :=
                  $toSpecOfSpecId
                    ($toStrT $dId) ($denotationId v) ($encAccId $dId) hvalue
                rw [hresult] at hinverse
                rw [hvalue]
                exact congrArg some hinverse.symm))
              emitGeneratedPrinter (← `(theorem $ofSpecToSpecId ($dId : $dTy) :
                  $ofSpecT ($toSpecT $dId) = $dId := by
                obtain ⟨v, hview, _, hresult⟩ := $encodeViewId $dId
                have hvalue :
                    $cvIdent ($toStrT $dId) = some ($denotationId v) := by
                  rw [$computeValueViewRw, hview]
                  rfl
                have hinverse :=
                  $toSpecOfSpecId
                    ($toStrT $dId) ($denotationId v) ($encAccId $dId) hvalue
                rw [hresult] at hinverse
                rw [hinverse, hresult]))
            | some ofSpecT, none =>
              emitGeneratedPrinter (← `(theorem $encValId ($dId : $dTy) :
                  ($cvIdent ($toStrT $dId)).map $ofSpecT = some $dId := by
                obtain ⟨v, hview, _, hresult⟩ := $encodeViewId $dId
                rw [$computeValueViewRw, hview]
                simpa using congrArg some hresult))
            | none, _ =>
              emitGeneratedPrinter (← `(theorem $encValId ($dId : $dTy) :
                  $cvIdent ($toStrT $dId) = some $dId := by
                obtain ⟨v, hview, _, hresult⟩ := $encodeViewId $dId
                rw [$computeValueViewRw, hview]
                exact congrArg some hresult))
            emitGeneratedPrinter (← `(theorem $rtId ($dId : $dTy) :
                $parseId ($toStrT $dId) = some $dId :=
              Triptych.parse_toString_roundtrip_of_encodeView
                $parseEqSomeViewId $encodeViewId $dId))
            emitGeneratedPrinter (←
              `(theorem $injId ($dId $dId' : $dTy)
                  (h : $toStrT $dId = $toStrT $dId') :
                $dId = $dId' :=
              Triptych.toString_injective $rtId $dId $dId' h))
            emitGeneratedPrinter (← `(theorem $normId (s s' : String) :
                ($parseId s).map $toStrT = ($parseId s').map $toStrT ↔
                  $parseId s = $parseId s' :=
              Triptych.normalize_eq_iff_parse_eq $rtId s s'))
            -- EXTERNAL parser (δ-view), when a `parser` clause exists: reuses the SAME `toStr` +
            -- `encode_accepted`/`encode_value` (`toSpec` view), closing roundtrip via the external
            -- `complete` — exactly Cedar's `parse_toString_roundtrip = parse_complete …`.
            match extParser? with
            | some parseT =>
              let xCompId  := mkIdentFrom name (name.getId ++ `extparse_complete)
              let xRtId    := mkIdentFrom name (name.getId ++ `extparse_toString_roundtrip)
              let xInjId   := mkIdentFrom name (name.getId ++ `extparse_toString_injective)
              let xNormId :=
                mkIdentFrom name (name.getId ++ `extparse_normalize_eq_iff_parse_eq)
              emitContractExt (←
                `(theorem $xRtId ($dId : $dTy) :
                    $parseT ($toStrT $dId) = some $dId :=
                Triptych.parse_toString_roundtrip $xCompId $encAccId $encValId $dId))
              emitContractExt (←
                `(theorem $xInjId ($dId $dId' : $dTy)
                    (h : $toStrT $dId = $toStrT $dId') :
                  $dId = $dId' :=
                Triptych.toString_injective $xRtId $dId $dId' h))
              emitContractExt (← `(theorem $xNormId (s s' : String) :
                  ($parseT s).map $toStrT = ($parseT s').map $toStrT ↔
                    $parseT s = $parseT s' :=
                Triptych.normalize_eq_iff_parse_eq $xRtId s s'))
            | none => pure ()
      -- WRITE (optional `to "<dir>"` clause): emit up to THREE generated modules into
      -- `<dir>` (default `.`, must pre-exist), split by audience:
      --   `spec.lean`     — the readable surface (cite): grammar, `IsWf.*`, `value`,
      --                     `Constraints`, `SatisfiesConstraints`, `IsValid`. Proof-free.
      --   `parser.lean`   — the runnable + trusted artifact (run + trust): the engine bundle,
      --                     ALL auto-discharged proofs (`IsWf_equiv`, `computeValue_eq`,
      --                     decidability), and the generated verified `parse` + its contracts.
      --                     Imports `spec`. No `sorry`.
      --   `soundness.lean`— printer/external-parser obligations (`sorry`d), emitted when either
      --                     clause is present. Imports `parser` + the caller module.
      --                     WRITE-ONCE: holds user proofs, never overwritten once it exists.
      -- Splitting by file (vs the old single module) gives each a crisp contract; the
      -- dependency chain spec ← parser ← soundness is acyclic.
      if let some toStx := to? then
        if let `(fmtTo| to $dirStx:str) := toStx then
          let nm := name.getId.toString
          let dir := dirStx.getString
          let specDecls ← bufS.get; let engineDecls ← bufE.get
          let proofDecls ← bufP.get; let parserDecls ← bufR.get
          let genContractDecls ← bufCg.get; let extContractDecls ← bufCx.get
          let contractDecls := genContractDecls ++ extContractDecls
          -- Module path prefix of the output dir (`Triptych/Examples/Decimal` →
          -- `Triptych.Examples.Decimal`), used to import sibling generated files.
          let dirMod := (dir.replace "/" ".").replace "\\" "."
          let callerImport ← callerModuleForOutput
          let callerNamespace := (← getCurrNamespace).toString
          let specMod   := dirMod ++ ".spec"
          let parserMod := dirMod ++ ".parser"
          -- The surface `value`/`Constraints` reference caller fns for the escape tiers
          -- (`toGraph`, `dayBound`, …); the engine bundle likewise. So both `spec` and
          -- `parser` import (and `open`) the caller when an escape is present.
          let needsCallerSurface := hasOpaque || hasValueEsc
          -- `parser.lean` additionally embeds the `ofSpec` term in the generated `parse`; when it
          -- is caller-defined (e.g. `millisToDuration`, not a library fn like `Int64.ofInt`)
          -- it must import+open the caller too. Presence of `ofSpec` is the trigger (a library fn
          -- makes the extra import harmless — the caller module is acyclic w.r.t. the generated
          -- files, same as `soundness.lean`'s caller import).
          let needsCallerParser := needsCallerSurface || ofSpecTerm?.isSome
          -- `unusedSimpArgs`/`unusedVariables` off — uniform generated proof closers
          -- intentionally over-provision some simp lemmas and binders.
          let mkHeader (imports : List String) (openCaller : Bool) : String :=
            let importLines := String.join (imports.map (fun i => s!"import {i}\n"))
            s!"/- Generated by Triptych from `triptych {nm}`. -/\n\n\
               {importLines}\
               \nopen Triptych\n\
               {if openCaller then s!"open {callerNamespace}\n" else ""}\
               \nset_option linter.unusedSimpArgs false\n\
               set_option linter.unusedVariables false\n"
          let libImports := ["Triptych.Architecture.Denote", "Triptych.Architecture.Derivation",
            "Triptych.Architecture.Value",
            "Triptych.Architecture.Constraint", "Triptych.Architecture.Assemble",
            "Triptych.Theorems.Reconcile", "Triptych.Theorems.Value"]
          let joinDecls (decls : Array String) : String :=
            String.intercalate "\n\n" decls.toList
          -- OVERWRITE GUARD: spec/parser are regenerated every elaboration, which is safe ONLY
          -- for files this tool wrote. Every generated file opens with the sentinel header
          -- below; a pre-existing file WITHOUT it is not ours (a hand-written module, or a
          -- mistyped `to` dir landing on someone else's spec.lean) → hard error, never clobber.
          -- (An interactive y/n is not possible here: elaboration runs headless under `lake`
          -- and the LSP, so the sentinel stands in for "the user already consented" — by
          -- having let the tool create the file in the first place.)
          let sentinel := "/- Generated by Triptych"
          let guardedWrite (path : String) (contents : String) : CommandElabM Unit := do
            if ← System.FilePath.pathExists path then
              let firstLine := ((← IO.FS.readFile path).splitOn "\n").headD ""
              unless firstLine.startsWith sentinel do
                throwError "Triptych: refusing to overwrite {path} — it was not generated by \
                  this tool (missing the `{sentinel} …` header). Move or delete it, or point the \
                  `to \"<dir>\"` clause elsewhere."
            IO.FS.writeFile path contents
          -- ── spec.lean ── the readable surface only.
          let specHeader := mkHeader
            (libImports ++ (if needsCallerSurface then [callerImport] else []))
            needsCallerSurface
          let specBanner := "/- ═══════════════════════════════ spec ═══════════════════════════════\n\
            The more readable specification. Each production of the input grammar becomes an\n\
            inlined well-formedness predicate `IsWf.*` written as a plain existential over the\n\
            named captures, so you can read it side-by-side with the grammar and check that it\n\
            says the same thing. When present, `WfConstraints` contains capture-derived format\n\
            conditions and `Constraints` contains conditions that explicitly mention the final\n\
            `value`. Empty phases are omitted; `IsWf` and `IsValid` specialize accordingly.\n\
            This file is proof-free — it is what you cite. -/"
          let specPath := dir ++ "/spec.lean"
          guardedWrite specPath
            (specHeader ++ "\n" ++ specBanner ++ "\n\n" ++ joinDecls specDecls ++ "\n")
          -- ── parser.lean ── engine + all auto-discharged proofs + the generated verified parser.
          let parserImports := libImports
            ++ ["Triptych.Theorems.DecodeLemmas", "Triptych.Theorems.Derivation"]
            ++ (if grammarStaticallyUnique then
                  ["Triptych.Theorems.RelationalParser", "Triptych.Theorems.Unambiguity"]
                else [])
            ++ [specMod]
            ++ (if needsCallerParser then [callerImport] else [])
          let parserHeader := mkHeader parserImports needsCallerParser
          let engineBanner := "/- ══════════════════════════════ engine ══════════════════════════════\n\
            The executable counterpart of the spec. `decode` walks the grammar over an input\n\
            string and returns its captured components; `computeValue` then evaluates the value\n\
            function on those captures. Generated `DecidablePred` instances make the readable\n\
            `IsWf` and `IsValid` predicates directly executable.\n\
            `decodeView` packages the exact input and value/constraint captures as a typed `View`.\n\
            \n\
            The public format API stays capitalized: use `#eval decide (IsValid s)` and\n\
            `#eval computeValue s`. The equivalence section below proves that these readable\n\
            predicates execute through the generic Triptych interpreter. -/"
          let proofBanner := "/- ════════════════════════════ equivalence ════════════════════════════\n\
            The auto-discharged guarantees relating the readable surface to the executable\n\
            engine: `IsWfGrammar_equiv` proves grammar-layout agreement and `IsWf_equiv`\n\
            proves full well-formedness agreement. `computeValue_eq` proves the values agree,\n\
            while `decodeView_input`, `IsValid_view`, and `computeValue_view` expose the typed\n\
            parse view. Derived `DecidablePred` instances make the surface predicates executable\n\
            via the engine. No `sorry`. -/"
          let parserBanner := "/- ═══════════════════════════════ parser ══════════════════════════════\n\
            The generated correct-by-construction parser `parse` (= `computeValue` gated on the\n\
            decidable `IsValid`) together with its guarantees — `parse_sound`, `parse_complete`,\n\
            `parse_reject`, `parse_view`, and typed `parse_eq_some_iff_view` /\n\
            `parse_eq_none_iff_view` normal forms — all AUTO-DISCHARGED here.\n\
            When an external parser is declared, `checkedExtParse` additionally validates each\n\
            external result against this parser and ships an AUTO-DISCHARGED soundness theorem.\n\
            A verified parser, no `sorry`. -/"
          let parserSections : List (String × Array String) :=
            [(engineBanner, engineDecls), (proofBanner, proofDecls), (parserBanner, parserDecls)]
          let parserBody := String.intercalate "\n\n"
            (parserSections.filterMap (fun (banner, decls) =>
              if decls.isEmpty then none else some (banner ++ "\n\n" ++ joinDecls decls)))
          let parserPath := dir ++ "/parser.lean"
          guardedWrite parserPath (parserHeader ++ "\n" ++ parserBody ++ "\n")
          -- ── soundness.lean ── the `sorry`d obligations, partitioned into two sections:
          -- the GENERATED parser (`<Name>.parse` — one encode-view obligation + its printer
          -- theorems), one for the EXTERNAL parser (the real Cedar `parse` — `extparse_*`).
          -- generated-first (the external printer theorems reuse the generated section's derived
          -- encode projections). Written ONLY when there is at least one obligation.
          --
          -- WRITE-ONCE (scaffold semantics): unlike spec/parser, this file holds USER work — the
          -- `sorry`s are meant to be replaced with real proofs — so an existing file is never
          -- overwritten (delete it to re-scaffold). Staleness stays impossible structurally: the
          -- obligations are stated against the defs imported from parser.lean, so a grammar change
          -- either retargets them (and outdated proofs fail to compile) or breaks the file loudly.
          -- Trade-off: generator improvements to the DISCHARGED theorems emitted here (the
          -- `parse_toString_*`/`extparse_toString_*` trios) don't reach an existing file until
          -- it is deleted and re-scaffolded.
          let mut soundWritten := false
          if !contractDecls.isEmpty then
            let soundHeader :=
              mkHeader [parserMod, callerImport, "Triptych.Automation.ExternalParser"] true
            let genBanner := "/- soundness · generated parser\n\
              Obligation about the GENERATED parser `parse`: `encode_view` says a serialized\n\
              value decodes to a valid typed view whose denotation is that value. It is left as\n\
              `sorry` — a serializer is a choice, so its correctness is yours to prove.\n\
              Given a serializer roundtrip and parser-agreement theorem, `triptych_encode`\n\
              composes them with `IsValid_view` and `computeValue_view` to build this witness.\n\
              Without an external parser, `triptych_encode_direct` composes direct generated-\n\
              spec acceptance and value proofs with the same view theorems.\n\
              `triptych_encode_derivation` instead projects a valid root derivation through the\n\
              generated `decodeView_render` theorem, removing decoder/capture-map bookkeeping.\n\
              From that one witness Triptych derives `encode_accepted`, `encode_value`, and the\n\
              printer\n\
              theorems (`parse_toString_roundtrip`/`toString_injective`/\n\
              `normalize_eq_iff_parse_eq`)\n\
              here. The derived encode projections are reused by the external section below. -/"
            let extBanner := "/- soundness · external parser\n\
              Obligations for validating YOUR OWN external parser against this specification:\n\
              `extparse_sound`, `extparse_complete`, and `extparse_reject`, stated over the\n\
              readable surface `IsValid`/`computeValue`. These are left as `sorry` — they are\n\
              claims about\n\
              your unwrapped parser, so you have to prove them yourself. The generated\n\
              `checkedExtParse` is already sound without these proofs when the spec value has\n\
              decidable equality. `triptych_sound` inverts supported successful parser paths;\n\
              `triptych_auto` then combines registered normalization and bounded search rules\n\
              with your format-specific agreement facts. `extparse_eq_some_iff_view` and\n\
              `extparse_eq_none_iff_view` then package their success and rejection consequences\n\
              as typed-view relations. The external printer theorems (`extparse_toString_*`) are\n\
              also DISCHARGED, reusing the generated section's derived encode projections. -/"
            let soundSections : List (String × Array String) :=
              [(genBanner, genContractDecls), (extBanner, extContractDecls)]
            let soundBody := String.intercalate "\n\n"
              (soundSections.filterMap (fun (banner, decls) =>
                if decls.isEmpty then none else some (banner ++ "\n\n" ++ joinDecls decls)))
            let soundPath := dir ++ "/soundness.lean"
            if ← System.FilePath.pathExists soundPath then
              logInfo m!"Triptych: {soundPath} exists — left untouched (it holds your proofs; \
                         delete it to re-scaffold)"
            else
              IO.FS.writeFile soundPath (soundHeader ++ "\n" ++ soundBody ++ "\n")
              soundWritten := true
          let filesWritten := "spec.lean, parser.lean" ++
            (if soundWritten then ", soundness.lean" else "")
          logInfo m!"Triptych: wrote {nm} → {dir}/ [{filesWritten}] \
                     ({specDecls.size} spec + {engineDecls.size} engine + {proofDecls.size} proof + \
                     {parserDecls.size} verified-parser + {contractDecls.size} obligation decls)"
          -- CAVEAT: this write is an elaboration side-effect. `lake` replays cached modules
          -- without re-running IO, so the files refresh only on a genuine cache miss — after
          -- editing the generator, force a rebuild (delete oleans or `lake clean`).
  | _ => throwUnsupportedSyntax

/-! ## `#triptych_help` — discoverable DSL vocabulary

Prints the full grammar / value / constraint DSL vocabulary so a user can see what is
expressible *before* reaching for the raw-Lean `opaque` escape hatch. The escape is the
LAST resort (it makes the value/constraint opaque to the analysis — no auto-affinity, and
its correctness is on the author); this reference exists so that fallback is a deliberate
choice, not a default taken for lack of knowing the vocabulary. -/
syntax (name := triptychHelpCmd) "#triptych_help" : command

@[command_elab triptychHelpCmd]
def elabTriptychHelp : CommandElab := fun _ => do
  let help : String := "\
Triptych DSL — the vocabulary of `triptych <Name> where …`.
Prefer these forms; the `opaque` escapes are a LAST resort (they hide the value/constraint
from analysis and put correctness on you).

── grammar ──  (required; a flat non-recursive DAG of `::=` productions)
  Name ::= item item … | alt | …     one or more `|`-separated alternatives
  item forms:
    \"lit\"                            a string literal (separators, unit tags)
    Nonterminal                      a reference to another production (the DAG edge)
    digit<len> / hexDigit<len> / bit<len>   a terminal token run
    [ item ]                         optional
    sign                             optional leading '-' (only as a production's SOLE rhs)
    rep item sepBy \"sep\" <len>       separated repetition (sep non-empty, count ≥ 1)
  <len> suffix:  +  (one-or-more)   {n}  (exactly n)   {lo,hi}  (between)

  CAPTURE RULE: only NAMED productions are captured — a capture `X` in `value`/`constraints`
  always means \"the span matched by the production named X\". Bare literals/terminals inside a
  rule are matched but recorded NOWHERE, so the value/constraint DSL cannot see them. If a
  value or constraint must read a piece, give that piece its OWN named production. In
  particular the `sign` terminal must be a production's sole rhs, so its capture is named and
  the value DSL can read its ±1 sign by that name.
  A name reused under several parents is disambiguated by QUALIFYING with the parent
  (`Parent.child`); a bare name reads only the first occurrence.
  Names use Lean identifier rules. Escape a Lean/Triptych keyword everywhere with guillemets
  (`«bit» ::= digit{1}`, then reference `«bit»`). Generated Lean names are quoted automatically;
  distinct captures that normalize to the same public binder are rejected rather than renamed.
  Follow the terminology of the format or upstream API. Cedar calls `/24` a CIDR prefix and
  represents it with `IPv4Prefix` / `IPv6Prefix`, so `Prefix` is the matching capture name.

── value ──  (optional; `Int`-valued, over the captured components)
  literals:  123        Int64.MAX        Int64.MIN
  readers on a capture X (X = a production name; see CAPTURE RULE above):
    nat X    unsigned decimal value        int X    signed (leading '-')
    len X    character length              count X  number of elements in `rep X ...`
    X        ±1 sign of a `sign` capture (bare name)
  a BARE capture name reads its sign — valid only when `X ::= sign`; the checker rejects a bare
  ref to a non-sign capture, and `nat/int/len/count` OF a sign capture.
  arithmetic:  a + b    a - b    a * b    a ^ b    ( … )    (prec: ^ > * > +/-)
  ofSpec <f>  (optional trailing sub-clause)  f : Int → δ converts the spec value to the
              generated parser's domain type δ.
  toSpec <g>  (optional trailing sub-clause)  g : δ → Int converts a domain value back to
              its readable-spec denotation. With both directions, Triptych asks for
              `toSpec_ofSpec : g (f v) = v` on accepted values. A printer's `encode_view`
              witness derives `ofSpec_toSpec : f (g d) = d`. The accepted-value law is provable
              for a lossy conversion only when constraints pin values to its faithful domain.
              A lint warns when `ofSpec` appears with no value constraint.

── value' ──  (optional ESCAPE, for values outside the DSL: structured output, calendar math)
  value' f X Y …   with  def f (x y … : String) : α := …    (`f` applied to capture STRINGS;
                   α is ANY type — a structured `IPNet`/graph/record, not just `Int`)
  a LIST argument  [X]  passes EVERY span the `rep`-repeated capture `X` matched, as
                   `List String` (the eight `H16` groups of an IPv6 address), where a scalar `X`
                   would give only the first — the way to read individually-addressable repeated
                   elements. `def f (… xs : List String) …`.
  An optional trailing `toSpec <g>` maps an external parser's result into this value type;
                   omission defaults to `id`.

── constraints ──  (optional; one per line; may refer to `value`)
  capture/string predicates (fold into IsWf):
    noLeadingZero X        X has no leading zero unless it is exactly \"0\"
    X = \"lit\"              X's matched string equals a literal
  cardinality over presence (how many of the listed captures are nonempty; SAT-style):
    nonempty X             X is present            (= atLeast 1 {X})
    atLeast k {X, Y, …}    ≥ k of the capture set present
    atMost  k {X, Y, …}    ≤ k present
    exactly k {X, Y, …}    exactly k present
  comparisons (phase follows explicit use of the final `value`):
    a ≤ b     a < b     a == b        comparisons of value expressions
    e ∈ [lo, hi]                      closed interval (⟺ lo ≤ e ∧ e ≤ hi)
  capture-only comparisons such as `nat MM ∈ [1, 12]` fold into IsWf.
  only a constraint containing the word `value` folds into SatisfiesConstraints.
  there, `value` denotes the elaborated final value function.

── constraints' ──  (optional ESCAPE, for constraints outside the DSL, e.g. calendar rules)
  one per line:  f X Y …   with  def f (x y … : String) : Bool := …   (`f` applied to captures)
  a list argument `[X]` passes all spans of a repeated capture as `List String`, and may be
  mixed with scalar arguments in the same predicate.
  these capture-only escapes fold into IsWf.

── parser ──  (optional)  parser <parse>   names an external parser and emits a sound checked
                          wrapper plus static agreement obligations. Its semantic comparison
                          uses the value section's `toSpec` clause, defaulting to `id`.
── printer ── (optional; needs value)
  printer auto            synthesizes a total certified printer only when Triptych can prove
                          that the analyzable `value` is invertible. The first supported shape is
                          `Root ::= Sign Digits`, `Sign ::= sign`, `Digits ::= digit+`, with
                          `value Sign * nat Digits` (either multiplication order). Unsupported,
                          constrained, `ofSpec`, and `value'` cases are rejected rather than
                          assigned a false total inverse.
  printer <toString>      names your canonical serializer over the DOMAIN type δ (what the
                          generated parser returns); emits one typed `encode_view` obligation and
                          derives roundtrip/injective/normalize for the GENERATED parser.
                          `triptych_encode` composes a known printer
                          roundtrip and parser-agreement theorem with the generated view facts.
                          `triptych_encode_direct` instead starts from direct generated-spec
                          acceptance and value proofs, with no external parser dependency.
                          `triptych_encode_derivation` starts from a valid root derivation;
                          a `DerivationPrinter` packages `toDerivation` with structural, view, and
                          denotation proofs. Several certificates may expose different verified
                          presentations of the same value.
                          If a `parser` clause is present, derived
                          acceptance/value projections also prove the EXTERNAL parser's trio.
── to ──      (optional)  to \"<dir>\"                        writes <dir>/{spec,parser,soundness}.lean.
                          spec/parser are regenerated every elaboration; soundness is a
                          WRITE-ONCE scaffold (it holds your proofs) — delete it to re-scaffold.
                          A pre-existing spec/parser file NOT generated by this tool (no
                          `/- Generated by Triptych` header) is never overwritten — hard error.

Section order:  grammar · value · value' · constraints · constraints' · parser · printer · to
(`ofSpec`/`toSpec` are semantic sub-clauses of `value`; `value'` may carry `toSpec`).
When a format needs something not listed here, that is a signal to either (a) use the
matching escape section (`value'` / `constraints'`) for that one piece, or (b) request the
vocabulary be extended — not to hand-write the whole spec in Lean."
  logInfo help

end Triptych
