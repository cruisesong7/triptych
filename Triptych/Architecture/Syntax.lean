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

/-!
# `triptych` embedded DSL

Surface syntax for flat non-recursive attribute grammars, transcribing the `::=`
grammars written in `doc/CedarDoc/*.lean`. Lean's own `syntax`/`declare_syntax_cat`
framework does all the *parsing* of the notation; this module declares the notation
and elaborates the resulting `Syntax` tree into the generated declarations.

The command has three sections (see design note §16.3), in order:

```
triptych Decimal where
  grammar
    Decimal  ::= Integer "." Fraction
    Integer  ::= ["-"] digit+
    Fraction ::= digit{1,4}
  constraints
    -- value/string constraints (raw Lean predicates for now; see below)
  value
    -- the value function (a raw Lean term for now; see below)
```

* **`grammar`** (required) — the EBNF productions. Elaborated fully into the core
  `Triptych.Grammar` value bound to `<Name>.grammar`. `grammar` is used rather than
  `syntax` because `syntax` is a reserved Lean keyword.
* **`constraints`** (optional) — currently captured as raw Lean predicate terms
  (`String → Prop`) and bound to `<Name>.constraints`. Per §16.3 these will later be
  written in a small predicate DSL and auto-classified into `IsWf` (string-only) vs
  `SatisfiesConstraints` (value-dependent).
* **`value`** (optional) — currently captured as a raw Lean term and bound to
  `<Name>.valueFn` (the §16.4 "opaque" tier). Per §16.4 this will later be written in
  a flat first-order value-DSL that is analyzed for affinity to auto-generate proofs.

Grammar notation:
* a production is `Name ::= item item …`
* an item is a string literal, a nonterminal reference (`ident`), a terminal
  (`digit`/`hexDigit` with a length suffix), or an optional `[item]`
* length suffix: `+` (one-or-more), `{n}` (exactly), `{lo,hi}` (between)

Not yet: production-level alternation (`A ::= x | y`), the predicate/value DSLs, and
generation of `IsWf` / `SatisfiesConstraints` / `IsValid` / `computeValue`. Those
are the next increments; this module currently generates the grammar value (+ captures
the raw value/constraint terms) so the three-section shape is in place.
-/

namespace Triptych

open Lean Elab Command

/-- Length suffix on a terminal: `+`, `{n}`, `{lo,hi}`. -/
declare_syntax_cat fmtLen
syntax "+"                : fmtLen
syntax "{" num "}"        : fmtLen
syntax "{" num "," num "}" : fmtLen

/-- A right-hand-side item: literal, nonterminal ref, terminal, or optional. -/
declare_syntax_cat fmtItem
syntax str                : fmtItem  -- literal
syntax "digit" fmtLen     : fmtItem  -- decimal terminal
syntax "hexDigit" fmtLen  : fmtItem  -- hex terminal
syntax "bit" fmtLen       : fmtItem  -- binary terminal (`0`/`1`)
syntax ident              : fmtItem  -- nonterminal reference
syntax "[" fmtItem "]"    : fmtItem  -- optional
-- Dedicated SIGN terminal: an optional leading `"-"`, whose CAPTURE denotes ±1 in `value` (bare
-- name, no `sign` keyword). Sugar for `["-"]` denotationally (so the engine/proofs are unchanged),
-- but only legal as a production's SOLE rhs item (`Sign ::= sign`), so the sign always lives in its
-- own named capture — the fix for the "bare `["-"]` is invisible to `value`" trap.
syntax "sign"             : fmtItem  -- optional '-' sign token (see CAPTURE RULE)
-- separated GROUP repetition: `rep H16 sepBy ":" {8}` = eight `H16`s joined by `":"`
-- (`item (sep item)*`, item-count per the `fmtLen`: `{8}`→exactly, `{1,8}`→range, `+`→≥1).
syntax "rep" fmtItem "sepBy" str fmtLen : fmtItem

/-- One alternative: a sequence of items. -/
declare_syntax_cat fmtSeq
syntax (colGt fmtItem)+ : fmtSeq

/-- A production: `Name ::= seq | seq | …` — one or more `|`-separated alternatives.
    `withPosition`/`colGt` pins the RHS strictly right of the LHS column, so the greedy
    parse stops at the next production's LHS instead of consuming it. -/
declare_syntax_cat fmtProd
syntax withPosition(ident " ::= " sepBy1(fmtSeq, " | ")) : fmtProd

/-- The optional `constraints` section: predicates in the constraint-DSL (`constraintExpr`),
    one per line (`colGt`, like the `grammar` productions — no commas). Auto-classified
    (string → `IsWf`, value → `SatisfiesConstraints`) downstream. -/
syntax fmtConstraints := "constraints" (colGt constraintExpr)+

/-- One ESCAPE entry: an ordinary Lean function applied to capture names, `f X Y …` (head
    ident + one-or-more capture idents). Its own syntax category so it destructures cleanly
    (vs. raw `Syntax` archaeology). Shared by the `constraints'` / `value'` sections. -/
declare_syntax_cat fmtEscEntry
syntax ident (ppSpace ident)+ : fmtEscEntry

/-- The optional `constraints'` ESCAPE section (design note §16.7): constraints outside the
    DSL vocabulary, each an `f X Y …` call with `f : String → … → Bool`, one line each
    (`colGt`). Reads like a Lean call; the generator feeds each capture its decoded string
    (no `Env`/`Option` in the author's `f`). The prime marks "the raw-Lean escape of the
    `constraints` section". -/
syntax fmtConstraintsEsc := "constraints'" (colGt fmtEscEntry)+

/-- The `lift <σ>` sub-clause of `value`: names a *lift* `σ : β → δ` from the spec value type `β`
    (e.g. the fixed-point `Int`) UP to the domain type `δ` (e.g. `Decimal`), a section of the
    external parser's `projection π : δ → β` (i.e. `σ ∘ π = id`, discharged by `lift_section` in
    `soundness.lean`; the dual `π ∘ σ = id` on ACCEPTED values is the `lift_faithful` obligation,
    emitted when both clauses are present — see the lift guard in `elabTriptych`).
    When present, the GENERATED parser returns `Option δ` (type-identical to a
    real external parser) via `(gatedParse …).map σ`, and its contracts become the σ-VIEW
    analogues (`(computeValue s).map σ = some d`). Works standalone (no `parser`/`printer` needed):
    it just upgrades the generated parser's output type. Nested inside `value` (like `projection`
    inside `parser`) because a lift only makes sense for the scalar `value` DSL — the `value'`
    escape already picks its own output type, so a lift there would be a redundant `id`. -/
syntax fmtLift := "lift" term

/-- The optional `value` section: the value-DSL formula (`valExpr`); analyzable, `value(X)=…`.
    May carry a trailing `lift <σ>` sub-clause (see `fmtLift`) — grammatically nested here (like
    `projection` inside `parser`), because a lift only makes sense for the scalar `value` DSL. -/
syntax fmtValue := "value" valExpr (fmtLift)?

/-- The optional `value'` ESCAPE section (design note §16.4/§16.7): a value outside the DSL
    vocabulary, an `f X Y …` call with `f : String → … → Int`. Same shape/contract as
    `constraints'` (no `Env`); the prime marks "the raw-Lean escape of the `value` section". -/
syntax fmtValueEsc := "value'" fmtEscEntry

/-- The optional `parser` clause: names the external hand-written parser and the
    projection reading its value's `Int` denotation back out. When present, the command
    emits the contract theorem *obligations* (`<Name>.sound`/`.complete`/`.reject`) as
    `sorry`d theorems relating that parser to the generated spec. -/
syntax fmtParser := "parser" term " projection " term

/-- The optional `printer` clause: names the user's canonical serializer `toStr : β → String`
    for the spec value type `β`. A serializer can't be synthesized (the canonical form is a
    choice), so it is supplied here; from two `sorry`d β-encode obligations
    (`encode_accepted` / `encode_value`) the command auto-derives the three printer theorems
    Cedar proves (`parse_toString_roundtrip` / `toString_injective` /
    `normalize_eq_iff_parse_eq`) for the GENERATED parser, and — when a `parser` clause is also
    present — the same trio (`extparse_*`) for the EXTERNAL parser, stated in β-VIEW via that
    parser's projection (both parsers project to `β`, so ONE serializer serves both; the
    generated parser is the `π = id` case). Needs a `value` section. -/
syntax fmtPrinter := "printer" term

/-- Optional trailing clause: `to "<dir>"` writes the generated modules
    `<dir>/{spec,parser,soundness}.lean` (the directory must already exist; `soundness.lean`
    only when there is at least one obligation). Overwrite discipline, by file:
    `spec.lean`/`parser.lean` are REGENERATED every elaboration, but only over files carrying
    the "Generated by Triptych" sentinel header comment — a pre-existing file without it is
    someone else's, so the write is a hard error (see `guardedWrite`). `soundness.lean` is a
    WRITE-ONCE scaffold (it holds the user's proofs): never overwritten once it exists;
    delete it to re-scaffold. -/
syntax fmtTo := "to " str

/-- The `triptych` command, sections in order: `grammar` (required), `value`
    (optional, with an optional trailing `lift`), `constraints` (optional), `parser`
    (optional, with a required `projection`), `printer` (optional), `to` (optional).
    `value` precedes `constraints` so a constraint can refer to `value`.
    The `parser`/`printer` clauses emit the sorried obligations; the `to "<dir>"` clause
    writes the generated modules. `#show` logs each declaration. -/
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
  | `(fmtItem| $i:ident)          => `(Sym.ref $(Syntax.mkStrLit i.getId.toString))
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
  | `(fmtItem| $i:ident)           => pure (.ref i.getId.toString)
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
      pure { name := lhs.getId.toString, alts := ← alts.getElems.toList.mapM parseSeq }
  | s => throwErrorAt s "unrecognized production"

/-- Destructure an ESCAPE entry `f X Y …` into its head function ident and capture idents. -/
def parseEscEntry : TSyntax `fmtEscEntry → CommandElabM (TSyntax `ident × Array (TSyntax `ident))
  | `(fmtEscEntry| $f:ident $is:ident*) => pure (f, is)
  | s => throwErrorAt s "unrecognized escape entry"

/-- Strip macro scopes from every identifier in a syntax tree, so pretty-printing yields
    clean source without hygiene daggers (`✝`). Used when writing generated declarations
    to a file. -/
partial def deHygiene (stx : Syntax) : Syntax :=
  match stx with
  | .ident info rawVal val pre => .ident info rawVal val.eraseMacroScopes pre
  | .node info kind args       => .node info kind (args.map deHygiene)
  | s                          => s

/-- Elaborate the `triptych` command: generates + elaborates the declarations, tagged
    into four sections, and — with a `to "<dir>"` clause — writes them as one module
    `<dir>/spec.lean`. `#show` additionally logs each declaration.

    The generated file is ONE module in four `═══`-banner sections (dependency order):
    * **spec** (`emitSpec`) — the reader-facing spec: `grammar`, readable per-production
      `IsWf.*` predicates, `value`, `Constraints`, `SatisfiesConstraints`, `IsValid`
      (valid = grammar ∧ constraints, matching Cedar's wording).
    * **engine** (`emitEngine`) — the analyzable/executable machinery: deep `valueExpr`/
      `valueFn`/`constraints` ASTs + the decode-backed interpreter bundle (`isWf`/
      `isValid`/`computeValue`).
    * **soundness** (`emitSound`) — the guarantees tying the two together: the surface⟺engine
      `Internal.matchesRef.*` lemmas + `IsWf_equiv`, and the derived `DecidablePred
      IsWf.<start>` instance (transported across the equiv — the payoff of the interpreter).
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
      --                   `Constraints`, `SatisfiesConstraints`, `IsValid`. Proof-free.
      --   parser.lean   ← bufE ++ bufP ++ bufR: the runnable + trusted artifact (run + trust)
      --                   — engine bundle, ALL auto-discharged proofs (`IsWf_equiv`,
      --                   `computeValue_eq`, decidability), and the generated verified `parse`
      --                   + its discharged contracts. No `sorry`.
      --   soundness.lean ← bufC: ONLY the external-parser obligations (`sorry`d), emitted only
      --                   when a `parser … projection …` clause names a real external parser.
      let bufS ← IO.mkRef (#[] : Array String)   -- spec file
      let bufE ← IO.mkRef (#[] : Array String)   -- engine (→ parser file)
      let bufP ← IO.mkRef (#[] : Array String)   -- reconciliation proofs (→ parser file)
      let bufR ← IO.mkRef (#[] : Array String)   -- generated verified parser (→ parser file)
      -- soundness.lean is partitioned into TWO sections, one per parser: `bufCg` holds the
      -- GENERATED parser's obligations + printer theorems (about `<Name>.parse`), `bufCx` the
      -- EXTERNAL parser's (about the real Cedar `parse`). Written generated-first, because the
      -- external printer theorems reuse the generated section's shared encode obligations.
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
      -- Per-production well-formedness (SPEC): `<Name>.IsWf.<Prod>` for each production as
      -- an INLINED structural predicate (∃ named captures, s = … ∧ …) — the readable form,
      -- reading like the hand specs (`IsWfDatetime`, `IsWfV4`). Capital-`I` `IsWf` = the Prop
      -- you read/prove; lowercase `isWf` (the engine bundle, below) = the decidable checker.
      -- These are reader-facing, so SPEC section. Emitted in topological (leaf-first) order.
      let gval : Triptych.Grammar :=
        { start := startName, prods := prodVals }
      for prod in Triptych.topoOrder gval do
        let pIdent := mkIdentFrom name (name.getId ++ `IsWf ++ prod.name.toName)
        let sVar ← `(s)
        let body ← Triptych.prodPred name.getId prod sVar
        emitSpec (← `(def $pIdent (s : String) : Prop := $body))
      -- SOUNDNESS + DECIDABILITY (SOUNDNESS section, emitted last). The readable `IsWf.<start>`
      -- is `∃ …` over `String`, so it has NO structural `Decidable` instance; the ONLY way it
      -- becomes executable is by transporting the interpreter's `DecidablePred (IsWf grammar)`
      -- across the equivalence `<Name>.IsWf_equiv`. So the equivalence + the derived instance
      -- are properties *of the spec* (soundness vs the analyzable engine, and an executable
      -- validator via the interpreter — the whole point of keeping the interpreter). The
      -- `Internal.matchesRef.*` support lemmas that `IsWf_equiv` is built from are tucked under
      -- `.Internal`. This closure runs after the engine bundle (it references `IsWf grammar`).
      -- `hasConstraints`/`hasValue`: which surface defs exist (set below), so the emitted
      -- decidability instances unfold exactly the defs present.
      let emitReconcile (hasConstraints hasValue : Bool) : CommandElabM Unit := do
        let fuelBound := gval.prods.length
        for prod in Triptych.topoOrder gval do
          let depth := Triptych.subtreeDepth gval prod.name fuelBound
          emitSound (← Triptych.matchesRefProof name.getId grammarIdent prod depth)
        if let some startProd := gval.prods.find? (·.name == gval.start) then
          emitSound (← Triptych.isWfEquivProof name.getId grammarIdent startProd)
          let equivId  := mkIdentFrom name (name.getId ++ `IsWf_equiv)
          let startIsWfId := mkIdentFrom name (name.getId ++ `IsWf ++ startProd.name.toName)
          -- Explicit instance names (`<Name>.instDecidable*`): anonymous instances get an
          -- auto-name derived from the (structurally identical) type `DecidablePred (String
          -- → Prop)`, which collides across generated modules when several are imported.
          let instWfId  := mkIdentFrom name (name.getId ++ `instDecidableIsWf)
          let instScId  := mkIdentFrom name (name.getId ++ `instDecidableSatisfiesConstraints)
          let instAccId := mkIdentFrom name (name.getId ++ `instDecidableIsValid)
          -- Source `Decidable (IsWf grammar s)` comes from `decIsWf` (the decode roundtrip),
          -- which now takes the `g.repOk = true` side condition — discharged by `decide` at
          -- this concrete grammar (the DSL guarantees it: non-empty rep separators, `lo ≥ 1`).
          emitSound (← `(instance $instWfId:ident : DecidablePred $startIsWfId := fun s =>
                        @decidable_of_iff _ _ ($equivId s) (Triptych.decIsWf $grammarIdent (by decide) s)))
          -- Decidability of the full validity predicate: `SatisfiesConstraints` is a
          -- `def` over decode-extracted strings + decidable atoms (`≤`/`≠`/…), so it needs
          -- its instance unfolded; then `IsValid = IsWf.<start> ∧ SatisfiesConstraints`
          -- is decidable by the `And` instance (both conjuncts now decidable). This makes
          -- `decide (<Name>.IsValid s)` — the executable validator — resolve.
          let scSurfId  := mkIdentFrom name (name.getId ++ `SatisfiesConstraints)
          let accSurfId := mkIdentFrom name (name.getId ++ `IsValid)
          let cRIdent   := mkIdentFrom name (name.getId ++ `Constraints)
          let valIdent  := mkIdentFrom name (name.getId ++ `value)
          -- With no constraints section `SatisfiesConstraints` is an `abbrev … := True`
          -- (transparently decidable), so no SC instance is needed; `IsValid`'s instance
          -- then rests on `IsWf`'s instance + `True`'s. With constraints, unfold through
          -- `SatisfiesConstraints → Constraints → value` to expose the decidable atoms.
          if hasConstraints then
            let unfoldList : Array (TSyntax `ident) :=
              #[scSurfId, cRIdent] ++ (if hasValue then #[valIdent] else #[])
            emitSound (← `(instance $instScId:ident : DecidablePred $scSurfId :=
                          fun s => by simp only [$[$unfoldList:ident],*]; exact inferInstance))
          -- `IsValid` is an `abbrev` (`IsWf.<start> s ∧ SatisfiesConstraints s`); both
          -- conjuncts are decidable (above), so the `And` instance resolves in term mode.
          emitSound (← `(instance $instAccId:ident : DecidablePred $accSurfId :=
                        fun s => inferInstanceAs (Decidable (_ ∧ _))))
          -- FULL acceptance equivalence: surface `IsValid` ⟺ engine `isValid`. Composes
          -- `IsWf_equiv` + the `decodeSome_iff_IsWf` roundtrip (WF halves) with reader
          -- agreement (constraint halves). The capstone soundness guarantee.
          emitSound (← Triptych.isValidEquivProof name.getId hasConstraints hasValue)
      -- Value (optional), processed BEFORE constraints so a constraint may refer to `value`.
      -- DSL tier (`value <formula>`, `v`): elaborate the value-DSL to a `ValExpr` (bound as
      -- `valueExpr`) whose `eval` is the value fn; `valueSub` is the `ValExpr` substituted for
      -- a `value` reference in constraints. ESCAPE tier (`value' f X Y …`, `ve`): bind
      -- `valueFn` to the author's fn applied to the decoded captures (no `ValExpr` AST — so
      -- `computeValue`/contracts, which need the AST, are DSL-tier only).
      let mut valueSub : Option (TSyntax `term) := none
      let mut veIdent? : Option (TSyntax `ident) := none
      let mut valueCaps : List String := []
      let mut hasValueEsc : Bool := false
      let mut constrCaps : Option (List String) := none  -- captures the surface `Constraints` binds (none ⟹ no constraints section)
      if let some vStx := v then
        let ve : TSyntax `valExpr := ⟨vStx.raw[1]⟩
        -- SIGN-REFERENCE VALIDATION: a BARE capture name in `value` denotes its sign (±1), so it
        -- must name a dedicated sign production (`X ::= sign`). Reject a bare ref to a non-sign
        -- capture (the old silent-`+1` trap), and reject `nat`/`int`/`len` applied to a sign
        -- capture (a sign holds only `""`/`"-"`, so a magnitude reader on it is meaningless).
        let signRefs := Triptych.valExprSignCaptures ve
        let magRefs := (Triptych.valExprCaptures ve).filter (· ∉ signRefs)
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
        -- (no `Env`), via `natOf`/`intOf`/… — reads like `value(Integer, Fraction) = …`.
        let readable ← liftMacroM (elabValReadableWith none ve)
        let capNames := Triptych.valExprCaptures ve
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
        | `(fmtValueEsc| value' $e:fmtEscEntry) =>
          let (f, is) ← parseEscEntry e
          hasValueEsc := true
          let vfnIdent := mkIdentFrom name (name.getId ++ `valueFn)
          -- ARBITRARY value type: no `: Env → Int` ascription — the author's `f` return type
          -- flows through (Env → α for whatever α `f` produces: Int, SimpleGraph, matrix, …),
          -- so a `value'` escape can parse to a STRUCTURED value, not just a scalar.
          emitEngine (← `(def $vfnIdent := $(← liftMacroM (Triptych.opaqueEnvClosure f is))))
          -- spec: a READABLE `<Name>.value` — the author's call over the surface string binders
          -- (return type inferred from `f`, likewise not pinned to `Int`).
          let capNames := is.toList.map (·.getId.toString)
          let binders : Array (TSyntax `ident) :=
            (capNames.map (fun c => mkIdent (Name.mkSimple (Triptych.surfaceBinder c)))).toArray
          let bArgs : Array (TSyntax `term) := binders.map (fun i => ⟨i.raw⟩)
          let valIdent := mkIdentFrom name (name.getId ++ `value)
          emitSpec (← `(def $valIdent $[($binders : String)]* := $f $bArgs*))
          valueCaps := capNames
        | _ => throwUnsupportedSyntax
      -- Constraints (optional): constraint-DSL predicates, one per line, with `value`
      -- substituted by the value expression. The `fmtConstraints` node is
      -- `"constraints" (colGt constraintExpr)+`; arg 1 is the plain array of exprs.
      -- Always bind `<Name>.constraints` (empty list if the section is absent) so the
      -- bundled predicates below can reference it uniformly.
      let cIdent := mkIdentFrom name (name.getId ++ `constraints)
      -- `constraints'` escape entries (`cse`): each is a raw `f X Y …` (head ident + capture
      -- idents). Parse them into (fn, captureIdents) pairs. Present ⟹ caller import needed.
      let escEntries : Array (TSyntax `ident × Array (TSyntax `ident)) ← match cse with
        | some cseStx =>
          let lines : Array (TSyntax `fmtEscEntry) := cseStx.raw[1].getArgs.map (⟨·⟩)
          lines.mapM parseEscEntry
        | none => pure #[]
      let hasOpaque := !escEntries.isEmpty
      -- DSL constraint exprs (may be empty even when `constraints'` is present).
      let dslExprs : Array (TSyntax `constraintExpr) := match cs with
        | some csStx => csStx.raw[1].getArgs.map (⟨·⟩)
        | none       => #[]
      if cs.isSome || cse.isSome then
        -- ENGINE `constraints` list: DSL entries (`.dsl`) ++ escape entries (`.opaque`).
        let dslTerms ← dslExprs.mapM (fun e => liftMacroM (elabEntryWith valueSub e))
        let escTerms ← escEntries.mapM (fun (f, is) => do
          `(ConstraintEntry.opaque $(← liftMacroM (Triptych.opaqueEnvClosure f is))))
        let csep : Syntax.TSepArray `term "," := .ofElems (dslTerms ++ escTerms)
        emitEngine (← `(def $cIdent : List ConstraintEntry := [$csep,*]))
        -- SPEC `Constraints` Prop: DSL forms rendered readably ++ each escape as `f x y = true`
        -- over the surface binders. A `value` reference renders as `<Name>.value <comps>`.
        let valSubR : Option (TSyntax `term) ← match veIdent? with
          | some _ =>
            let vId := mkIdentFrom name (name.getId ++ `value)
            let vArgs : Array (TSyntax `term) :=
              (valueCaps.map (fun c => ⟨(mkIdent (Name.mkSimple (Triptych.surfaceBinder c))).raw⟩)).toArray
            pure (some (← `($vId $vArgs*)))
          | none   => pure none
        let dslRTerms ← dslExprs.mapM (fun e => liftMacroM (elabConstraintReadable valSubR e))
        let escRTerms ← escEntries.mapM (fun (f, is) => do
          let bArgs : Array (TSyntax `term) := is.map (fun i =>
            ⟨(mkIdent (Name.mkSimple (Triptych.surfaceBinder i.getId.toString))).raw⟩)
          `($f $bArgs* = true))
        let allR := dslRTerms ++ escRTerms
        let body ← match allR.toList with
          | []      => `(True)
          | x :: xs => xs.foldlM (fun acc p => `($acc ∧ $p)) x
        -- capture params: DSL captures ∪ escape captures ∪ value captures (if `value` used)
        let usesValue := dslExprs.any (fun e => (Triptych.constraintUsesValue e))
        let escCaps := escEntries.toList.flatMap (fun (_, is) => is.toList.map (·.getId.toString))
        let cCaps := (dslExprs.toList.flatMap Triptych.constraintCaptures ++ escCaps
                        ++ (if usesValue then valueCaps else [])).eraseDups
        let cBinders : Array (TSyntax `ident) :=
          (cCaps.map (fun c => mkIdent (Name.mkSimple (Triptych.surfaceBinder c)))).toArray
        let cRIdent := mkIdentFrom name (name.getId ++ `Constraints)
        emitSpec (← `(def $cRIdent $[($cBinders : String)]* : Prop := $body))
        constrCaps := some cCaps
      else
        emitEngine (← `(def $cIdent : List ConstraintEntry := []))
      -- ENGINE bundle (lowercase): the decode-backed interpreter predicates. The readable
      -- surface `IsWf.<start>` is PROVEN equal to `Triptych.isWf` by `<Name>.IsWf_equiv`.
      let wfIdent  := mkIdentFrom name (name.getId ++ `isWf)
      let scIdent  := mkIdentFrom name (name.getId ++ `satisfiesConstraints)
      let accIdent := mkIdentFrom name (name.getId ++ `isValid)
      emitEngine (← `(abbrev $wfIdent  (s : String) : Prop := Triptych.isWf $grammarIdent $cIdent s))
      emitEngine (← `(abbrev $scIdent  (s : String) : Prop := Triptych.satisfiesConstraints $grammarIdent $cIdent s))
      emitEngine (← `(abbrev $accIdent (s : String) : Prop := $wfIdent s ∧ $scIdent s))
      if let some veIdent := veIdent? then
        -- DSL tier: `computeValue` via the analyzable `ValExpr` (Int-valued).
        let cvIdent := mkIdentFrom name (name.getId ++ `computeValue)
        emitEngine (← `(def $cvIdent (s : String) : Option Int :=
                      Triptych.computeValue $grammarIdent $veIdent s))
      else if hasValueEsc then
        -- ESCAPE tier: `computeValue` via `computeValueF` and the author's `valueFn` — the
        -- value type is arbitrary (inferred from `valueFn`), so this parses to whatever
        -- structured value `value'` produces (`Option SimpleGraph`, `Option (Matrix …)`, …).
        let cvIdent := mkIdentFrom name (name.getId ++ `computeValue)
        let vfnIdent := mkIdentFrom name (name.getId ++ `valueFn)
        emitEngine (← `(def $cvIdent (s : String) :=
                      Triptych.computeValueF $grammarIdent $vfnIdent s))
      -- SPEC bundle (capitalized): the citable validity predicate, engine-free except for
      -- the `grammar` + library `decode` (the irreducible String→components bridge). Matches
      -- Cedar's wording — "a string is VALID iff it satisfies the grammar and constraints":
      --   `SatisfiesConstraints (s)`: decode `s`, then apply the readable `Constraints` to
      --     the extracted components (`True` if no constraints section).
      --   `IsValid (s) := IsWf.<start> s ∧ SatisfiesConstraints s`.
      let startName : Name := (gval.prods.head?.map (·.name.toName)).getD name.getId
      let startIsWf := mkIdentFrom name (name.getId ++ `IsWf ++ startName)
      let scSurf := mkIdentFrom name (name.getId ++ `SatisfiesConstraints)
      let accSurf := mkIdentFrom name (name.getId ++ `IsValid)
      -- `SatisfiesConstraints s`: decode `s` and apply the readable `Constraints` to the
      -- extracted component strings (`True` if there is no constraints section). All forms,
      -- including `opaque*` escapes (now string-param), live uniformly inside `Constraints`.
      match constrCaps with
      | none =>
        emitSpec (← `(abbrev $scSurf (s : String) : Prop := True))
      | some caps =>
        let cRIdent := mkIdentFrom name (name.getId ++ `Constraints)
        let args : Array (TSyntax `term) ← caps.toArray.mapM (fun c =>
          `(Triptych.component $grammarIdent s $(Syntax.mkStrLit c)))
        emitSpec (← `(def $scSurf (s : String) : Prop := $cRIdent $args*))
      emitSpec (← `(abbrev $accSurf (s : String) : Prop := $startIsWf s ∧ $scSurf s))
      -- Soundness/decidability (SOUNDNESS section): the surface⟺engine `IsWf_equiv` + the
      -- derived `Decidable` instances. Runs after the engine bundle + surface `IsValid`.
      emitReconcile constrCaps.isSome veIdent?.isSome
      -- VALUE equivalence (SOUNDNESS section): surface `value` ⟺ engine `computeValue`, as a
      -- standalone theorem (the value analogue of `IsWf_equiv`). Emitted whenever a value
      -- section is present — DSL tier (`veIdent?`) or `value'` escape (`hasValueEsc`).
      if veIdent?.isSome || hasValueEsc then
        emitSound (← Triptych.computeValueEqProof name.getId grammarIdent valueCaps veIdent?.isSome)
      -- GENERATED VERIFIED PARSER (→ parser file): whenever a value section exists, emit the
      -- tool's own `<Name>.parse` and its three AUTO-DISCHARGED contracts (`parse_sound`/
      -- `parse_complete`/`parse_reject`). Gated on the engine `isValid` (structurally decidable),
      -- so the parser is self-contained relative to the engine — no `sorry`. This is the
      -- correct-by-construction parser; the external obligations below are the SEPARATE
      -- translation-validation surface. A `lift <σ>` clause LIFTS the output to the domain type
      -- `δ` (so `parse : String → Option δ`, σ-view contracts); otherwise it returns `β`.
      let liftTerm? : Option (TSyntax `term) := do
        let vStx ← v
        match vStx with
        | `(fmtValue| value $_:valExpr lift $σT:term) => some σT
        | _ => none
      if veIdent?.isSome || hasValueEsc then
        for cmd in ← Triptych.parserContractsProof name.getId veIdent?.isSome liftTerm? do
          emitParser cmd
      -- LIFT GUARD (lint): a `lift σ` whose σ is not injective on all of `Int` (e.g.
      -- `Int64.ofInt`, which WRAPS) needs a value constraint carving the accepted language down
      -- to σ's faithful domain — otherwise out-of-range inputs are ACCEPTED and σ silently wraps
      -- them (internally consistent, so no generated proof fails; only `lift_faithful` below —
      -- when a projection exists — or a conformance test would catch it). We can't inspect σ
      -- (an opaque term), so this is a heuristic WARNING, not an error: no DSL constraint
      -- mentions `value` and no `constraints'` escape is present ⟹ warn. A total-injective σ
      -- (a plain embedding) legitimately needs no constraint — then ignore the warning.
      if let some σT := liftTerm? then
        unless dslExprs.any Triptych.constraintUsesValue || hasOpaque do
          logWarningAt σT m!"`lift` without a value constraint: if `{σT}` is not injective on \
            all of Int (e.g. it wraps, like `Int64.ofInt`), out-of-range inputs will be ACCEPTED \
            and silently wrapped by the lifted parser. Add a range constraint matching the \
            lift's faithful domain (e.g. `value ∈ [Int64.MIN, Int64.MAX]`) — with a `parser … \
            projection` clause the emitted `lift_faithful` obligation is unprovable without it. \
            If the lift is a total embedding, this warning can be ignored."
      -- LIFT FAITHFULNESS (→ soundness file, generated section): with BOTH `lift σ` and a
      -- `parser … projection π` clause, emit the obligation `lift_faithful : isValid s →
      -- computeValue s = some v → π (σ v) = v` — faithfulness of the lift on ACCEPTED values,
      -- the dual of `lift_section` (`σ ∘ π = id` everywhere; here `π ∘ σ = id` on the accepted
      -- language, where alone it can hold for a wrapping σ). Its proof is exactly what the
      -- value range constraint provides, so a missing/too-loose constraint makes it UNPROVABLE —
      -- the silent-wrap trap surfaces as a permanent `sorry` instead of wrong behavior. Payoff
      -- (discharged): `parse_sound_proj`, the π-VIEW soundness of the generated lifted parser —
      -- the same contract shape as the external `extparse_sound`.
      if let some σT := liftTerm? then
        if let some prStx := pr then
          if let `(fmtParser| parser $_:term projection $projT:term) := prStx then
            let faithId     := mkIdentFrom name (name.getId ++ `lift_faithful)
            let soundProjId := mkIdentFrom name (name.getId ++ `parse_sound_proj)
            let validEng    := mkIdentFrom name (name.getId ++ `isValid)
            let cvIdent     := mkIdentFrom name (name.getId ++ `computeValue)
            let parseId     := mkIdentFrom name (name.getId ++ `parse)
            let (dTy, dNm) ← Triptych.liftCodomainBinder σT
            let dId := mkIdent dNm
            emitContractGen (← `(theorem $faithId (s : String) (v : Int) :
                $validEng s → $cvIdent s = some v → $projT ($σT v) = v := by sorry))
            emitContractGen (← `(theorem $soundProjId (s : String) ($dId : $dTy) :
                $parseId s = some $dId → $validEng s ∧ $cvIdent s = some ($projT $dId) :=
              Triptych.gatedParseLift_sound_proj $validEng $cvIdent $σT $projT $faithId s $dId))
      -- EXTERNAL-PARSER obligations (→ soundness file): with a `parser <p> projection <π>`
      -- clause naming an EXISTING external parser, emit `<Name>.sound`/`.complete`/`.reject` as
      -- `sorry`d theorems (design §16.1), stated over the SURFACE `<Name>.IsValid`/
      -- `computeValue` — the human-facing "the real parser accepts iff the readable spec is
      -- valid, with matching value". These are the ONLY obligations left to the human; they
      -- reference the external parser, so the soundness file re-imports the caller module.
      if let some prStx := pr then
        if let `(fmtParser| parser $parseT:term projection $projT:term) := prStx then
          -- Statements written OUT (not `RejectStmt`/`SoundStmt`/…), so the obligation reads as
          -- the actual proposition to prove for the external parser `parseT` (projection `projT`).
          let rejIdent := mkIdentFrom name (name.getId ++ `extparse_reject)
          emitContractExt (← `(theorem $rejIdent (s : String) :
              $parseT s = none ↔ ¬ $accSurf s := by sorry))
          -- Concrete type + one-letter binder from the EXTERNAL parser's `Option` payload
          -- (e.g. Cedar `Decimal` → `d`); reused by both obligations and the printer theorems.
          let (extTy, extNm) ← Triptych.optionPayloadBinder parseT
          let extId := mkIdent extNm
          let compIdent  := mkIdentFrom name (name.getId ++ `extparse_complete)
          -- `sound`/`complete` need a value function — emitted whenever a `value` OR `value'`
          -- section is present (both produce `<Name>.computeValue`; the escape tier's value
          -- type is arbitrary, matched by the `projection`'s codomain).
          if veIdent?.isSome || hasValueEsc then
            let cvIdent := mkIdentFrom name (name.getId ++ `computeValue)
            let soundIdent := mkIdentFrom name (name.getId ++ `extparse_sound)
            -- Both obligations parametrized over the external output `extId` (matching Cedar's
            -- target-parametrized `parse_sound`/`parse_complete`).
            emitContractExt (← `(theorem $soundIdent (s : String) ($extId : $extTy) :
                $parseT s = some $extId → $accSurf s ∧ $cvIdent s = some ($projT $extId) := by sorry))
            emitContractExt (← `(theorem $compIdent (s : String) ($extId : $extTy) :
                $accSurf s → $cvIdent s = some ($projT $extId) → $parseT s = some $extId := by sorry))
      -- PRINTER (→ soundness file): `printer <toStr>` names ONE canonical serializer
      -- `toStr : δ → String` over the DOMAIN type δ (the type BOTH parsers return). From `sorry`d
      -- encode obligations the three printer theorems Cedar proves are AUTO-DERIVED in the clean
      -- δ-VIEW (`parse (toStr d) = some d`, matching Cedar's `parse_toString_roundtrip`) for the
      -- GENERATED parser (`parse_toString_roundtrip` / `toString_injective` /
      -- `normalize_eq_iff_parse_eq`) — and, when a `parser` clause is present, the SAME trio
      -- (`extparse_*`) for the EXTERNAL parser. Needs a value section.
      --
      -- With a `lift σ` (in `value`) + `parser … projection π`, the generated parser is LIFTED to
      -- δ and closes its roundtrip π-VIEW (Cedar's own recipe): two shared obligations
      -- `encode_accepted d : isValid (toStr d)` and `encode_value d : computeValue (toStr d) =
      -- some (π d)` (≙ Cedar's `toString_isWfStr` / `computeValue_toString`) plus a section fact
      -- `lift_section d : σ (π d) = d` (≙ Cedar's `Int64.ofInt_toInt`). The SAME two obligations
      -- serve the external parser (via its `complete`), so one pair drives both. Without a lift the
      -- generated parser returns β (δ = β, π = id); without a parser clause the lifted generated
      -- roundtrip closes σ-VIEW (`(computeValue (toStr d)).map σ = some d`), no π / no section.
      if let some ppStx := pp then
        if let `(fmtPrinter| printer $toStrT:term) := ppStx then
          if veIdent?.isSome || hasValueEsc then
            let cvIdent  := mkIdentFrom name (name.getId ++ `computeValue)
            let encAccId := mkIdentFrom name (name.getId ++ `encode_accepted)
            let encValId := mkIdentFrom name (name.getId ++ `encode_value)
            let secId    := mkIdentFrom name (name.getId ++ `lift_section)
            let validEng := mkIdentFrom name (name.getId ++ `isValid)
            -- The serializer's DOMAIN is the value type BOTH printer sides key on: δ when lifted,
            -- β otherwise. One helper reads it (+ a one-letter binder) straight off `toStr`.
            let (dTy, dNm) ← Triptych.serializerDomainBinder toStrT
            let dId := mkIdent dNm; let dId' := mkIdent (dNm.appendAfter "'")
            let parseId  := mkIdentFrom name (name.getId ++ `parse)
            let rtId     := mkIdentFrom name (name.getId ++ `parse_toString_roundtrip)
            let injId    := mkIdentFrom name (name.getId ++ `toString_injective)
            let normId   := mkIdentFrom name (name.getId ++ `normalize_eq_iff_parse_eq)
            -- The `parser … projection` clause supplies the projection π (: δ → β) that phrases
            -- the shared π-view `encode_value` and the section fact `lift_section : σ (π d) = d`.
            let extClause? : Option (TSyntax `term × TSyntax `term) := do
              let prStx ← pr
              match prStx with
              | `(fmtParser| parser $parseT:term projection $projT:term) => some (parseT, projT)
              | _ => none
            -- GENERATED section: the shared encode obligations live here (the external section
            -- reuses them), so the whole `encode_*`/`lift_section` + generated-parser trio is one
            -- self-contained block. `encode_accepted` (over ENGINE `isValid`) is shared by every branch.
            emitContractGen (← `(theorem $encAccId ($dId : $dTy) : $validEng ($toStrT $dId) := by sorry))
            -- Emit the shared obligations' value part + the GENERATED roundtrip, per branch.
            match liftTerm?, extClause? with
            | some σT, some (_, projT) =>
              -- LIFTED + PARSER: π-view (Cedar's recipe). `encode_value` through π, `lift_section`
              -- the section `σ (π d) = d`; generated roundtrip via `gatedParseLift_toString_roundtrip`.
              emitContractGen (← `(theorem $encValId ($dId : $dTy) :
                  $cvIdent ($toStrT $dId) = some ($projT $dId) := by sorry))
              emitContractGen (← `(theorem $secId ($dId : $dTy) : $σT ($projT $dId) = $dId := by sorry))
              emitContractGen (← `(theorem $rtId ($dId : $dTy) : $parseId ($toStrT $dId) = some $dId :=
                Triptych.gatedParseLift_toString_roundtrip $encAccId $encValId $secId $dId))
            | some σT, none =>
              -- LIFTED, NO PARSER: no π available → σ-view `encode_value`; roundtrip closes straight
              -- from `gatedParseLift_complete` (self-contained, no section fact needed).
              emitContractGen (← `(theorem $encValId ($dId : $dTy) :
                  ($cvIdent ($toStrT $dId)).map $σT = some $dId := by sorry))
              emitContractGen (← `(theorem $rtId ($dId : $dTy) : $parseId ($toStrT $dId) = some $dId :=
                Triptych.gatedParseLift_complete $validEng $cvIdent $σT ($toStrT $dId) $dId
                  ($encAccId $dId) ($encValId $dId)))
            | none, _ =>
              -- UNLIFTED: generated parser returns β (δ = β, π = id). `encode_value` is the plain
              -- `computeValue (toStr d) = some d`; roundtrip via `gatedParse_toString_roundtrip`.
              emitContractGen (← `(theorem $encValId ($dId : $dTy) :
                  $cvIdent ($toStrT $dId) = some $dId := by sorry))
              emitContractGen (← `(theorem $rtId ($dId : $dTy) : $parseId ($toStrT $dId) = some $dId :=
                Triptych.gatedParse_toString_roundtrip $validEng $cvIdent $encAccId $encValId $dId))
            -- GENERATED injectivity + normalization: generic over the roundtrip (δ-view), same for
            -- every branch.
            emitContractGen (← `(theorem $injId ($dId $dId' : $dTy) (h : $toStrT $dId = $toStrT $dId') :
                $dId = $dId' :=
              Triptych.toString_injective $rtId $dId $dId' h))
            emitContractGen (← `(theorem $normId (s s' : String) :
                ($parseId s).map $toStrT = ($parseId s').map $toStrT ↔ $parseId s = $parseId s' :=
              Triptych.normalize_eq_iff_parse_eq $rtId s s'))
            -- EXTERNAL parser (δ-view), when a `parser` clause exists: reuses the SAME `toStr` +
            -- `encode_accepted`/`encode_value` (π-view), closing roundtrip via the external
            -- `complete` — exactly Cedar's `parse_toString_roundtrip = parse_complete …`.
            match extClause? with
            | some (parseT, _) =>
              let xCompId  := mkIdentFrom name (name.getId ++ `extparse_complete)
              let xRtId    := mkIdentFrom name (name.getId ++ `extparse_toString_roundtrip)
              let xInjId   := mkIdentFrom name (name.getId ++ `extparse_toString_injective)
              let xNormId  := mkIdentFrom name (name.getId ++ `extparse_normalize_eq_iff_parse_eq)
              -- `encode_accepted` is over the ENGINE `isValid`, but the external `complete` speaks
              -- the SURFACE `IsValid`; bridge via `IsValid_equiv` (`.mpr : isValid → IsValid`).
              let equivId  := mkIdentFrom name (name.getId ++ `IsValid_equiv)
              let encAccSurf ← `(fun d => ($equivId ($toStrT d)).mpr ($encAccId d))
              emitContractExt (← `(theorem $xRtId ($dId : $dTy) : $parseT ($toStrT $dId) = some $dId :=
                Triptych.parse_toString_roundtrip $xCompId $encAccSurf $encValId $dId))
              emitContractExt (← `(theorem $xInjId ($dId $dId' : $dTy) (h : $toStrT $dId = $toStrT $dId') :
                  $dId = $dId' :=
                Triptych.toString_injective $xRtId $dId $dId' h))
              emitContractExt (← `(theorem $xNormId (s s' : String) :
                  ($parseT s).map $toStrT = ($parseT s').map $toStrT ↔ $parseT s = $parseT s' :=
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
      --   `soundness.lean`— ONLY the external-parser obligations (`sorry`d), emitted ONLY when a
      --                     `parser … projection …` clause names an existing external parser.
      --                     Imports `parser` + the caller module (the external parser lives there).
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
          let callerImport := (← getMainModule).toString
          let callerNamespace := (← getCurrNamespace).toString
          -- Module path prefix of the output dir (`Triptych/Examples/Decimal` →
          -- `Triptych.Examples.Decimal`), used to import sibling generated files.
          let dirMod := (dir.replace "/" ".").replace "\\" "."
          let specMod   := dirMod ++ ".spec"
          let parserMod := dirMod ++ ".parser"
          -- The surface `value`/`Constraints` reference caller fns for the escape tiers
          -- (`toGraph`, `dayBound`, …); the engine bundle likewise. So both `spec` and
          -- `parser` import (and `open`) the caller when an escape is present.
          let needsCallerSurface := hasOpaque || hasValueEsc
          -- `parser.lean` additionally embeds the `lift σ` term in the generated `parse`; when `σ`
          -- is a CALLER-defined fn (e.g. `millisToDuration`, not a library one like `Int64.ofInt`)
          -- it must import+open the caller too. Presence of a lift is the trigger (a library σ
          -- makes the extra import harmless — the caller module is acyclic w.r.t. the generated
          -- files, same as `soundness.lean`'s caller import).
          let needsCallerParser := needsCallerSurface || liftTerm?.isSome
          -- `unusedSimpArgs`/`unusedVariables` off — the uniform proof closer over-provisions
          -- simp lemmas by design, and some defs keep a uniform signature with an unused
          -- parameter (`SatisfiesConstraints (s) := True`); neither is a defect.
          let mkHeader (imports : List String) (openCaller : Bool) : String :=
            let importLines := String.join (imports.map (fun i => s!"import {i}\n"))
            s!"/- Generated by Triptych from `triptych {nm}`. -/\n\n\
               {importLines}\
               \nopen Triptych\n\
               {if openCaller then s!"open {callerNamespace}\n" else ""}\
               \nset_option linter.unusedSimpArgs false\n\
               set_option linter.unusedVariables false\n"
          let libImports := ["Triptych.Architecture.Denote", "Triptych.Architecture.Value",
            "Triptych.Architecture.Constraint", "Triptych.Architecture.Assemble",
            "Triptych.Theorems.Reconcile"]
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
            says the same thing. `value` is the value function, `Constraints` the extra\n\
            conditions, and `IsValid` the overall acceptance predicate (well-formed ∧\n\
            constraints). This file is proof-free — it is what you cite. -/"
          let specPath := dir ++ "/spec.lean"
          guardedWrite specPath
            (specHeader ++ "\n" ++ specBanner ++ "\n\n" ++ joinDecls specDecls ++ "\n")
          -- ── parser.lean ── engine + all auto-discharged proofs + the generated verified parser.
          let parserImports := libImports ++ [specMod]
            ++ (if needsCallerParser then [callerImport] else [])
          let parserHeader := mkHeader parserImports needsCallerParser
          let engineBanner := "/- ══════════════════════════════ engine ══════════════════════════════\n\
            The executable counterpart of the spec. `decode` walks the grammar over an input\n\
            string and returns its captured components; `computeValue` then evaluates the value\n\
            function on those captures, and `isWf`/`isValid` decide well-formedness/acceptance.\n\
            \n\
            Naming convention: CAPITALIZED `IsWf.*`/`IsValid` are the surface `Prop`s you READ\n\
            and reason about; lowercase `isWf`/`isValid` are the engine's executable deciders you\n\
            RUN (`#eval isValid s`, `#eval computeValue s`). The `equivalence` section below\n\
            proves the two describe the same language and value. -/"
          let proofBanner := "/- ════════════════════════════ equivalence ════════════════════════════\n\
            The auto-discharged guarantees relating the readable surface to the executable\n\
            engine: `IsWf_equiv` (+ its `Internal.matchesRef.*` lemmas) proves recognition\n\
            agrees, `computeValue_eq` proves the values agree, and the derived `DecidablePred`\n\
            instances make the surface predicates executable via the engine. No `sorry`. -/"
          let parserBanner := "/- ═══════════════════════════════ parser ══════════════════════════════\n\
            The generated correct-by-construction parser `parse` (= `computeValue` gated on the\n\
            decidable `isValid`) together with its guarantees — `parse_sound`, `parse_complete`,\n\
            `parse_reject` — all AUTO-DISCHARGED here. A verified parser, no `sorry`. -/"
          let parserSections : List (String × Array String) :=
            [(engineBanner, engineDecls), (proofBanner, proofDecls), (parserBanner, parserDecls)]
          let parserBody := String.intercalate "\n\n"
            (parserSections.filterMap (fun (banner, decls) =>
              if decls.isEmpty then none else some (banner ++ "\n\n" ++ joinDecls decls)))
          let parserPath := dir ++ "/parser.lean"
          guardedWrite parserPath (parserHeader ++ "\n" ++ parserBody ++ "\n")
          -- ── soundness.lean ── the `sorry`d obligations, PARTITIONED into two sections: one for
          -- the GENERATED parser (`<Name>.parse` — the shared encode obligations + its printer
          -- theorems), one for the EXTERNAL parser (the real Cedar `parse` — `extparse_*`). Written
          -- generated-first (the external printer theorems reuse the generated section's encode
          -- obligations). Written ONLY when there is at least one obligation.
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
            let soundHeader := mkHeader [parserMod, callerImport] true
            let genBanner := "/- ══════════════════════ soundness · generated parser ══════════════════════\n\
              Obligations about the GENERATED parser `parse`. The `encode_*` obligations (a\n\
              serialized value is accepted, and evaluates back to itself) are left as `sorry` — a\n\
              serializer is a choice, so its correctness is yours to prove; from them the printer\n\
              theorems (`parse_toString_roundtrip`/`toString_injective`/`normalize_eq_iff_parse_eq`)\n\
              are DISCHARGED here. These same `encode_*` obligations are reused by the external\n\
              section below. -/"
            let extBanner := "/- ══════════════════════ soundness · external parser ══════════════════════\n\
              Obligations for validating YOUR OWN external parser against this specification:\n\
              `extparse_sound`, `extparse_complete`, and `extparse_reject`, stated over the readable\n\
              surface `IsValid`/`computeValue`. These are left as `sorry` — they are claims about\n\
              your parser, so you have to prove them yourself. Given them, the external printer\n\
              theorems (`extparse_toString_*`) are DISCHARGED, reusing the generated section's\n\
              `encode_*`. -/"
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

── value ──  (optional; `Int`-valued, over the captured components)
  literals:  123        Int64.MAX        Int64.MIN
  readers on a capture X (X = a production name; see CAPTURE RULE above):
    nat X    unsigned decimal value        int X    signed (leading '-')
    len X    character length              X        ±1 sign of a `sign` capture (bare name)
  a BARE capture name reads its sign — valid only when `X ::= sign`; the checker rejects a bare
  ref to a non-sign capture, and `nat/int/len` OF a sign capture.
  arithmetic:  a + b    a - b    a * b    a ^ b    ( … )    (prec: ^ > * > +/-)
  lift <σ>   (optional trailing sub-clause)  σ : Int → δ lifts the GENERATED parser's output
             to the domain type δ (so `parse : String → Option δ`); with a
             `parser … projection π` clause, σ is π's section (`σ ∘ π = id`, the emitted
             `lift_section` obligation) and π∘σ = id on accepted values (the emitted
             `lift_faithful` obligation — provable exactly when the constraints pin the
             accepted values inside σ's faithful domain, e.g. `value ∈ [Int64.MIN, Int64.MAX]`
             for a wrapping σ like `Int64.ofInt`; a missing range constraint makes it
             unprovable, surfacing the silent-wrap trap). A lint warns when `lift` appears
             with no value constraint at all.

── value' ──  (optional ESCAPE, for values outside the DSL, e.g. calendar math)
  value' f X Y …   with  def f (x y … : String) : Int := …    (`f` applied to captures)

── constraints ──  (optional; one per line; may refer to `value`)
  string (fold into IsWf):
    noLeadingZero X        X has no leading zero unless it is exactly \"0\"
    X = \"lit\"              X's matched string equals a literal
  cardinality over presence (how many of the listed captures are nonempty; SAT-style):
    nonempty X             X is present            (= atLeast 1 {X})
    atLeast k {X, Y, …}    ≥ k of the capture set present
    atMost  k {X, Y, …}    ≤ k present
    exactly k {X, Y, …}    exactly k present
  value (fold into SatisfiesConstraints):
    a ≤ b     a < b     a == b        comparisons of value expressions
    e ∈ [lo, hi]                      closed interval (⟺ lo ≤ e ∧ e ≤ hi)
  the word `value` inside a constraint = the elaborated value function.

── constraints' ──  (optional ESCAPE, for constraints outside the DSL, e.g. calendar rules)
  one per line:  f X Y …   with  def f (x y … : String) : Bool := …   (`f` applied to captures)

── parser ──  (optional)  parser <parse> projection <π>   emits the external-parser obligations
                          (π : δ → β reads the external parser's value into the spec value type).
── printer ── (optional; needs value)  printer <toString>   names your canonical serializer over
                          the DOMAIN type δ (what the parsers return); emits the encode
                          obligations + auto-derives roundtrip/injective/normalize for the
                          GENERATED parser, and (if a `parser` clause is present) the same trio
                          for the EXTERNAL parser — both in δ-view `parse (toStr d) = some d`.
── to ──      (optional)  to \"<dir>\"                        writes <dir>/{spec,parser,soundness}.lean.
                          spec/parser are regenerated every elaboration; soundness is a
                          WRITE-ONCE scaffold (it holds your proofs) — delete it to re-scaffold.
                          A pre-existing spec/parser file NOT generated by this tool (no
                          `/- Generated by Triptych` header) is never overwritten — hard error.

Section order:  grammar · value · value' · constraints · constraints' · parser · printer · to
(`lift` nests inside `value`, as `projection` nests inside `parser`).
When a format needs something not listed here, that is a signal to either (a) use the
matching escape section (`value'` / `constraints'`) for that one piece, or (b) request the
vocabulary be extended — not to hand-write the whole spec in Lean."
  logInfo help

end Triptych
