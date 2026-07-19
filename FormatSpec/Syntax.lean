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
import FormatSpec.Grammar
import FormatSpec.Classify
import FormatSpec.Value
import FormatSpec.Constraint
import FormatSpec.Assemble
import FormatSpec.Emit

/-!
# `format_spec` embedded DSL

Surface syntax for flat non-recursive attribute grammars, transcribing the `::=`
grammars written in `doc/CedarDoc/*.lean`. Lean's own `syntax`/`declare_syntax_cat`
framework does all the *parsing* of the notation; this module declares the notation
and elaborates the resulting `Syntax` tree into the generated declarations.

The command has three sections (see design note §16.3), in order:

```
format_spec Decimal where
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
  `FormatSpec.Grammar` value bound to `<Name>.grammar`. `grammar` is used rather than
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

namespace FormatSpec

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

/-- The optional `value` section: the value-DSL formula (`valExpr`); analyzable, `value(X)=…`. -/
syntax fmtValue := "value" valExpr

/-- The optional `value'` ESCAPE section (design note §16.4/§16.7): a value outside the DSL
    vocabulary, an `f X Y …` call with `f : String → … → Int`. Same shape/contract as
    `constraints'` (no `Env`); the prime marks "the raw-Lean escape of the `value` section". -/
syntax fmtValueEsc := "value'" fmtEscEntry

/-- The optional `parser` clause: names the external hand-written parser and the
    projection reading its value's `Int` denotation back out. When present, the command
    emits the contract theorem *obligations* (`<Name>.sound`/`.complete`/`.reject`) as
    `sorry`d theorems relating that parser to the generated spec. -/
syntax fmtParser := "parser" term " projection " term

/-- Optional trailing clause: `to "<dir>"` writes the generated module to `<dir>/spec.lean`
    (default dir `.`; the directory must already exist). -/
syntax fmtTo := "to " str

/-- The `format_spec` command, sections in order: `grammar` (required), `value`
    (optional), `constraints` (optional), `parser` (optional), `to` (optional). `value`
    precedes `constraints` so a constraint can refer to `value`. The `parser` clause emits
    the sorried contract theorems; the `to "<dir>"` clause writes the generated module to
    `<dir>/spec.lean` (in addition to elaborating everything). `#show` logs each declaration. -/
syntax (name := formatSpecCmd)
  ("#show ")? "format_spec " ident " where "
    "grammar" (colGt fmtProd)+
    (fmtValue)?
    (fmtValueEsc)?
    (fmtConstraints)?
    (fmtConstraintsEsc)?
    (fmtParser)?
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
-- (`Sym.lit`, `Production.mk`, …). The generated file `open`s `FormatSpec`, so these
-- resolve there and read cleanly; within this module `open Lean Elab Command` + the
-- enclosing `namespace FormatSpec` also make them resolve.
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

/-- Elaborate an item into a `SymItem` term, setting `optional` for `[…]`. -/
def elabItem : TSyntax `fmtItem → CommandElabM (TSyntax `term)
  | `(fmtItem| [ $inner:fmtItem ]) => do
      `(SymItem.mk $(← elabSym inner) true)
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
    the inlined-predicate synthesizer (`FormatSpec.prodPred`, `topoOrder`) can run at
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

/-- Elaborate the `format_spec` command: generates + elaborates the declarations, tagged
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
@[command_elab formatSpecCmd]
def elabFormatSpec : CommandElab := fun stx => do
  match stx with
  | `($[#show%$sh]? format_spec $name:ident where grammar $prods:fmtProd* $[$v:fmtValue]? $[$ve:fmtValueEsc]? $[$cs:fmtConstraints]? $[$cse:fmtConstraintsEsc]? $[$pr:fmtParser]? $[$to?:fmtTo]?) => do
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
      let bufC ← IO.mkRef (#[] : Array String)   -- external-parser obligations (→ soundness file)
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
      let emitContract (cmd : TSyntax `command) : CommandElabM Unit := do record bufC cmd; elabCommand cmd
      -- Grammar data literal (SPEC): the auditable EBNF transcription; the interpreter,
      -- proofs, and `SatisfiesConstraints`'s decode bridge all reference it. The START symbol
      -- is the FIRST production's name (NOT the `format_spec` display name — they may differ,
      -- e.g. `format_spec IPv4` whose first production is `V4Addr`); it must name a real
      -- production so `grammar.prod? grammar.start` resolves.
      let prodVals ← prods.toList.mapM parseProd
      let startName := (prodVals.head?.map (·.name)).getD name.getId.toString
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
      let gval : FormatSpec.Grammar :=
        { start := startName, prods := prodVals }
      for prod in FormatSpec.topoOrder gval do
        let pIdent := mkIdentFrom name (name.getId ++ `IsWf ++ prod.name.toName)
        let sVar ← `(s)
        let body ← FormatSpec.prodPred name.getId prod sVar
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
        for prod in FormatSpec.topoOrder gval do
          let depth := FormatSpec.subtreeDepth gval prod.name fuelBound
          emitSound (← FormatSpec.matchesRefProof name.getId grammarIdent prod depth)
        if let some startProd := gval.prods.find? (·.name == gval.start) then
          emitSound (← FormatSpec.isWfEquivProof name.getId grammarIdent startProd)
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
                        @decidable_of_iff _ _ ($equivId s) (FormatSpec.decIsWf $grammarIdent (by decide) s)))
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
          emitSound (← FormatSpec.isValidEquivProof name.getId hasConstraints hasValue)
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
        let vfnIdent := mkIdentFrom name (name.getId ++ `valueFn)
        -- engine: the analyzable AST + its eval
        let valTerm ← liftMacroM (elabValExpr ve)
        let veIdent := mkIdentFrom name (name.getId ++ `valueExpr)
        emitEngine (← `(def $veIdent : ValExpr := $valTerm))
        emitEngine (← `(def $vfnIdent : Env → Int := ($veIdent).eval))
        -- spec: a READABLE `<Name>.value` taking the captured component STRINGS directly
        -- (no `Env`), via `natOf`/`intOf`/… — reads like `value(Integer, Fraction) = …`.
        let readable ← liftMacroM (elabValReadableWith none ve)
        let capNames := FormatSpec.valExprCaptures ve
        let binders : Array (TSyntax `ident) :=
          (capNames.map (fun c => mkIdent (Name.mkSimple (FormatSpec.surfaceBinder c)))).toArray
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
          emitEngine (← `(def $vfnIdent := $(← liftMacroM (FormatSpec.opaqueEnvClosure f is))))
          -- spec: a READABLE `<Name>.value` — the author's call over the surface string binders
          -- (return type inferred from `f`, likewise not pinned to `Int`).
          let capNames := is.toList.map (·.getId.toString)
          let binders : Array (TSyntax `ident) :=
            (capNames.map (fun c => mkIdent (Name.mkSimple (FormatSpec.surfaceBinder c)))).toArray
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
          `(ConstraintEntry.opaque $(← liftMacroM (FormatSpec.opaqueEnvClosure f is))))
        let csep : Syntax.TSepArray `term "," := .ofElems (dslTerms ++ escTerms)
        emitEngine (← `(def $cIdent : List ConstraintEntry := [$csep,*]))
        -- SPEC `Constraints` Prop: DSL forms rendered readably ++ each escape as `f x y = true`
        -- over the surface binders. A `value` reference renders as `<Name>.value <comps>`.
        let valSubR : Option (TSyntax `term) ← match veIdent? with
          | some _ =>
            let vId := mkIdentFrom name (name.getId ++ `value)
            let vArgs : Array (TSyntax `term) :=
              (valueCaps.map (fun c => ⟨(mkIdent (Name.mkSimple (FormatSpec.surfaceBinder c))).raw⟩)).toArray
            pure (some (← `($vId $vArgs*)))
          | none   => pure none
        let dslRTerms ← dslExprs.mapM (fun e => liftMacroM (elabConstraintReadable valSubR e))
        let escRTerms ← escEntries.mapM (fun (f, is) => do
          let bArgs : Array (TSyntax `term) := is.map (fun i =>
            ⟨(mkIdent (Name.mkSimple (FormatSpec.surfaceBinder i.getId.toString))).raw⟩)
          `($f $bArgs* = true))
        let allR := dslRTerms ++ escRTerms
        let body ← match allR.toList with
          | []      => `(True)
          | x :: xs => xs.foldlM (fun acc p => `($acc ∧ $p)) x
        -- capture params: DSL captures ∪ escape captures ∪ value captures (if `value` used)
        let usesValue := dslExprs.any (fun e => (FormatSpec.constraintUsesValue e))
        let escCaps := escEntries.toList.flatMap (fun (_, is) => is.toList.map (·.getId.toString))
        let cCaps := (dslExprs.toList.flatMap FormatSpec.constraintCaptures ++ escCaps
                        ++ (if usesValue then valueCaps else [])).eraseDups
        let cBinders : Array (TSyntax `ident) :=
          (cCaps.map (fun c => mkIdent (Name.mkSimple (FormatSpec.surfaceBinder c)))).toArray
        let cRIdent := mkIdentFrom name (name.getId ++ `Constraints)
        emitSpec (← `(def $cRIdent $[($cBinders : String)]* : Prop := $body))
        constrCaps := some cCaps
      else
        emitEngine (← `(def $cIdent : List ConstraintEntry := []))
      -- ENGINE bundle (lowercase): the decode-backed interpreter predicates. The readable
      -- surface `IsWf.<start>` is PROVEN equal to `FormatSpec.isWf` by `<Name>.IsWf_equiv`.
      let wfIdent  := mkIdentFrom name (name.getId ++ `isWf)
      let scIdent  := mkIdentFrom name (name.getId ++ `satisfiesConstraints)
      let accIdent := mkIdentFrom name (name.getId ++ `isValid)
      emitEngine (← `(abbrev $wfIdent  (s : String) : Prop := FormatSpec.isWf $grammarIdent $cIdent s))
      emitEngine (← `(abbrev $scIdent  (s : String) : Prop := FormatSpec.satisfiesConstraints $grammarIdent $cIdent s))
      emitEngine (← `(abbrev $accIdent (s : String) : Prop := $wfIdent s ∧ $scIdent s))
      if let some veIdent := veIdent? then
        -- DSL tier: `computeValue` via the analyzable `ValExpr` (Int-valued).
        let cvIdent := mkIdentFrom name (name.getId ++ `computeValue)
        emitEngine (← `(def $cvIdent (s : String) : Option Int :=
                      FormatSpec.computeValue $grammarIdent $veIdent s))
      else if hasValueEsc then
        -- ESCAPE tier: `computeValue` via `computeValueF` and the author's `valueFn` — the
        -- value type is arbitrary (inferred from `valueFn`), so this parses to whatever
        -- structured value `value'` produces (`Option SimpleGraph`, `Option (Matrix …)`, …).
        let cvIdent := mkIdentFrom name (name.getId ++ `computeValue)
        let vfnIdent := mkIdentFrom name (name.getId ++ `valueFn)
        emitEngine (← `(def $cvIdent (s : String) :=
                      FormatSpec.computeValueF $grammarIdent $vfnIdent s))
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
          `(FormatSpec.component $grammarIdent s $(Syntax.mkStrLit c)))
        emitSpec (← `(def $scSurf (s : String) : Prop := $cRIdent $args*))
      emitSpec (← `(abbrev $accSurf (s : String) : Prop := $startIsWf s ∧ $scSurf s))
      -- Soundness/decidability (SOUNDNESS section): the surface⟺engine `IsWf_equiv` + the
      -- derived `Decidable` instances. Runs after the engine bundle + surface `IsValid`.
      emitReconcile constrCaps.isSome veIdent?.isSome
      -- VALUE equivalence (SOUNDNESS section): surface `value` ⟺ engine `computeValue`, as a
      -- standalone theorem (the value analogue of `IsWf_equiv`). Emitted whenever a value
      -- section is present — DSL tier (`veIdent?`) or `value'` escape (`hasValueEsc`).
      if veIdent?.isSome || hasValueEsc then
        emitSound (← FormatSpec.computeValueEqProof name.getId grammarIdent valueCaps veIdent?.isSome)
      -- GENERATED VERIFIED PARSER (→ parser file): whenever a value section exists, emit the
      -- tool's own `<Name>.parse := gatedParse isValid computeValue` and its three
      -- AUTO-DISCHARGED contracts (`parse_sound`/`parse_complete`/`parse_reject`). Gated on the
      -- engine `isValid` (structurally decidable), so the parser is self-contained relative to
      -- the engine — no `sorry`. This is the correct-by-construction parser; the external
      -- obligations below are the SEPARATE translation-validation surface.
      if veIdent?.isSome || hasValueEsc then
        for cmd in ← FormatSpec.parserContractsProof name.getId veIdent?.isSome do
          emitParser cmd
      -- EXTERNAL-PARSER obligations (→ soundness file): with a `parser <p> projection <π>`
      -- clause naming an EXISTING external parser, emit `<Name>.sound`/`.complete`/`.reject` as
      -- `sorry`d theorems (design §16.1), stated over the SURFACE `<Name>.IsValid`/
      -- `computeValue` — the human-facing "the real parser accepts iff the readable spec is
      -- valid, with matching value". These are the ONLY obligations left to the human; they
      -- reference the external parser, so the soundness file re-imports the caller module.
      if let some prStx := pr then
        if let `(fmtParser| parser $parseT:term projection $projT:term) := prStx then
          let rejIdent := mkIdentFrom name (name.getId ++ `reject_ext)
          emitContract (← `(theorem $rejIdent :
              RejectStmt $accSurf $parseT := by sorry))
          -- `sound`/`complete` need a value function — emitted whenever a `value` OR `value'`
          -- section is present (both produce `<Name>.computeValue`; the escape tier's value
          -- type is arbitrary, matched by the `projection`'s codomain).
          if veIdent?.isSome || hasValueEsc then
            let cvIdent := mkIdentFrom name (name.getId ++ `computeValue)
            let soundIdent := mkIdentFrom name (name.getId ++ `sound_ext)
            let compIdent  := mkIdentFrom name (name.getId ++ `complete_ext)
            emitContract (← `(theorem $soundIdent :
                SoundStmt $accSurf $cvIdent $parseT $projT := by sorry))
            emitContract (← `(theorem $compIdent :
                CompleteStmt $accSurf $cvIdent $parseT $projT := by sorry))
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
      -- Splitting by file (vs the old single module) gives each a crisp contract; the
      -- dependency chain spec ← parser ← soundness is acyclic.
      if let some toStx := to? then
        if let `(fmtTo| to $dirStx:str) := toStx then
          let nm := name.getId.toString
          let dir := dirStx.getString
          let specDecls ← bufS.get; let engineDecls ← bufE.get
          let proofDecls ← bufP.get; let parserDecls ← bufR.get
          let contractDecls ← bufC.get
          let callerImport := (← getMainModule).toString
          let callerNamespace := (← getCurrNamespace).toString
          -- Module path prefix of the output dir (`FormatSpec/Examples/Decimal` →
          -- `FormatSpec.Examples.Decimal`), used to import sibling generated files.
          let dirMod := (dir.replace "/" ".").replace "\\" "."
          let specMod   := dirMod ++ ".spec"
          let parserMod := dirMod ++ ".parser"
          -- The surface `value`/`Constraints` reference caller fns for the escape tiers
          -- (`toGraph`, `dayBound`, …); the engine bundle likewise. So both `spec` and
          -- `parser` import (and `open`) the caller when an escape is present.
          let needsCallerSurface := hasOpaque || hasValueEsc
          -- `unusedSimpArgs`/`unusedVariables` off — the uniform proof closer over-provisions
          -- simp lemmas by design, and some defs keep a uniform signature with an unused
          -- parameter (`SatisfiesConstraints (s) := True`); neither is a defect.
          let mkHeader (imports : List String) (openCaller : Bool) : String :=
            let importLines := String.join (imports.map (fun i => s!"import {i}\n"))
            s!"-- Generated by FormatSpec from `format_spec {nm}`. Do not edit by hand.\n\n\
               {importLines}\
               \nopen FormatSpec\n\
               {if openCaller then s!"open {callerNamespace}\n" else ""}\
               \nset_option linter.unusedSimpArgs false\n\
               set_option linter.unusedVariables false\n"
          let libImports := ["FormatSpec.Denote", "FormatSpec.Value", "FormatSpec.Constraint",
            "FormatSpec.Assemble", "FormatSpec.Reconcile"]
          let joinDecls (decls : Array String) : String :=
            String.intercalate "\n\n" decls.toList
          -- ── spec.lean ── the readable surface only.
          let specHeader := mkHeader
            (libImports ++ (if needsCallerSurface then [callerImport] else []))
            needsCallerSurface
          let specBanner := "-- ═══════════════════════════════ spec ═══════════════════════════════\n\
            -- The reader-facing specification: the grammar, the readable per-production\n\
            -- well-formedness predicates `IsWf.*`, the `value` function, the `Constraints`,\n\
            -- and the acceptance predicates `SatisfiesConstraints` / `IsValid` (a string is\n\
            -- VALID iff it satisfies the grammar and constraints — Cedar's wording)."
          let specPath := dir ++ "/spec.lean"
          IO.FS.writeFile specPath
            (specHeader ++ "\n" ++ specBanner ++ "\n\n" ++ joinDecls specDecls ++ "\n")
          -- ── parser.lean ── engine + all auto-discharged proofs + the generated verified parser.
          let parserImports := libImports ++ [specMod]
            ++ (if needsCallerSurface then [callerImport] else [])
          let parserHeader := mkHeader parserImports needsCallerSurface
          let engineBanner := "-- ══════════════════════════════ engine ══════════════════════════════\n\
            -- The analyzable/executable machinery behind the spec: the deep-embedded\n\
            -- value/constraint ASTs and the decode-backed interpreter bundle (`isWf`,\n\
            -- `isValid`, `computeValue`)."
          let proofBanner := "-- ════════════════════════════ soundness ════════════════════════════\n\
            -- The auto-discharged guarantees tying surface to engine: `IsWf_equiv` (+ its\n\
            -- `Internal.matchesRef.*` lemmas), `computeValue_eq`, and the derived\n\
            -- `DecidablePred` instances (an executable validator, via the interpreter)."
          let parserBanner := "-- ═══════════════════════════════ parser ══════════════════════════════\n\
            -- The generated correct-by-construction parser `parse` (= `computeValue` gated on\n\
            -- the decidable `isValid`) and its AUTO-DISCHARGED contracts `parse_sound` /\n\
            -- `parse_complete` / `parse_reject`. A verified parser, no `sorry`."
          let parserSections : List (String × Array String) :=
            [(engineBanner, engineDecls), (proofBanner, proofDecls), (parserBanner, parserDecls)]
          let parserBody := String.intercalate "\n\n"
            (parserSections.filterMap (fun (banner, decls) =>
              if decls.isEmpty then none else some (banner ++ "\n\n" ++ joinDecls decls)))
          let parserPath := dir ++ "/parser.lean"
          IO.FS.writeFile parserPath (parserHeader ++ "\n" ++ parserBody ++ "\n")
          -- ── soundness.lean ── external-parser obligations only; written ONLY when present.
          if !contractDecls.isEmpty then
            let soundHeader := mkHeader [parserMod, callerImport] true
            let contractBanner := "-- ═══════════════════════════ soundness ═══════════════════════════\n\
              -- The parser-correctness OBLIGATIONS for the external, hand-written parser, stated\n\
              -- over the SURFACE `IsValid`/`computeValue` (`sorry`d — the ONLY proofs left to the\n\
              -- human; discharge by bridging `IsValid` to `decode` via `IsWf_equiv`)."
            let soundPath := dir ++ "/soundness.lean"
            IO.FS.writeFile soundPath
              (soundHeader ++ "\n" ++ contractBanner ++ "\n\n" ++ joinDecls contractDecls ++ "\n")
          let filesWritten := "spec.lean, parser.lean" ++
            (if contractDecls.isEmpty then "" else ", soundness.lean")
          logInfo m!"FormatSpec: wrote {nm} → {dir}/ [{filesWritten}] \
                     ({specDecls.size} spec + {engineDecls.size} engine + {proofDecls.size} proof + \
                     {parserDecls.size} verified-parser + {contractDecls.size} obligation decls)"
          -- CAVEAT: this write is an elaboration side-effect. `lake` replays cached modules
          -- without re-running IO, so the files refresh only on a genuine cache miss — after
          -- editing the generator, force a rebuild (delete oleans or `lake clean`).
  | _ => throwUnsupportedSyntax

/-! ## `#format_spec_help` — discoverable DSL vocabulary

Prints the full grammar / value / constraint DSL vocabulary so a user can see what is
expressible *before* reaching for the raw-Lean `opaque` escape hatch. The escape is the
LAST resort (it makes the value/constraint opaque to the analysis — no auto-affinity, and
its correctness is on the author); this reference exists so that fallback is a deliberate
choice, not a default taken for lack of knowing the vocabulary. -/
syntax (name := formatSpecHelpCmd) "#format_spec_help" : command

@[command_elab formatSpecHelpCmd]
def elabFormatSpecHelp : CommandElab := fun _ => do
  let help : String := "\
FormatSpec DSL — the vocabulary of `format_spec <Name> where …`.
Prefer these forms; the `opaque` escapes are a LAST resort (they hide the value/constraint
from analysis and put correctness on you).

── grammar ──  (required; a flat non-recursive DAG of `::=` productions)
  Name ::= item item … | alt | …     one or more `|`-separated alternatives
  item forms:
    \"lit\"                            a string literal (separators, unit tags)
    Nonterminal                      a reference to another production (the DAG edge)
    digit<len> / hexDigit<len>       a terminal token run
    [ item ]                         optional
  <len> suffix:  +  (one-or-more)   {n}  (exactly n)   {lo,hi}  (between)

── value ──  (optional; `Int`-valued, over the captured components)
  literals:  123        Int64.MAX        Int64.MIN
  readers on a capture X:
    nat X    unsigned decimal value        int X    signed (leading '-')
    len X    character length              sign X   -1 if X starts '-', else +1
  arithmetic:  a + b    a - b    a * b    a ^ b    ( … )    (prec: ^ > * > +/-)

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

── parser ──  (optional)  parser <parse> projection <π>   emits the contract obligations.
── to ──      (optional)  to \"<dir>\"                        writes <dir>/spec.lean.

Section order:  grammar · value · value' · constraints · constraints' · parser · to.
When a format needs something not listed here, that is a signal to either (a) use the
matching escape section (`value'` / `constraints'`) for that one piece, or (b) request the
vocabulary be extended — not to hand-write the whole spec in Lean."
  logInfo help

end FormatSpec
