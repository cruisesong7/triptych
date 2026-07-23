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
import Triptych.Architecture.Denote
import Triptych.Theorems.Reconcile
import Triptych.Architecture.Value

/-!
# Inlined per-production predicate synthesis

Generates *readable, inlined* well-formedness predicates per production — the `∃ …, s =
p0 ++ p1 ++ … ∧ …` structural form that reads like the hand-written specs
(`doc/CedarDoc/*.lean`), instead of an opaque `IsWfProd grammar "Name"` interpreter call.

The synthesized predicate mirrors the `Denote` denotation exactly (`matchesSeq` /
`matchesProd`), with nonterminal references resolved to sibling predicate *names*
(`<Name>.isWf.<Prod>`). This eliminates the fuel/interpreter indirection: the DAG is
unrolled into named defs emitted in topological (leaf-first) order.
-/

namespace Triptych

open Lean Elab Command

/-- Render a natural number as Unicode subscript digits (`1 ↦ "₁"`, `12 ↦ "₁₂"`), for
    readable disambiguating suffixes on generated binder names (`rest₁`, `rest₂`, …). -/
def subscript (n : Nat) : String :=
  let subs := "₀₁₂₃₄₅₆₇₈₉".toList
  String.ofList ((toString n).toList.map (fun c => subs[(c.toNat - '0'.toNat)]!))

/-- The readable leaf predicate for a `term tok len`, matching the hand specs'
    vocabulary (`IsDigits`, `IsFixedDigits`, …). Names are emitted UNQUALIFIED (the
    generated file `open`s `Triptych`), so they read like the doc. -/
def termPred (tok : TokClass) (ls : LenSpec) (v : TSyntax `term) : CommandElabM (TSyntax `term) :=
  match tok, ls with
  | .digit,    .atLeastOne    => `(IsDigits $v)
  | .hexDigit, .atLeastOne    => `(IsHexDigits $v)
  | .bit,      .atLeastOne    => `(IsBits $v)
  | .digit,    .exactly n     => `(IsFixedDigits $(quote n) $v)
  | .hexDigit, .exactly n     => `(IsFixedHexDigits $(quote n) $v)
  | .bit,      .exactly n     => `(IsFixedBits $(quote n) $v)
  | .digit,    .between lo hi => `(IsDigitsBetween $(quote lo) $(quote hi) $v)
  | .hexDigit, .between lo hi => `(IsHexDigitsBetween $(quote lo) $(quote hi) $v)
  | .bit,      .between lo hi => `(IsBitsBetween $(quote lo) $(quote hi) $v)

/-- Predicate that string `v` matches symbol `sym`. Refs resolve to the sibling
    per-production predicate `<specName>.IsWf.<Nt>`. -/
partial def symPred (specName : Name) : Sym → (v : TSyntax `term) → CommandElabM (TSyntax `term)
  | .lit l,       v => `($v = $(Syntax.mkStrLit l))
  | .term tok ls, v => termPred tok ls v
  | .ref nm,      v => do
      -- resolve to the sibling per-production predicate `<specName>.IsWf.<Nt>` (the
      -- capital-`I` Prop = the readable surface spec; cf. the bundle's lowercase `isWf`)
      let refId := mkIdent (specName ++ `IsWf ++ nm.toName)
      `($refId $v)
  | .rep sep item lo hi, v => do
      -- separated repetition reads as its `matchesRep` surface form: some `parts` list,
      -- each satisfying the item predicate, joined by `sep`, with count within `[lo,hi]`.
      let itemPred ← symPred specName item (← `(p))
      let loT := Syntax.mkNatLit lo
      let hiBound ← match hi with
        | none   => `(True)
        | some h => `(parts.length ≤ $(Syntax.mkNatLit h))
      `(∃ parts : List String,
          $loT ≤ parts.length ∧ $hiBound
            ∧ (∀ p ∈ parts, $itemPred) ∧ $v = String.intercalate $(Syntax.mkStrLit sep) parts)

/-- Nonterminal name → its `∃`-binder in the inlined predicates. Shares `surfaceBinder`
    (from `Value`) so the well-formedness binders match the value/constraint parameter names
    exactly: CamelCase lowers the first char (`Integer` → `integer`), an all-caps acronym
    lowers fully (`YYYY` → `yyyy`, not `yYYY`). -/
private def deCap (s : String) : String := surfaceBinder s

/-- Base binder name for a capturing symbol; `none` for a literal (no binder). -/
private def binderBase : Sym → Option String
  | .lit _      => none
  | .ref nm     => some (deCap nm)
  | .term _ _   => some "digits"
  | .rep _ item _ _ => (binderBase item).map (· ++ "s")  -- a list of the items ("groups")

/-- Assign a readable, unique binder name to each capturing item (literals → `none`).
    Names come from the nonterminal (`Integer` → `integer`); duplicates within one
    sequence are disambiguated with a numeric suffix (`group0`, `group1`, …). -/
private def assignBinders (items : List SymItem) : List (Option String) := Id.run do
  let bases := items.map (binderBase ·.sym)
  -- how many times each base occurs
  let mut counts : Std.HashMap String Nat := {}
  for b in bases do
    if let some nm := b then counts := counts.insert nm ((counts.getD nm 0) + 1)
  -- assign, suffixing only when a base is duplicated
  let mut seen : Std.HashMap String Nat := {}
  let mut out : List (Option String) := []
  for b in bases do
    match b with
    | none    => out := out ++ [none]
    | some nm =>
      if (counts.getD nm 1) == 1 then
        out := out ++ [some nm]
      else
        let idx := seen.getD nm 0
        seen := seen.insert nm (idx + 1)
        out := out ++ [some s!"{nm}{idx}"]
  return out

/-- Build `∃ x₁ x₂ … xₙ, body` as a SINGLE existential binding all `binders` at once
    (`∃ a b c, P`), rather than nested `∃ a, ∃ b, ∃ c, P`. Reads the same but keeps the
    term flatter, which makes the reconciliation proof's existential handling easier
    (fewer `∃`-intro/elim layers). Empty `binders` ⟹ `body` unchanged. -/
def mkExists (binders : List (TSyntax `ident)) (body : TSyntax `term) :
    CommandElabM (TSyntax `term) := do
  match binders with
  | []      => pure body
  | _ =>
    -- `∃`'s antiquotation splat expects `explicitBinders`; build one node holding all the
    -- idents (an `unbracketedExplicitBinders` with no type ascription).
    let bis ← binders.toArray.mapM (fun id => `(Lean.binderIdent| $id:ident))
    let ueb ← `(Lean.unbracketedExplicitBinders| $bis*)
    let eb ← `(Lean.explicitBinders| $ueb:unbracketedExplicitBinders)
    `(∃ $eb, $body)

/-- Predicate that string `whole` matches a NON-optional sequence, in the flat form that
    reads like the hand spec: bind one variable per capture (named from the grammar),
    literals inline in the concatenation.
      `∃ integer fraction, whole = integer ++ "." ++ fraction ∧ P integer ∧ Q fraction`
    A single lone capture needs no `∃` (`P whole` directly). -/
def seqPredFlat (specName : Name) (whole : TSyntax `term) (items : List SymItem) :
    CommandElabM (TSyntax `term) := do
  let names := assignBinders items
  -- single lone capture: apply its predicate directly to `whole`, no existential.
  match items, names with
  | [it], [some _] => symPred specName it.sym whole
  | _, _ => do
    -- concatenation pieces: literal string for lits, binder var for captures
    let mut concatPieces : List (TSyntax `term) := []
    let mut binders : List (TSyntax `ident) := []
    let mut preds : List (TSyntax `term) := []
    for (it, nm?) in items.zip names do
      match nm? with
      | none =>
        if let .lit l := it.sym then concatPieces := concatPieces ++ [← `($(Syntax.mkStrLit l))]
      | some nm =>
        let id := mkIdent (Name.mkSimple nm)
        let idTm : TSyntax `term := ⟨id.raw⟩
        binders := binders ++ [id]
        concatPieces := concatPieces ++ [idTm]
        preds := preds ++ [← symPred specName it.sym idTm]
    let concat ← match concatPieces with
      | []      => `("")
      | x :: xs => xs.foldlM (fun acc y => `($acc ++ $y)) x
    let eqp ← `($whole = $concat)
    let body ← preds.foldlM (fun acc p => `($acc ∧ $p)) eqp
    mkExists binders body

/-- Peel a single item off the front of `whole`, then recurse on `rest`.
    * a LITERAL is inlined into the equation with no binder (`whole = "-" ++ tl ∧ …`),
      matching the hand spec's `∃ t, s = "-" ++ t ∧ …`;
    * a CAPTURE binds a variable named after the nonterminal.
    The trailing `rest` binder is named `rest` (or `rest2`, … at deeper peels).
    A trailing empty sequence closes with the tail predicate directly (no `= ""`). -/
partial def seqPeel (specName : Name) (whole : TSyntax `term)
    (items : List SymItem) (depth : Nat) : CommandElabM (TSyntax `term) := do
  match items with
  | []           => `($whole = "")
  | [item] =>
    -- last item: it must consume all of `whole` (no fresh rest binder needed)
    if item.optional then
      let hd ← symPred specName item.sym whole
      `($hd ∨ $whole = "")
    else
      symPred specName item.sym whole
  | item :: rest =>
    -- first remainder is `rest`, then `rest₁`, `rest₂`, … (Unicode subscripts)
    let restName := if depth == 0 then "rest" else s!"rest{subscript depth}"
    let rst   := mkIdent (Name.mkSimple restName)
    let rstTm : TSyntax `term := ⟨rst.raw⟩
    let tl ← seqPeel specName rstTm rest (depth + 1)
    let mkPresent : CommandElabM (TSyntax `term) := do
      match item.sym, binderBase item.sym with
      | .lit l, _ =>              -- literal: inline, bind only the rest
        `(∃ $rst:ident, $whole = $(Syntax.mkStrLit l) ++ $rstTm ∧ $tl)
      | sym, some base =>          -- capture: bind a named var + the rest
        let p   := mkIdent (Name.mkSimple base)
        let pTm : TSyntax `term := ⟨p.raw⟩
        let hd ← symPred specName sym pTm
        `(∃ $p:ident $rst:ident, $whole = $pTm ++ $rstTm ∧ $hd ∧ $tl)
      | sym, none =>               -- (unreachable: only lits have no base)
        let p   := mkIdent (Name.mkSimple "piece")
        let pTm : TSyntax `term := ⟨p.raw⟩
        let hd ← symPred specName sym pTm
        `(∃ $p:ident $rst:ident, $whole = $pTm ++ $rstTm ∧ $hd ∧ $tl)
    if item.optional then
      let present ← mkPresent
      let absent ← seqPeel specName whole rest (depth + 1)
      `($present ∨ $absent)
    else
      mkPresent

/-- A sequence of ALL-optional captures (e.g. `[Days][Hours][Minutes][Seconds][Millis]`).
    The peel form would produce a combinatorial `present ∨ absent` tree; instead emit the
    flat, linear form — bind one piece per component, concatenated in order, each piece
    "empty or well-formed":
      `∃ days hours …, whole = days ++ hours ++ … ∧ (days = "" ∨ IsWf.Days days) ∧ …`
    This reads like the doc's one-line `[Days][Hours]…` and is O(n), not O(2ⁿ). -/
def seqAllOptional (specName : Name) (whole : TSyntax `term) (items : List SymItem) :
    CommandElabM (TSyntax `term) := do
  let names := assignBinders items          -- every item is a capture ⟹ all `some`
  let binders : List (TSyntax `ident) := names.filterMap (·.map (mkIdent ∘ Name.mkSimple))
  let binderTms : List (TSyntax `term) := binders.map (fun i => ⟨i.raw⟩)
  let concat ← match binderTms with
    | []      => `("")
    | x :: xs => xs.foldlM (fun acc y => `($acc ++ $y)) x
  -- per-piece: `(piece = "" ∨ IsWf.<Nt> piece)`
  let pieceProps ← (items.zip binderTms).mapM (fun (it, pTm) => do
    let hd ← symPred specName it.sym pTm
    `($pTm = "" ∨ $hd))
  let eqp ← `($whole = $concat)
  let body ← pieceProps.foldlM (fun acc p => `($acc ∧ $p)) eqp
  mkExists binders body

/-- Predicate that string `whole` matches sequence `items`:
    * no optionals            → flat named form (`seqPredFlat`);
    * ALL items optional captures → flat "empty-or-wf" form (`seqAllOptional`), avoiding
      the combinatorial peel tree (the doc's `[Days][Hours]…` shape);
    * otherwise (mixed)       → peel form (`seqPeel`). -/
partial def seqPred (specName : Name) (whole : TSyntax `term)
    (items : List SymItem) (_depth : Nat := 0) : CommandElabM (TSyntax `term) := do
  if items.all (! ·.optional) then
    seqPredFlat specName whole items
  else if items.all (fun it => it.optional && (binderBase it.sym).isSome) then
    seqAllOptional specName whole items
  else
    seqPeel specName whole items 0

/-- Predicate that string `v` matches production `p` (disjunction over alternatives). -/
def prodPred (specName : Name) (p : Production) (v : TSyntax `term) :
    CommandElabM (TSyntax `term) := do
  match p.alts with
  | []        => `(False)
  | a :: rest =>
      let first ← seqPred specName v a 0
      rest.foldlM (fun acc alt => do `($acc ∨ $(← seqPred specName v alt 0))) first

/-- Topologically order productions leaf-first (dependencies before dependents), so each
    emitted `def` references only already-defined sibling predicates. Assumes the grammar
    is acyclic (checked elsewhere); on a cycle, remaining nodes are appended in input
    order (the generated defs would then fail to compile, surfacing the cycle). -/
partial def topoOrder (g : Grammar) : List Production :=
  let step := fun (visited : List String) (acc : List Production) (name : String) =>
    goName g name visited acc
  (g.prods.map (·.name)).foldl (fun (st : List String × List Production) nm =>
    let (v, a) := step st.1 st.2 nm
    (v, a)) ([], []) |>.2 |>.reverse
where
  /-- DFS: visit `name`'s dependencies, then `name`; accumulate in reverse post-order. -/
  goName (g : Grammar) (name : String) (visited : List String) (acc : List Production) :
      List String × List Production :=
    if visited.contains name then (visited, acc)
    else match g.prod? name with
      | none   => (name :: visited, acc)
      | some p =>
          let visited := name :: visited
          let (visited, acc) := p.directRefs.foldl (fun (st : List String × List Production) r =>
            goName g r st.1 st.2) (visited, acc)
          (visited, p :: acc)

/-! ## Reconciliation proof synthesis (engine `IsWf` ⟺ surface `IsWf.<Prod>`)

Emits, per production (leaf-first), a lemma `<Name>.matchesRef.<Prod>` proving the engine
denotation of a *reference* to `<Prod>` equals the surface predicate `<Name>.IsWf.<Prod>`,
plus a top-level `<Name>.IsWf_equiv` bridging `IsWf grammar` to `<Name>.IsWf.<start>`. The
proofs are a fixed skeleton discharged by the `Triptych/Reconcile.lean` lemmas + a uniform
`simp`/`grind` closer; see that module and design note §16. -/

/-- Subtree depth of a production: the longest chain of nonterminal references starting at
    `name` (a leaf with no refs has depth 1). This is the exact fuel *offset* at which the
    production's `matchesRef` lemma must be stated: the engine reference `matchesSym g
    (fuel+depth) (ref name)` decrements one fuel per ref hop, so each descendant reference
    lands on a `_+1` successor that its own `∀ fuel` lemma can unify against. Assumes the
    grammar is acyclic (`fuel` bounds the recursion by #productions as a backstop). -/
partial def subtreeDepth (g : Grammar) (name : String) (fuel : Nat) : Nat :=
  match fuel, g.prod? name with
  | 0, _            => 1
  | _, none         => 1
  | fuel+1, some p  =>
      let childDepths := p.directRefs.map (fun r => subtreeDepth g r fuel)
      1 + childDepths.foldl Nat.max 0

/-- Render a `Sym` as a `SymItem` literal term (mirrors `elabSym`/`elabItem` but produces
    the fully-applied constructor form used inside the `show … = some <prod> from rfl`). -/
private partial def symLit : Sym → CommandElabM (TSyntax `term)
  | .lit l        => `(Sym.lit $(Syntax.mkStrLit l))
  | .ref nm       => `(Sym.ref $(Syntax.mkStrLit nm))
  | .term tok ls  => do
      let tokT ← match tok with
        | .digit    => `(TokClass.digit)
        | .hexDigit => `(TokClass.hexDigit)
        | .bit      => `(TokClass.bit)
      let lsT ← match ls with
        | .exactly n    => `(LenSpec.exactly $(quote n))
        | .between lo hi => `(LenSpec.between $(quote lo) $(quote hi))
        | .atLeastOne   => `(LenSpec.atLeastOne)
      `(Sym.term $tokT $lsT)
  | .rep sep item lo hi => do
      let itemT ← symLit item
      let hiT ← match hi with
        | none   => `((none : Option Nat))
        | some h => `(some $(quote h))
      `(Sym.rep $(Syntax.mkStrLit sep) $itemT $(quote lo) $hiT)

private def symItemLit (it : SymItem) : CommandElabM (TSyntax `term) := do
  let symT ← symLit it.sym
  let optT ← if it.optional then `(true) else `(false)
  `(SymItem.mk $symT $optT)

/-- Render a production as a `Production.mk <name> [<alt>…]` literal term. -/
private def prodLit (p : Production) : CommandElabM (TSyntax `term) := do
  let altTerms ← p.alts.mapM (fun alt => do
    let itemTerms ← alt.mapM symItemLit
    let sep : Syntax.TSepArray `term "," := .ofElems itemTerms.toArray
    `([$sep,*]))
  let asep : Syntax.TSepArray `term "," := .ofElems altTerms.toArray
  `(Production.mk $(Syntax.mkStrLit p.name) [$asep,*])

/-- The leaf-collapse `simp` lemma names for the terminals appearing in a production
    (so `matchesTerm` rewrites to the surface `IsDigits`/… vocabulary). -/
private def leafLemmasFor (p : Production) : List (TSyntax `term) := Id.run do
  let mut out : List (TSyntax `term) := []
  let mut haveDigits := false
  let mut haveHex := false
  let mut haveBit := false
  -- the terminal class of a symbol, seeing through a `rep` wrapper to its item
  let rec tokOf : Sym → Option TokClass
    | .term tok _     => some tok
    | .rep _ item _ _ => tokOf item
    | _               => none
  for alt in p.alts do
    for it in alt do
      match tokOf it.sym with
      | some .digit    => haveDigits := true
      | some .hexDigit => haveHex := true
      | some .bit      => haveBit := true
      | none           => pure ()
  -- Reference the leaf-collapse lemmas by (unresolved) name — they live in
  -- `Triptych.Theorems.Reconcile`, which the GENERATED file imports; resolving them here would
  -- force an Emit→Reconcile import. Include all shapes per class; `simp only` ignores
  -- any that don't fire.
  let mk (n : String) : TSyntax `term := ⟨(mkIdent (Name.mkSimple n)).raw⟩
  if haveDigits then
    out := out ++ [mk "IsDigits_matchesTerm", mk "IsFixedDigits_matchesTerm",
      mk "IsDigitsBetween_matchesTerm"]
  if haveHex then
    out := out ++ [mk "IsHexDigits_matchesTerm", mk "IsFixedHexDigits_matchesTerm",
      mk "IsHexDigitsBetween_matchesTerm"]
  if haveBit then
    out := out ++ [mk "IsBits_matchesTerm", mk "IsFixedBits_matchesTerm",
      mk "IsBitsBetween_matchesTerm"]
  return out

/-- The namespace the per-production reconciliation support lemmas live in:
    `<Name>.Internal.matchesRef.<Prod>`. Kept under `Internal` to visually demote the
    grinding (it's support for `<Name>.IsWf_equiv`, not a public result). -/
def matchesRefName (specName : Name) (prod : String) : Name :=
  specName ++ `Internal ++ `matchesRef ++ prod.toName

/-- Sibling `matchesRef` lemma references for the nonterminals a production references
    (so they fire as `simp` rewrites, resolving each engine reference to its surface
    predicate). -/
private def refLemmasFor (specName : Name) (p : Production) : List (TSyntax `term) :=
  p.directRefs.eraseDups.map (fun r =>
    ⟨(mkIdent (matchesRefName specName r)).raw⟩)

/-- Is a production's (single) alternative an ALL-optional capture run? (Mirrors
    `seqPred`'s branch — decides `matchesSeq_opt_cons` vs raw `matchesSeq.eq_2`.) -/
private def altAllOptional (alt : Seq) : Bool :=
  alt.all (fun it => it.optional && (binderBase it.sym).isSome)


/-- Emit `<Name>.matchesRef.<Prod>` : `∀ fuel s, matchesSym g (fuel+depth) (ref "Prod") s ↔
    <Name>.IsWf.<Prod> s` (or, for the start/top production called via `matchesProd`, the
    `matchesProd` form). `depth` = `subtreeDepth`. -/
def matchesRefProof (specName : Name) (grammarId : TSyntax `ident) (p : Production)
    (depth : Nat) : CommandElabM (TSyntax `command) := do
  let lemId := mkIdent (matchesRefName specName p.name)
  let surfId := mkIdent (specName ++ `IsWf ++ p.name.toName)
  let prodT ← prodLit p
  let nameLit := Syntax.mkStrLit p.name
  let depthLit := Syntax.mkNatLit depth
  -- wrap a `term` as a `simpLemma` arg so it can be spliced into a `simp only [...]` list
  let asSimp := fun (t : TSyntax `term) => show CommandElabM (TSyntax `Lean.Parser.Tactic.simpLemma) from
    `(Lean.Parser.Tactic.simpLemma| $t:term)
  let leaves ← (leafLemmasFor p).mapM asSimp
  let refs ← (refLemmasFor specName p).mapM asSimp
  let multiAlt := p.alts.length > 1
  -- opt_cons only for an all-optional single alternative (mirrors `seqPred`'s branch);
  -- otherwise the raw `matchesSeq` equations (`eq_1`/`eq_2`) drive the peel/flat form.
  let useOptCons := (p.alts.length == 1) && altAllOptional (p.alts.headD [])
  -- Build the FULL body simp-lemma list as one array and splat it once (empty sub-lists
  -- would otherwise produce invalid trailing commas). `mk` = name → simpLemma.
  let mk := fun (n : Name) => asSimp ⟨(mkIdent n).raw⟩
  let bodyBase : List (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    (if multiAlt then
      [``List.mem_cons, ``List.mem_singleton, ``List.not_mem_nil].mapM mk
    else pure [])
  let optCons ← if useOptCons then (do pure [← mk ``matchesSeq_opt_cons]) else pure []
  let seqEqs ← [``matchesSeq.eq_1, ``matchesSeq.eq_2].mapM mk
  let membershipEqs ← if multiAlt then
      (do pure [← mk ``exists_eq_or_imp, ← mk ``exists_eq_left])
    else pure []
  -- shared boolean/if reducers
  let reducers ← [``exists_eq_left, ``if_true, ``if_false, ``Bool.false_eq_true,
    ``false_and, ``or_false, ``or_assoc].mapM mk
  let matchesSymL ← mk ``matchesSym
  let allBody : Array (TSyntax `Lean.Parser.Tactic.simpLemma) :=
    (bodyBase ++ optCons ++ seqEqs ++ membershipEqs ++ reducers ++ [matchesSymL]
      ++ leaves ++ refs).toArray
  if multiAlt then
    `(theorem $lemId (fuel : Nat) (s : String) :
          matchesSym $grammarId (fuel + $depthLit) (Sym.ref $nameLit) s ↔ $surfId s := by
        rw [matchesSym, show ($grammarId).prod? $nameLit = some $prodT from rfl]
        dsimp only
        unfold matchesProd $surfId
        simp (config := { maxSteps := 1000000 }) only [$allBody,*]
        repeat'
          first
          | apply or_congr
          | (simp (config := { maxSteps := 1000000 }) only [String.append_assoc, String.append_empty, exists_and_left,
                ← and_assoc, exists_eq_left, exists_eq_left', exists_eq_right, and_true,
                Option.some.injEq, forall_eq']
             try grind [String.append_assoc, String.append_empty]))
  else
    `(theorem $lemId (fuel : Nat) (s : String) :
          matchesSym $grammarId (fuel + $depthLit) (Sym.ref $nameLit) s ↔ $surfId s := by
        rw [matchesSym, show ($grammarId).prod? $nameLit = some $prodT from rfl]
        dsimp only
        rw [matchesProd_single]
        unfold $surfId
        simp (config := { maxSteps := 1000000 }) only [$allBody,*]
        simp (config := { maxSteps := 1000000 }) only [String.append_assoc, String.append_empty, exists_and_left,
          ← and_assoc, exists_eq_left, exists_eq_left', exists_eq_right, and_true,
          Option.some.injEq, forall_eq']
        try grind [String.append_assoc, String.append_empty])

/-- Emit the top-level bridge `<Name>.IsWf_equiv : IsWf g s ↔ <Name>.IsWf.<start> s`.
    Reduces `IsWf` to the start production's `matchesProd` at concrete fuel `g.prods.length`,
    re-folds it as a `matchesSym` reference (`matchesSym g (N+1) (ref start) = matchesProd g N
    …` definitionally), then applies the start production's `matchesRef` lemma (`∀ fuel`, so
    the concrete fuel unifies). -/
def isWfEquivProof (specName : Name) (grammarId : TSyntax `ident) (start : Production)
    : CommandElabM (TSyntax `command) := do
  let equivId := mkIdent (specName ++ `IsWf_equiv)
  let startRef := mkIdent (matchesRefName specName start.name)
  let surfId := mkIdent (specName ++ `IsWf ++ start.name.toName)
  let startLit := Syntax.mkStrLit start.name
  let prodT ← prodLit start
  `(theorem $equivId (s : String) : IsWf $grammarId s ↔ $surfId s := by
      rw [isWf_eq_isWfProd_start, IsWfProd,
        show ($grammarId).prod? ($grammarId).start = some $prodT from rfl]
      -- `IsWf` uses fuel = `prods.length`; re-express the start production match as the
      -- reference `matchesSym _ (prods.length) (ref start)` so the `matchesRef` lemma fires.
      have hstart : ∀ n, matchesProd $grammarId n $prodT s
          = matchesSym $grammarId (n+1) (Sym.ref $startLit) s := by
        intro n
        rw [matchesSym, show ($grammarId).prod? $startLit = some $prodT from rfl]
      show matchesProd $grammarId ($grammarId).prods.length $prodT s ↔ _
      rw [hstart]
      exact $startRef _ s)

/-- Emit the FULL acceptance bridge `<Name>.IsValid_equiv : <Name>.IsValid s ↔ <Name>.isValid s`
    — the surface (readable) acceptance predicate equals the engine (decode-backed) one.
    Composes three facts: `IsWf_equiv` (readable `IsWf.<start>` ⟺ interpreter `IsWf grammar`),
    `decodeSome_iff_IsWf` (interpreter `IsWf` ⟺ `decode.isSome`, the roundtrip), and reader
    agreement (`natOf (getD "") = Env.natVal`, …) that reconciles the surface `Constraints` (on
    decoded component strings) with the engine's `wfPart`/`valPart` `eval`. The whole thing
    closes by `simp` after unfolding both sides. `hasConstraints`/`hasValue`/`opaque` control
    which spec-specific defs to unfold (a def absent ⟹ not unfolded). -/
def isValidEquivProof (specName : Name)
    (hasConstraints hasValue : Bool) : CommandElabM (TSyntax `command) := do
  let equivId    := mkIdent (specName ++ `IsValid_equiv)
  let validSurf  := mkIdent (specName ++ `IsValid)
  let validEng   := mkIdent (specName ++ `isValid)
  let isWfEng    := mkIdent (specName ++ `isWf)
  let scEng      := mkIdent (specName ++ `satisfiesConstraints)
  let scSurf     := mkIdent (specName ++ `SatisfiesConstraints)
  let cList      := mkIdent (specName ++ `constraints)
  let cRel       := mkIdent (specName ++ `Constraints)
  let valFn      := mkIdent (specName ++ `value)
  let valExpr    := mkIdent (specName ++ `valueExpr)
  let equivWf    := mkIdent (specName ++ `IsWf_equiv)
  let grammarId  := mkIdent (specName ++ `grammar)
  -- Defs to unfold, in dependency order: `SatisfiesConstraints → Constraints` (surface) and
  -- the engine `constraints` list; then `value` (surface) and `valueExpr` (engine AST, which
  -- only appears *after* the `constraints` list is unfolded). Each included only when present
  -- AND reachable: `value`/`valueExpr` appear in the goal only through the constraints, so a
  -- value section WITHOUT constraints must not list them (`unfold` fails on an absent target).
  let surfUnfolds : Array (TSyntax `ident) :=
    #[scSurf] ++ (if hasConstraints then #[cRel] else #[]) ++ #[cList]
      ++ (if hasConstraints && hasValue then #[valFn, valExpr] else #[])
  -- The final `simp` lemma set (fixed): unfold the constraint-entry machinery + reader
  -- agreement, collapse the wf/val classification `if`s and the `∀ _ ∈ []` tails.
  `(theorem $equivId (s : String) : $validSurf s ↔ $validEng s := by
      unfold $validSurf $validEng $isWfEng $scEng
      unfold Triptych.isWf Triptych.satisfiesConstraints
      rw [← $equivWf, ← decodeSome_iff_IsWf $grammarId (by decide)]
      unfold $[$surfUnfolds:ident]*
      simp only [Triptych.component, List.forall_mem_cons, List.forall_mem_singleton,
        List.not_mem_nil, forall_const, if_true, if_false, ConstraintEntry.wfPart,
        ConstraintEntry.valPart, Constraint.wfPart, Constraint.valPart, Constraint.isValueDependent,
        Constraint.eval, ValExpr.eval, presentCount, natOf_getD, intOf_getD, lenOf_getD, signOf_getD,
        and_true, true_and, false_implies, implies_true, Bool.false_eq_true]
      try grind)
  -- After the `simp`, both sides are the same set of atoms — but the engine groups all
  -- `wfPart`s then all `valPart`s, while the surface groups per-constraint. `grind` closes
  -- that ∧-reassociation/permutation (a no-op `try` when `simp` already finished the goal).

/-- Emit the value bridge `<Name>.computeValue_eq : computeValue s = (decode g s).map (fun _ =>
    value <components>)` — the engine's extracted value equals the READABLE `value` function
    applied to the same decoded component strings, on every string (`none` when not
    well-formed). This is the value analogue of `IsWf_equiv`: it exposes, as a standalone
    theorem, the surface⟺engine value agreement that otherwise only appears folded into
    `IsValid_equiv` (and only when the value is constrained). `caps` are the captures the
    value reads, in `value`'s binder order; `isDsl` selects the tier — DSL unfolds the
    `valueExpr` AST and discharges via the reader-agreement lemmas + `ValExpr.eval`, the
    `value'` escape unfolds `valueFn` (surface and engine share the author's fn, so the two
    sides are defeq after `Option.map_some`). -/
def computeValueEqProof (specName : Name) (grammarId : TSyntax `ident)
    (caps : List String) (isDsl : Bool) : CommandElabM (TSyntax `command) := do
  let equivId := mkIdent (specName ++ `computeValue_eq)
  let cvId    := mkIdent (specName ++ `computeValue)
  let valId   := mkIdent (specName ++ `value)
  -- `value <component g s "c₀"> <component g s "c₁"> …` — the readable value on decoded strings.
  let compArgs : Array (TSyntax `term) ← caps.toArray.mapM (fun c =>
    `(Triptych.component $grammarId s $(Syntax.mkStrLit c)))
  -- Tier-specific unfolds: the engine value entry point + the value definition it reduces to.
  let cvEntry  := mkIdent (if isDsl then `Triptych.computeValue else `Triptych.computeValueF)
  let valDef   := mkIdent (specName ++ (if isDsl then `valueExpr else `valueFn))
  `(theorem $equivId (s : String) :
        $cvId s = (decode $grammarId s).map (fun _ => $valId $compArgs*) := by
      unfold $cvId $cvEntry Triptych.component Triptych.envOf $valId $valDef
      cases h : decode $grammarId s with
      | none => simp
      | some m =>
        simp only [Option.map_some, natOf_getD, intOf_getD, lenOf_getD, signOf_getD, ValExpr.eval])

/-- Elaborate the identifier `fnId` (expected type `String → Option τ`) and return `τ` as
    surface syntax together with a one-letter binder name derived from `τ`'s head — e.g.
    `Decimal.computeValue : String → Option Int` ↦ (`Int`, `i`), a `… → Option Decimal` ↦
    (`Decimal`, `d`). The concrete type replaces the `_` in the generated `∀ (a : _)` binder so
    the reader sees the real value type. Falls back to (`_`, `a`) if the shape is unexpected. -/
def optionPayloadBinder (fnId : TSyntax `term) : CommandElabM (TSyntax `term × Name) := do
  let fallbackTy ← `(_)
  let fallback : TSyntax `term × Name := (fallbackTy, `a)
  liftTermElabM do
    let e ← Term.elabTerm fnId none
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← Meta.whnf (← Meta.inferType e)
    -- Peel `String → Option τ` (the value-fn / parser shape); non-dependent arrow.
    let .forallE _ _ body _ := ty | return fallback
    let cod ← Meta.whnf body
    unless cod.isAppOfArity ``Option 1 do return fallback
    let payload := cod.appArg!
    let payloadStx ← Lean.PrettyPrinter.delab payload
    -- Binder name = lowercased first letter of the payload type's head constant.
    let nm : Name :=
      match payload.getAppFn.constName? with
      | some c =>
        match c.getString!.toList with
        | ch :: _ => Name.mkSimple (String.singleton ch.toLower)
        | [] => `a
      | none => `a
    return (payloadStx, nm)

/-- Elaborate the lift `σ : β → δ` and return its CODOMAIN `δ` as surface syntax plus a
    one-letter binder derived from `δ`'s head (e.g. `Int64.ofInt : Int → Decimal` ↦ (`Decimal`,
    `d`)). Peels one non-dependent arrow and delaborates the result. Falls back to (`_`, `d`). -/
def liftCodomainBinder (σId : TSyntax `term) : CommandElabM (TSyntax `term × Name) := do
  let fallbackTy ← `(_)
  let fallback : TSyntax `term × Name := (fallbackTy, `d)
  liftTermElabM do
    let e ← Term.elabTerm σId none
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← Meta.whnf (← Meta.inferType e)
    let .forallE _ _ body _ := ty | return fallback
    let cod ← Meta.whnf body
    let codStx ← Lean.PrettyPrinter.delab cod
    let nm : Name :=
      match cod.getAppFn.constName? with
      | some c =>
        match c.getString!.toList with
        | ch :: _ => Name.mkSimple (String.singleton ch.toLower)
        | [] => `d
      | none => `d
    return (codStx, nm)

/-- Elaborate the serializer `toStr : δ → String` and return its DOMAIN `δ` as surface syntax plus
    a one-letter binder derived from `δ`'s head (e.g. `decimalToStr : Decimal → String` ↦
    (`Cedar.Spec.Ext.Decimal`, `d`)). This is the AUTHORITATIVE domain type for the printer
    theorems (Cedar's `parse_toString_roundtrip` is keyed on `d : Decimal`). Peels one
    non-dependent arrow and delaborates the ARGUMENT. Falls back to (`_`, `d`). -/
def serializerDomainBinder (toStrId : TSyntax `term) : CommandElabM (TSyntax `term × Name) := do
  let fallbackTy ← `(_)
  let fallback : TSyntax `term × Name := (fallbackTy, `d)
  liftTermElabM do
    let e ← Term.elabTerm toStrId none
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← Meta.whnf (← Meta.inferType e)
    let .forallE _ dom _ _ := ty | return fallback
    let dom ← Meta.whnf dom
    let domStx ← Lean.PrettyPrinter.delab dom
    let nm : Name :=
      match dom.getAppFn.constName? with
      | some c =>
        match c.getString!.toList with
        | ch :: _ => Name.mkSimple (String.singleton ch.toLower)
        | [] => `d
      | none => `d
    return (domStx, nm)

/-- Emit the generated correct-by-construction parser and its three DISCHARGED contracts:
    `<Name>.computeValue_isSome` (accepted ⟹ value present, straight from the ENGINE `isValid`
    → engine `isWf` → `decode.isSome`), `<Name>.parse`, and `parse_sound`/`parse_complete`/
    `parse_reject` (statements written out). No `sorry` — this is the tool's OWN verified parser
    (distinct from the external-parser obligations). Gated on the ENGINE `isValid` (structurally
    decidable, no `IsValid_equiv` needed), so this whole bundle depends only on the engine.
    `isDsl` selects the value entry point (`computeValue` vs `computeValueF`).

    With a `lift? = some σ` clause the parser is LIFTED to the domain type `δ` (via `σ : β → δ`):
    `parse := gatedParseLift isValid computeValue σ : String → Option δ`, with σ-VIEW contracts
    (`(computeValue s).map σ = some d`), closed by the `gatedParseLift_*` lemmas. Without a lift,
    `parse := gatedParse isValid computeValue : String → Option β` with the `π = id` contracts. -/
def parserContractsProof (specName : Name) (isDsl : Bool) (lift? : Option (TSyntax `term))
    : CommandElabM (Array (TSyntax `command)) := do
  let isSomeId := mkIdent (specName ++ `computeValue_isSome)
  let parseId  := mkIdent (specName ++ `parse)
  let soundId  := mkIdent (specName ++ `parse_sound)
  let compId   := mkIdent (specName ++ `parse_complete)
  let rejId    := mkIdent (specName ++ `parse_reject)
  let validEng  := mkIdent (specName ++ `isValid)
  let isWfEng   := mkIdent (specName ++ `isWf)
  let cvId      := mkIdent (specName ++ `computeValue)
  let cvEntry   := mkIdent (if isDsl then `Triptych.computeValue else `Triptych.computeValueF)
  let isSomeThm ← `(theorem $isSomeId (s : String) : $validEng s → ($cvId s).isSome := by
      intro h
      unfold $validEng $isWfEng Triptych.isWf at h
      unfold $cvId $cvEntry
      rw [Option.isSome_map]
      exact h.1.1)
  match lift? with
  | some σT =>
    -- LIFTED parser: return the domain type `δ` via `σ`. Contracts are σ-view.
    let parseDef ← `(def $parseId (s : String) := Triptych.gatedParseLift $validEng $cvId $σT s)
    let (dTy, dNm) ← liftCodomainBinder σT
    let dId := mkIdent dNm
    let soundThm ← `(theorem $soundId (s : String) ($dId : $dTy) :
        $parseId s = some $dId → $validEng s ∧ ($cvId s).map $σT = some $dId :=
      Triptych.gatedParseLift_sound _ _ _ s $dId)
    let compThm ← `(theorem $compId (s : String) ($dId : $dTy) :
        $validEng s → ($cvId s).map $σT = some $dId → $parseId s = some $dId :=
      Triptych.gatedParseLift_complete _ _ _ s $dId)
    let rejThm ← `(theorem $rejId (s : String) :
        $parseId s = none ↔ ¬ $validEng s := Triptych.gatedParseLift_reject _ _ _ $isSomeId s)
    return #[isSomeThm, parseDef, soundThm, compThm, rejThm]
  | none =>
    -- UNLIFTED parser: return the spec value type `β` (`π = id`).
    let parseDef ← `(def $parseId (s : String) := Triptych.gatedParse $validEng $cvId s)
    -- Concrete value type + a one-letter binder from its head (e.g. `Int`→`i`), so the emitted
    -- statements show the real type instead of `_`.
    let (valTy, aNm) ← optionPayloadBinder cvId
    let aId := mkIdent aNm
    -- The three guarantees, with their statements written OUT (not hidden behind `SoundStmt`
    -- etc.) so the reader sees the actual proposition; each closes definitionally from the
    -- generic `gatedParse_*` lemma (`π = id`, so `some (id a)` reduces to `some a`).
    let soundThm ← `(theorem $soundId (s : String) ($aId : $valTy) :
        $parseId s = some $aId → $validEng s ∧ $cvId s = some $aId :=
      Triptych.gatedParse_sound _ _ s $aId)
    let compThm ← `(theorem $compId (s : String) ($aId : $valTy) :
        $validEng s → $cvId s = some $aId → $parseId s = some $aId :=
      Triptych.gatedParse_complete _ _ s $aId)
    let rejThm ← `(theorem $rejId (s : String) :
        $parseId s = none ↔ ¬ $validEng s := Triptych.gatedParse_reject _ _ $isSomeId s)
    return #[isSomeThm, parseDef, soundThm, compThm, rejThm]

end Triptych
