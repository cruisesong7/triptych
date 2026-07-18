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

import FormatSpec.Grammar
import FormatSpec.Denote
import FormatSpec.Value

/-!
# `decode` — the executable capture extractor, and `computeValue`

`IsWf` (from `Denote`) *recognizes* a string existentially. `computeValue` needs the
*witnessing* capture assignment: which substring each nonterminal matched. `decode`
computes that assignment — the executable inverse of the grammar denotation.

`decode` is a small backtracking recognizer-with-captures over the flat grammar: it
tries every way to split the string across a sequence's items, records each matched
nonterminal's substring, and keeps assignments that consume the whole string. It is the
*reference* decoder (simple, obviously-correct-by-inspection), NOT a production parser.

Status: `partial` and executable (drives `#eval`/demos and, later, differential testing
against the hand-written parser). Its roundtrip lemma vs `IsWf` — `decode (asString env)
= some env` on well-formed inputs — is the next proof milestone; not yet proved.
-/

namespace FormatSpec

/-- A capture assignment: nonterminal name ↦ matched substring. -/
abbrev CaptureMap := List (String × String)

/-- View a `CaptureMap` as the `Env` the value/constraint DSLs evaluate against. -/
def CaptureMap.toEnv (m : CaptureMap) : Env := fun k => (m.find? (·.1 == k)).map (·.2)

/-- Does the length-`k` prefix of `cs` satisfy the terminal `tok`/`ls`? Routes through the
    single `matchesTerm` predicate (shared with the recognizer/spec), so the token semantics
    is defined once; the `k ≤ cs.length` guard keeps the prefix a genuine prefix. -/
def termPrefixOk (tok : TokClass) (ls : LenSpec) (cs : List Char) (k : Nat) : Bool :=
  k ≤ cs.length && decide (matchesTerm tok ls (String.ofList (cs.take k)))

/-- The `(sep item)*` tail: from position `cs`, every way to match zero-or-more further
    `sep item` groups. Each result is `(captures, remaining, k)` where `k` is the number of
    ADDITIONAL items matched here. Higher-order in the item-matcher `matchItem` and
    structurally recursive on its own `fuel` (bounded by the string length at the call site),
    so it lives OUTSIDE the fuel/`Sym` mutual block below — `matchSym` feeds it the closure. -/
def matchStar (matchItem : List Char → List (CaptureMap × List Char)) (sepL : List Char) :
    Nat → List Char → List (CaptureMap × List Char × Nat)
  | 0,      cs => [([], cs, 0)]                 -- iteration fuel out: only the empty tail
  | fuel+1, cs =>
      let more :=
        if sepL.isPrefixOf cs then
          let cs1 := cs.drop sepL.length
          (matchItem cs1).flatMap (fun (m1, r1) =>
            (matchStar matchItem sepL fuel r1).map (fun (m2, r2, k) => (m1 ++ m2, r2, k + 1)))
        else []
      ([], cs, 0) :: more                        -- stop here, or take one more `sep item`

/-- All ways `item (sep item)*` (≥ 1 item) matches a prefix of `cs`, each as
    `(captures, remaining, count)` with `count` ≥ 1 the number of items matched. -/
def matchRep (matchItem : List Char → List (CaptureMap × List Char)) (sepL : List Char)
    (cs : List Char) : List (CaptureMap × List Char × Nat) :=
  (matchItem cs).flatMap (fun (m1, r1) =>
    (matchStar matchItem sepL cs.length r1).map (fun (m2, r2, k) => (m1 ++ m2, r2, k + 1)))

mutual

/-- All ways symbol `sym` matches a prefix of `cs`: each result is (captures, remaining).
    `fuel` bounds ref-recursion (= #productions, the DAG depth), mirroring `Denote`; this
    makes the function TOTAL and kernel-reducible (so `decide`, not `native_decide`).

    `qual` is the IMMEDIATE-PARENT production name (`""` at the start production). A matched
    nonterminal `name` is recorded under BOTH its bare key `name` AND — when `qual` is
    nonempty — the qualified key `qual ++ "." ++ name`. So a nonterminal reused in several
    parents (e.g. `hh` in both `Time` and `Offset`) is still reachable *unambiguously* as
    `Time.hh` / `Offset.hh`, while the bare `name` keeps working for uniquely-used captures
    (backward compatible: unique captures resolve by bare name exactly as before). -/
def matchSym (g : Grammar) (qual : String) : Nat → Sym → List Char → List (CaptureMap × List Char)
  | _,      .lit l,        cs =>
      let ls := l.toList
      if ls.isPrefixOf cs then [([], cs.drop ls.length)] else []
  | _,      .term tok ls,  cs =>
      -- try every valid prefix length (backtracking over the token run)
      (List.range (cs.length + 1)).filterMap (fun k =>
        if termPrefixOk tok ls cs k then some ([], cs.drop k) else none)
  | fuel,   .rep sep item lo hi, cs =>
      -- Enumerate every way `item (sep item)*` consumes a prefix, keeping only those whose
      -- item-count lands in `[lo, hi]`. `matchRep` returns (captures, remaining, count); we
      -- surface the count under the derived key `qual ++ "#count"` (decimal), so downstream
      -- `count(...)` constraints read it via the existing `natOf` — no CaptureMap shape change.
      -- Count key: the repeated ITEM's name (`H16#count`) — what a `count(H16)` constraint
      -- references — falling back to the enclosing production `qual` for anonymous items.
      let base := item.refName?.getD qual
      (matchRep (fun cs' => matchSym g qual fuel item cs') sep.toList cs).filterMap
        (fun (m, rem, n) =>
          if lo ≤ n && (match hi with | none => true | some h => n ≤ h)
          then some ((base ++ "#count", toString n) :: m, rem) else none)
  | 0,      .ref _,        _  => []        -- out of fuel (cannot happen in a DAG)
  | fuel+1, .ref name,     cs =>
      match g.prod? name with
      | none   => []
      | some p =>
          -- children of `name` are qualified by `name`
          (matchProd g name fuel p cs).map (fun (m, rem) =>
            let consumed := String.ofList (cs.take (cs.length - rem.length))
            let keys := if qual.isEmpty then [(name, consumed)]
                        else [(name, consumed), (qual ++ "." ++ name, consumed)]
            (keys ++ m, rem))

/-- All ways a sequence matches a prefix of `cs`. `qual` = the enclosing production name. -/
def matchSeq (g : Grammar) (qual : String) : Nat → Seq → List Char → List (CaptureMap × List Char)
  | _,    [],           cs => [([], cs)]
  | fuel, item :: rest, cs =>
      let present := (matchSym g qual fuel item.sym cs).flatMap (fun (m1, r1) =>
        (matchSeq g qual fuel rest r1).map (fun (m2, r2) => (m1 ++ m2, r2)))
      if item.optional then present ++ matchSeq g qual fuel rest cs else present

/-- All ways a production matches a prefix of `cs` (union over alternatives). `qual` is the
    production's OWN name, used to qualify the captures its alternatives produce. -/
def matchProd (g : Grammar) (qual : String) (fuel : Nat) (p : Production) (cs : List Char) :
    List (CaptureMap × List Char) :=
  p.alts.flatMap (fun alt => matchSeq g qual fuel alt cs)

end

/-- Decode a string into a capture assignment: a full-consumption match of the start
    production. Fuel = #productions (DAG-depth backstop). Returns the first such
    assignment, or `none` if the string is not well-formed. Start-production children are
    unqualified (`qual := ""`), so top-level captures keep their bare names. -/
def decode (g : Grammar) (s : String) : Option CaptureMap :=
  match g.startProd? with
  | none   => none
  | some p =>
      let full := (matchProd g "" g.prods.length p s.toList).filter (fun (_, rem) => rem.isEmpty)
      full.head?.map (·.1)

/-- The value function: decode the string, then evaluate the value expression against
    the resulting capture environment. `none` when the string is not well-formed. -/
def computeValue (g : Grammar) (ve : ValExpr) (s : String) : Option Int :=
  (decode g s).map (fun m => ve.eval m.toEnv)

/-- The value function for an ARBITRARY-typed value: decode the string, then apply a value
    reader `valFn : Env → α` to the resulting capture environment. `none` when the string is
    not well-formed. This is the generalization of `computeValue` beyond `Int` — the `value'`
    escape tier supplies a `valFn` returning any `α` (e.g. `SimpleGraph`, an adjacency matrix,
    an `IPNet`), so the generated `computeValue` can parse a string into a STRUCTURED value.
    `computeValue g ve = computeValueF g (ve.eval ·)` (the DSL tier is the `α := Int` case). -/
def computeValueF {α : Type} (g : Grammar) (valFn : Env → α) (s : String) : Option α :=
  (decode g s).map (fun m => valFn m.toEnv)

end FormatSpec
