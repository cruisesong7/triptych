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

import Triptych.Architecture.Classify
import Triptych.Architecture.Scanner

/-!
# Ordered search-plan intermediate representation

`ScanPlan` is the smallest and fastest parser IR: one deterministic path lowers to a flat
`CursorProgram`. `SearchPlan` is the next tier. It covers the complete acyclic grammar surface
while retaining the scanner's source ordering:

* production alternatives remain ordered choices;
* optional symbols try present before absent;
* separated repetitions try stop before continue;
* references are resolved and inlined at generation time.

The executor is continuation based. It never materializes the candidate lists used by the
reference decoder, and it never performs a production-name lookup at runtime.

Compilation is proof carrying in the same sense as `ScanPlan`: an independently executable
validator reconstructs a `MirrorsGrammar` witness. The theorem layer uses that witness to prove
that ordered search is exactly the complete scanner, including its selected capture map.
-/

namespace Triptych

/-- One resolved search-plan symbol. Optionality is represented explicitly so its ordering is
    visible in the plan rather than retained in a source `SymItem`. -/
inductive SearchPattern where
  | literal (text : String)
  | stringLiteral
  | tokenRun (token : TokClass) (length : LenSpec)
  | capture (name : String) (keys : List String)
      (alternatives : List (List SearchPattern))
  | repetition (separator : String) (item : SearchPattern)
      (lower : Nat) (upper : Option Nat) (countKey : String)
  | optional (body : SearchPattern)
  deriving Repr, Inhabited

/-- A resolved, source-ordered parser plan for one grammar root. -/
structure SearchPlan where
  start : String
  alternatives : List (List SearchPattern)
  deriving Repr, Inhabited

def SearchPattern.expectedCaptureKeys (qual name : String) : List String :=
  if qual.isEmpty then [name] else [name, qual ++ "." ++ name]

mutual

private partial def compileSearchSymbol (grammar : Grammar) (qual : String) (fuel : Nat) :
    Sym → Except String SearchPattern
  | .lit text => pure (.literal text)
  | .str => pure .stringLiteral
  | .term token length => pure (.tokenRun token length)
  | .rep separator item lower upper => do
      let compiled ← compileSearchSymbol grammar qual fuel item
      pure (.repetition separator compiled lower upper (item.refName?.getD qual))
  | .ref name =>
      if fuel == 0 then
        throw "search plan: production nesting exceeded the grammar size"
      else
        match grammar.prod? name with
        | none => throw s!"search plan: unresolved production reference `{name}`"
        | some production => do
            let alternatives ←
              compileSearchAlternatives grammar name (fuel - 1) production.alts
            pure
              (.capture name (SearchPattern.expectedCaptureKeys qual name) alternatives)

private partial def compileSearchSequence (grammar : Grammar) (qual : String) (fuel : Nat) :
    Triptych.Seq → Except String (List SearchPattern)
  | [] => pure []
  | item :: rest => do
      let body ← compileSearchSymbol grammar qual fuel item.sym
      let head := if item.optional then .optional body else body
      pure (head :: (← compileSearchSequence grammar qual fuel rest))

private partial def compileSearchAlternatives (grammar : Grammar) (qual : String)
    (fuel : Nat) : List Triptych.Seq → Except String (List (List SearchPattern))
  | [] => pure []
  | alternative :: rest => do
      let head ← compileSearchSequence grammar qual fuel alternative
      pure (head :: (← compileSearchAlternatives grammar qual fuel rest))

end

mutual

/-- Structural evidence that one resolved plan symbol is the source symbol with references
    inlined and capture metadata preserved. -/
inductive SearchPattern.MirrorsSymbol (grammar : Grammar) :
    String → Nat → Sym → SearchPattern → Prop
  | literal :
      MirrorsSymbol grammar qual fuel (.lit text) (.literal text)
  | stringLiteral :
      MirrorsSymbol grammar qual fuel .str .stringLiteral
  | tokenRun :
      MirrorsSymbol grammar qual fuel (.term token length) (.tokenRun token length)
  | capture
      (hproduction : grammar.prod? name = some production)
      (hkeys : keys = SearchPattern.expectedCaptureKeys qual name)
      (body : SearchPattern.MirrorsAlternatives grammar name fuel
        production.alts alternatives) :
      MirrorsSymbol grammar qual (fuel + 1) (.ref name)
        (.capture name keys alternatives)
  | repetition
      (hcount : countKey = item.refName?.getD qual)
      (body : MirrorsSymbol grammar qual fuel item pattern) :
      MirrorsSymbol grammar qual fuel (.rep separator item lower upper)
        (.repetition separator pattern lower upper countKey)

/-- Structural evidence for one source sequence. -/
inductive SearchPattern.MirrorsSequence (grammar : Grammar) :
    String → Nat → Triptych.Seq → List SearchPattern → Prop
  | empty :
      MirrorsSequence grammar qual fuel [] []
  | required
      (head : SearchPattern.MirrorsSymbol grammar qual fuel symbol pattern)
      (tail : MirrorsSequence grammar qual fuel rest patterns) :
      MirrorsSequence grammar qual fuel
        ({ sym := symbol, optional := false } :: rest) (pattern :: patterns)
  | optional
      (head : SearchPattern.MirrorsSymbol grammar qual fuel symbol pattern)
      (tail : MirrorsSequence grammar qual fuel rest patterns) :
      MirrorsSequence grammar qual fuel
        ({ sym := symbol, optional := true } :: rest) (.optional pattern :: patterns)

/-- Structural evidence for a source-ordered alternative list. -/
inductive SearchPattern.MirrorsAlternatives (grammar : Grammar) :
    String → Nat → List Triptych.Seq → List (List SearchPattern) → Prop
  | empty :
      MirrorsAlternatives grammar qual fuel [] []
  | cons
      (head : SearchPattern.MirrorsSequence grammar qual fuel alternative pattern)
      (tail : MirrorsAlternatives grammar qual fuel alternatives patterns) :
      MirrorsAlternatives grammar qual fuel
        (alternative :: alternatives) (pattern :: patterns)

end

mutual

/-- Proof-producing validator for one resolved symbol. -/
private partial def SearchPattern.validateSymbol (grammar : Grammar) (qual : String) :
    (fuel : Nat) → (symbol : Sym) → (pattern : SearchPattern) →
      Option (PLift (SearchPattern.MirrorsSymbol grammar qual fuel symbol pattern))
  | _fuel, .lit text, .literal found =>
      if h : text = found then
        some ⟨h ▸ .literal⟩
      else
        none
  | _fuel, .str, .stringLiteral => some ⟨.stringLiteral⟩
  | _fuel, .term token length, .tokenRun foundToken foundLength =>
      if htoken : token = foundToken then
        if hlength : length = foundLength then
          some ⟨htoken ▸ hlength ▸ .tokenRun⟩
        else
          none
      else
        none
  | fuel, .rep separator item lower upper,
      .repetition foundSeparator pattern foundLower foundUpper countKey =>
      if hseparator : separator = foundSeparator then
        if hlower : lower = foundLower then
          if hupper : upper = foundUpper then
            if hcount : countKey = item.refName?.getD qual then
              match pattern.validateSymbol grammar qual fuel item with
              | some body =>
                  some
                    ⟨hseparator ▸ hlower ▸ hupper ▸
                      .repetition hcount body.down⟩
              | none => none
            else
              none
          else
            none
        else
          none
      else
        none
  | 0, .ref _, .capture _ _ _ => none
  | fuel + 1, .ref name, .capture foundName keys alternatives =>
      if hname : name = foundName then
        if hkeys : keys = SearchPattern.expectedCaptureKeys qual name then
          match hproduction : grammar.prod? name with
          | none => none
          | some production =>
              match SearchPattern.validateAlternatives grammar name fuel
                  production.alts alternatives with
              | some body =>
                  some
                    ⟨hname ▸ .capture hproduction hkeys body.down⟩
              | none => none
        else
          none
      else
        none
  | _, _, _ => none

/-- Proof-producing validator for one resolved sequence. -/
private partial def SearchPattern.validateSequence (grammar : Grammar) (qual : String) :
    (fuel : Nat) → (sequence : Triptych.Seq) → (patterns : List SearchPattern) →
      Option (PLift (SearchPattern.MirrorsSequence grammar qual fuel sequence patterns))
  | _fuel, [], [] => some ⟨.empty⟩
  | fuel, ⟨symbol, true⟩ :: rest, .optional pattern :: patterns =>
      match pattern.validateSymbol grammar qual fuel symbol,
          validateSequence grammar qual fuel rest patterns with
      | some head, some tail => some ⟨.optional head.down tail.down⟩
      | _, _ => none
  | fuel, ⟨symbol, false⟩ :: rest, pattern :: patterns =>
      match pattern.validateSymbol grammar qual fuel symbol,
          validateSequence grammar qual fuel rest patterns with
      | some head, some tail => some ⟨.required head.down tail.down⟩
      | _, _ => none
  | _, _, _ => none

/-- Proof-producing validator for source-ordered alternatives. -/
private partial def SearchPattern.validateAlternatives (grammar : Grammar) (qual : String) :
    (fuel : Nat) → (alternatives : List Triptych.Seq) →
      (patterns : List (List SearchPattern)) →
      Option
        (PLift
          (SearchPattern.MirrorsAlternatives grammar qual fuel alternatives patterns))
  | _fuel, [], [] => some ⟨.empty⟩
  | fuel, alternative :: alternatives, pattern :: patterns =>
      match SearchPattern.validateSequence grammar qual fuel alternative pattern,
          validateAlternatives grammar qual fuel alternatives patterns with
      | some head, some tail => some ⟨.cons head.down tail.down⟩
      | _, _ => none
  | _, _, _ => none

end

namespace SearchPlan

/-- The compiled plan exactly mirrors the grammar's start production. -/
inductive MirrorsGrammar (plan : SearchPlan) (grammar : Grammar) : Prop where
  | intro
      (hstart : plan.start = grammar.start)
      (production : Production)
      (hproduction : grammar.startProd? = some production)
      (body : SearchPattern.MirrorsAlternatives grammar "" grammar.prods.length
        production.alts plan.alternatives)

/-- Independently validate a compiled plan against its source grammar. -/
def matchesGrammar (plan : SearchPlan) (grammar : Grammar) : Bool :=
  plan.start == grammar.start &&
    match grammar.startProd? with
    | none => false
    | some production =>
        (SearchPattern.validateAlternatives grammar "" grammar.prods.length
          production.alts plan.alternatives).isSome

/-- Passing the executable validator yields the structural grammar witness. -/
theorem mirrorsGrammar_of_matchesGrammar {plan : SearchPlan} {grammar : Grammar}
    (hmatch : plan.matchesGrammar grammar = true) :
    MirrorsGrammar plan grammar := by
  unfold matchesGrammar at hmatch
  have hand := Bool.and_eq_true_iff.mp hmatch
  have hstart : plan.start = grammar.start := by
    simpa using hand.1
  cases hproduction : grammar.startProd? with
  | none => simp [hproduction] at hand
  | some production =>
      cases hvalidate :
          SearchPattern.validateAlternatives grammar "" grammar.prods.length
            production.alts plan.alternatives with
      | none => simp [hproduction, hvalidate] at hand
      | some body =>
          exact .intro hstart production hproduction body.down

end SearchPlan

/-- Compile every supported acyclic grammar into an ordered search plan. -/
def compileSearchPlan (grammar : Grammar) : Except String SearchPlan :=
  if !grammar.refsResolve then
    .error "search plan: every production reference must resolve"
  else
    match grammar.cycle? with
    | some cycle =>
        .error
          s!"search plan: recursive grammars are unsupported: \
            {String.intercalate " -> " cycle}"
    | none =>
        if !grammar.repOk then
          .error
            "search plan: separated repetition requires a nonempty separator and lower bound 1"
        else
          match grammar.startProd? with
          | none => .error s!"search plan: start production `{grammar.start}` is missing"
          | some root =>
              match compileSearchAlternatives grammar "" grammar.prods.length root.alts with
              | .error message => .error message
              | .ok alternatives =>
                  let plan : SearchPlan := { start := grammar.start, alternatives }
                  if plan.matchesGrammar grammar then
                    .ok plan
                  else
                    .error "search plan: internal certification failed"

/-- Successful compilation has passed the independent structural validator. -/
theorem compileSearchPlan_matchesGrammar {grammar : Grammar} {plan : SearchPlan}
    (hcompile : compileSearchPlan grammar = .ok plan) :
    plan.matchesGrammar grammar = true := by
  unfold compileSearchPlan at hcompile
  split at hcompile <;> try contradiction
  split at hcompile <;> try contradiction
  split at hcompile <;> try contradiction
  split at hcompile <;> try contradiction
  rename_i production hproduction
  cases hcompiled :
      compileSearchAlternatives grammar "" grammar.prods.length production.alts with
  | error message =>
      rw [hcompiled] at hcompile
      contradiction
  | ok alternatives =>
      rw [hcompiled] at hcompile
      simp only at hcompile
      let candidate : SearchPlan := { start := grammar.start, alternatives }
      by_cases hmatch : candidate.matchesGrammar grammar = true
      · rw [hmatch] at hcompile
        simp only at hcompile
        cases hcompile
        exact hmatch
      · rw [show candidate.matchesGrammar grammar = false by simpa using hmatch] at hcompile
        simp at hcompile

/-- Successful compilation yields the proof-facing grammar witness. -/
theorem compileSearchPlan_mirrorsGrammar {grammar : Grammar} {plan : SearchPlan}
    (hcompile : compileSearchPlan grammar = .ok plan) :
    SearchPlan.MirrorsGrammar plan grammar :=
  SearchPlan.mirrorsGrammar_of_matchesGrammar (compileSearchPlan_matchesGrammar hcompile)

namespace SearchPattern

mutual

/-- Execute one resolved search symbol and pass candidates to its continuation in reference
    order. -/
def searchK {α : Type} (pattern : SearchPattern) (input : List Char)
    (k : CaptureMap → List Char → Option α) : Option α :=
  match pattern with
  | .literal text =>
      let characters := text.toList
      if characters.isPrefixOf input then k [] (input.drop characters.length) else none
  | .stringLiteral =>
      (List.range (input.length + 1)).findSome? fun width =>
        if stringPrefixOk input width then k [] (input.drop width) else none
  | .tokenRun token length =>
      (List.range (input.length + 1)).findSome? fun width =>
        if termPrefixOk token length input width then k [] (input.drop width) else none
  | .capture _ keys alternatives =>
      searchAlternativesK alternatives input fun captures remaining =>
        let consumed := String.ofList (input.take (input.length - remaining.length))
        k (keys.map (·, consumed) ++ captures) remaining
  | .repetition separator item lower upper countKey =>
      searchK item input fun firstCaptures remaining =>
        scanStarK (searchK item) separator.toList lower upper input.length
          remaining firstCaptures 1 fun captures suffix itemCount =>
            k ((countKey ++ "#count", toString itemCount) :: captures) suffix
  | .optional body =>
      scanOrElse (searchK body input k) fun _ => k [] input
termination_by sizeOf pattern

/-- Execute one resolved sequence. -/
def searchSequenceK {α : Type} (patterns : List SearchPattern) (input : List Char)
    (k : CaptureMap → List Char → Option α) : Option α :=
  match patterns with
  | [] => k [] input
  | pattern :: rest =>
      searchK pattern input fun headCaptures remaining =>
        searchSequenceK rest remaining fun tailCaptures suffix =>
          k (headCaptures ++ tailCaptures) suffix
termination_by sizeOf patterns

/-- Execute source-ordered alternatives. -/
def searchAlternativesK {α : Type} (alternatives : List (List SearchPattern))
    (input : List Char) (k : CaptureMap → List Char → Option α) : Option α :=
  match alternatives with
  | [] => none
  | alternative :: rest =>
      scanOrElse (searchSequenceK alternative input k) fun _ =>
        searchAlternativesK rest input k
termination_by sizeOf alternatives
decreasing_by
  all_goals simp_wf
  all_goals omega

end

end SearchPattern

namespace SearchPlan

/-- Execute a resolved ordered-search plan. -/
def decode (plan : SearchPlan) (source : String) : Option CaptureMap :=
  SearchPattern.searchAlternativesK plan.alternatives source.toList fun captures remaining =>
    if remaining.isEmpty then some captures else none

end SearchPlan

end Triptych
