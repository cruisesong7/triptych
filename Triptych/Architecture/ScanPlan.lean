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
import Triptych.Architecture.Prefix
import Triptych.Architecture.Scanner
import Triptych.Architecture.Unambiguity
import Triptych.Architecture.Value

/-!
# Shared scan-plan intermediate representation

`ScanPlan` is the generation-time IR between Triptych's grammar AST and direct parser
backends. It retains capture nesting in `ScanPattern`, then derives one deterministic,
straight-line operation program. Both Lean and Rust/Verus can execute or compile the same plan.

Unlike the generic scanner, a generated parser does not inspect productions or symbols at
runtime. References are inlined, captures become source spans, and token runs become direct
cursor advances. Compilation is fail-closed: grammars outside this deterministic fragment keep
using the complete verified scanner.

The current shared alphabet is ASCII. That matches the scalar formats for which the direct
backend is enabled and avoids silently assigning different byte and character meanings in Lean
and Rust.
-/

namespace Triptych

/-- One operation in a direct, single-cursor parser. -/
inductive ScanOp where
  | beginCapture (name : String) (keys : List String)
  | endCapture (name : String)
  | literal (character : Char)
  | optionalLiteral (character : Char)
  | tokenRun (token : TokClass) (length : LenSpec)
  deriving Repr, Inhabited, DecidableEq

/-- A structured deterministic pattern before capture nesting is flattened into cursor
    operations. `rest` represents sequence composition; a capture has both a nested body and
    the pattern that follows it. This first-order shape gives semantic proofs an induction
    principle over both dimensions. -/
inductive ScanPattern where
  | empty
  | literal (character : Char) (rest : ScanPattern)
  | optionalLiteral (character : Char) (rest : ScanPattern)
  | tokenRun (token : TokClass) (length : LenSpec) (rest : ScanPattern)
  | capture (name : String) (keys : List String) (body rest : ScanPattern)
  deriving Repr, Inhabited, DecidableEq

namespace ScanPattern

/-- Sequence composition for structured scan patterns. -/
def append : ScanPattern → ScanPattern → ScanPattern
  | .empty, suffix => suffix
  | .literal character rest, suffix => .literal character (rest.append suffix)
  | .optionalLiteral character rest, suffix =>
      .optionalLiteral character (rest.append suffix)
  | .tokenRun token length rest, suffix => .tokenRun token length (rest.append suffix)
  | .capture name keys body rest, suffix =>
      .capture name keys body (rest.append suffix)

/-- Flatten a structured pattern into the straight-line operation vocabulary. -/
def operations : ScanPattern → List ScanOp
  | .empty => []
  | .literal character rest => .literal character :: rest.operations
  | .optionalLiteral character rest => .optionalLiteral character :: rest.operations
  | .tokenRun token length rest => .tokenRun token length :: rest.operations
  | .capture name keys body rest =>
      .beginCapture name keys :: (body.operations ++ .endCapture name :: rest.operations)

/-- Collect capture slots in the same outer-before-inner order as the reference decoder. -/
def captureKeys : ScanPattern → List (String × List String)
  | .empty => []
  | .literal _ rest | .optionalLiteral _ rest | .tokenRun _ _ rest => rest.captureKeys
  | .capture name keys body rest => (name, keys) :: body.captureKeys ++ rest.captureKeys

/-- Flattening commutes with sequence composition. -/
@[simp] theorem operations_append (pattern suffix : ScanPattern) :
    (pattern.append suffix).operations = pattern.operations ++ suffix.operations := by
  induction pattern with
  | empty => rfl
  | literal character rest ih
  | optionalLiteral character rest ih
  | tokenRun token length rest ih =>
      simp [append, operations, ih]
  | capture name keys body rest bodyIH restIH =>
      simp [append, operations, restIH, List.append_assoc]

/-- Capture layout commutes with sequence composition. -/
@[simp] theorem captureKeys_append (pattern suffix : ScanPattern) :
    (pattern.append suffix).captureKeys = pattern.captureKeys ++ suffix.captureKeys := by
  induction pattern with
  | empty => rfl
  | literal character rest ih
  | optionalLiteral character rest ih
  | tokenRun token length rest ih =>
      simp [append, captureKeys, ih]
  | capture name keys body rest bodyIH restIH =>
      simp [append, captureKeys, restIH, List.append_assoc]

end ScanPattern

/-- A structured direct-scanner program specialized from one deterministic acyclic grammar. -/
structure ScanPlan where
  start : String
  pattern : ScanPattern
  deriving Repr, Inhabited, DecidableEq

namespace ScanPlan

/-- Flatten the structured pattern into straight-line cursor operations. -/
def operations (plan : ScanPlan) : List ScanOp :=
  plan.pattern.operations

/-- For each capture slot, the bare and qualified keys emitted into `CaptureMap`. -/
def captureKeys (plan : ScanPlan) : List (String × List String) :=
  plan.pattern.captureKeys

/-- Capture slots in generated result-record order. -/
def captures (plan : ScanPlan) : List String :=
  plan.captureKeys.map (·.1)

end ScanPlan

/-- One source span captured by a scan plan. `stop` is exclusive. -/
structure ScanCapture where
  name : String
  start : Nat
  stop : Nat
  deriving Repr, Inhabited, DecidableEq

/-- Successful execution of a scan plan. -/
structure ScanResult where
  stop : Nat
  captures : List ScanCapture
  captureMap : CaptureMap
  deriving Repr, Inhabited, DecidableEq

private def duplicate? [BEq α] (values : List α) : Bool :=
  values.eraseDups.length != values.length

def ScanPattern.singleAsciiCharacter? (text : String) : Option Char :=
  match text.toList with
  | [character] => if character.toNat ≤ 127 then some character else none
  | _ => none

namespace ScanPattern

/-- A successful one-character literal check exposes the exact source character. -/
theorem singleAsciiCharacter?_eq_some {text : String} {character : Char}
    (hcharacter : singleAsciiCharacter? text = some character) :
    text.toList = [character] := by
  unfold singleAsciiCharacter? at hcharacter
  cases hchars : text.toList with
  | nil => simp [hchars] at hcharacter
  | cons first rest =>
      cases rest with
      | nil =>
          simp only [hchars] at hcharacter
          split at hcharacter
          · simp only [Option.some.injEq] at hcharacter
            subst first
            rfl
          · contradiction
      | cons second rest =>
          simp [hchars] at hcharacter

end ScanPattern

private structure CompiledSequence where
  pattern : ScanPattern

private partial def compileSequence (grammar : Grammar) (qual : String) (fuel : Nat) :
    Triptych.Seq → Except String CompiledSequence
  | [] => pure { pattern := .empty }
  | item :: rest => do
      let head : CompiledSequence ←
        if item.optional then
          match item.sym with
          | .lit text =>
              match ScanPattern.singleAsciiCharacter? text with
              | some character =>
                  pure { pattern := .optionalLiteral character .empty }
              | none =>
                  throw "scan plan: optional literals must be one ASCII character"
          | _ =>
              throw "scan plan: only literal symbols may be optional"
        else
          match item.sym with
          | .lit text =>
              match ScanPattern.singleAsciiCharacter? text with
              | some character =>
                  pure { pattern := .literal character .empty }
              | none =>
                  throw "scan plan: literals must be one ASCII character"
          | .term token length =>
              pure { pattern := .tokenRun token length .empty }
          | .ref name =>
              if fuel == 0 then
                throw "scan plan: production nesting exceeded the grammar size"
              else
                match grammar.prod? name with
                | none =>
                    throw s!"scan plan: unresolved production reference `{name}`"
                | some production =>
                    match production.alts with
                    | [alternative] =>
                        let body ← compileSequence grammar name (fuel - 1) alternative
                        let keys :=
                          if qual.isEmpty then [name] else [name, qual ++ "." ++ name]
                        pure { pattern := .capture name keys body.pattern .empty }
                    | _ =>
                        throw s!"scan plan: production `{name}` must have exactly one alternative"
          | .str =>
              throw "scan plan: quoted-string symbols are not yet supported"
          | .rep _ _ _ _ =>
              throw "scan plan: separated repetition is not yet supported"
      let tail : CompiledSequence ← compileSequence grammar qual fuel rest
      pure { pattern := head.pattern.append tail.pattern }

def ScanPattern.expectedCaptureKeys (qual name : String) : List String :=
  if qual.isEmpty then [name] else [name, qual ++ "." ++ name]

namespace ScanPattern

/-- Structural evidence that a pattern is exactly the supported direct lowering of one grammar
    sequence. The grammar is fixed, while `qual` changes when the proof descends through a named
    production. -/
inductive MirrorsSequence (grammar : Grammar) :
    String → Nat → Triptych.Seq → ScanPattern → Prop
  | empty : MirrorsSequence grammar qual fuel [] .empty
  | optionalLiteral
      (htext : text.toList = [character])
      (tail : MirrorsSequence grammar qual fuel rest tailPattern) :
      MirrorsSequence grammar qual fuel
        ({ sym := .lit text, optional := true } :: rest)
        (.optionalLiteral character tailPattern)
  | literal
      (htext : text.toList = [character])
      (tail : MirrorsSequence grammar qual fuel rest tailPattern) :
      MirrorsSequence grammar qual fuel
        ({ sym := .lit text, optional := false } :: rest)
        (.literal character tailPattern)
  | tokenRun
      (htoken : token = foundToken)
      (hlength : length = foundLength)
      (tail : MirrorsSequence grammar qual fuel rest tailPattern) :
      MirrorsSequence grammar qual fuel
        ({ sym := .term token length, optional := false } :: rest)
        (.tokenRun foundToken foundLength tailPattern)
  | capture
      (hname : name = foundName)
      (hkeys : keys = expectedCaptureKeys qual name)
      (hproduction : grammar.prod? name = some production)
      (halternative : production.alts = [alternative])
      (body : MirrorsSequence grammar name fuel alternative bodyPattern)
      (tail : MirrorsSequence grammar qual (fuel + 1) rest tailPattern) :
      MirrorsSequence grammar qual (fuel + 1)
        ({ sym := .ref name, optional := false } :: rest)
        (.capture foundName keys bodyPattern tailPattern)

/-- Proof-producing source-shape validator. `PLift` keeps the witness computationally erasable
    while allowing the checker to return it in `Option`. -/
def validateSequence (grammar : Grammar) (qual : String) :
    (fuel : Nat) → (sequence : Triptych.Seq) → (pattern : ScanPattern) →
      Option (PLift (MirrorsSequence grammar qual fuel sequence pattern))
  | fuel, [], .empty => some ⟨.empty⟩
  | _, [], _ => none
  | fuel, ⟨.lit text, true⟩ :: rest, .optionalLiteral character tail =>
      match hcharacter : singleAsciiCharacter? text with
      | none => none
      | some found =>
          if heq : found = character then
            match tail.validateSequence grammar qual fuel rest with
            | none => none
            | some htail =>
                some
                  ⟨.optionalLiteral
                    (singleAsciiCharacter?_eq_some (by simpa [heq] using hcharacter))
                    htail.down⟩
          else
            none
  | fuel, ⟨.lit text, false⟩ :: rest, .literal character tail =>
      match hcharacter : singleAsciiCharacter? text with
      | none => none
      | some found =>
          if heq : found = character then
            match tail.validateSequence grammar qual fuel rest with
            | none => none
            | some htail =>
                some
                  ⟨.literal
                    (singleAsciiCharacter?_eq_some (by simpa [heq] using hcharacter))
                    htail.down⟩
          else
            none
  | fuel, ⟨.term token length, false⟩ :: rest,
      .tokenRun foundToken foundLength tail =>
      if htoken : token = foundToken then
        if hlength : length = foundLength then
          match tail.validateSequence grammar qual fuel rest with
          | none => none
          | some htail => some ⟨.tokenRun htoken hlength htail.down⟩
        else
          none
      else
        none
  | 0, ⟨.ref _, false⟩ :: _, .capture _ _ _ _ => none
  | fuel + 1, ⟨.ref name, false⟩ :: rest, .capture foundName keys body tail =>
      if hname : name = foundName then
        if hkeys : keys = expectedCaptureKeys qual name then
          match hproduction : grammar.prod? name with
          | none => none
          | some production =>
              match halternatives : production.alts with
              | [alternative] =>
                  match body.validateSequence grammar name fuel alternative with
                  | none => none
                  | some hbody =>
                      match tail.validateSequence grammar qual (fuel + 1) rest with
                      | none => none
                      | some htail =>
                          some
                            ⟨.capture hname hkeys hproduction halternatives
                              hbody.down htail.down⟩
              | _ => none
        else
          none
      else
        none
  | _, _ :: _, _ => none
termination_by fuel sequence _ => (fuel, sequence.length)

/-- Independently replay a structured pattern against one grammar sequence. This validator is
    intentionally separate from `compileSequence`: direct backends consume a plan only after the
    generated shape passes this check. -/
def matchesSequence (grammar : Grammar) (qual : String) (fuel : Nat)
    (sequence : Triptych.Seq) (pattern : ScanPattern) : Bool :=
  (pattern.validateSequence grammar qual fuel sequence).isSome

/-- Passing the executable validator yields the structural source-shape witness used by proofs. -/
theorem mirrorsSequence_of_matchesSequence {grammar : Grammar} {qual : String} {fuel : Nat}
    {sequence : Triptych.Seq} {pattern : ScanPattern}
    (hmatch : pattern.matchesSequence grammar qual fuel sequence = true) :
    MirrorsSequence grammar qual fuel sequence pattern := by
  unfold matchesSequence at hmatch
  cases hvalidate : pattern.validateSequence grammar qual fuel sequence with
  | none => simp [hvalidate] at hmatch
  | some certificate => exact certificate.down

end ScanPattern

private def consumingOps : List ScanOp → List ScanOp
  | [] => []
  | ((.beginCapture _ _) :: rest) => consumingOps rest
  | ((.endCapture _) :: rest) => consumingOps rest
  | operation :: rest => operation :: consumingOps rest

private def tokenAccepts (token : TokClass) (character : Char) : Bool :=
  decide (token.mem character)

private def greedyBoundarySafe (token : TokClass) (length : LenSpec)
    (remaining : List ScanOp) : Bool :=
  match length with
  | .exactly _ => true
  | _ =>
      match consumingOps remaining with
      | [] => true
      | .literal character :: _ => !tokenAccepts token character
      | _ => false

private def optionalBoundarySafe (character : Char) (remaining : List ScanOp) : Bool :=
  match consumingOps remaining with
  | [] => true
  | .literal next :: _ => character != next
  | .tokenRun token _ :: _ => !tokenAccepts token character
  | .optionalLiteral _ :: _ => false
  | _ => false

private def boundariesSafe : List ScanOp → Bool
  | [] => true
  | .tokenRun token length :: rest =>
      greedyBoundarySafe token length rest && boundariesSafe rest
  | .optionalLiteral character :: rest =>
      optionalBoundarySafe character rest && boundariesSafe rest
  | _ :: rest => boundariesSafe rest

namespace ScanPlan

/-- No named capture slot occurs twice in the flattened plan. -/
def captureNamesUnique (plan : ScanPlan) : Bool :=
  !duplicate? plan.captures

/-- Every greedy or optional operation has a locally deterministic following boundary. -/
def deterministicBoundaries (plan : ScanPlan) : Bool :=
  boundariesSafe plan.operations

/-- Executable certificate required before a direct backend consumes a compiled plan. -/
def certified (plan : ScanPlan) : Bool :=
  plan.captureNamesUnique && plan.deterministicBoundaries

/-- The structured plan exactly mirrors the start production and every inlined reference. -/
def matchesGrammar (plan : ScanPlan) (grammar : Grammar) : Bool :=
  plan.start == grammar.start &&
    match grammar.startProd? with
    | some production =>
        match production.alts with
        | [alternative] =>
            plan.pattern.matchesSequence grammar "" grammar.prods.length alternative
        | _ => false
    | none => false

/-- Complete executable certificate checked before direct backend lowering. In addition to the
    plan-local invariants and structural grammar correspondence, it records the grammar-level
    uniqueness fact needed to identify every successful direct capture map with the decoder's
    selected result. -/
def certifiedFor (plan : ScanPlan) (grammar : Grammar) : Bool :=
  plan.certified && (plan.matchesGrammar grammar && grammar.staticUnique)

/-- Structural evidence connecting a complete plan to the grammar's start production. -/
inductive MirrorsGrammar (plan : ScanPlan) (grammar : Grammar) : Prop where
  | intro
      (start : plan.start = grammar.start)
      (production : Production)
      (alternative : Triptych.Seq)
      (startProduction : grammar.startProd? = some production)
      (singleAlternative : production.alts = [alternative])
      (sequence :
        ScanPattern.MirrorsSequence grammar "" grammar.prods.length alternative plan.pattern)

/-- Passing the complete grammar-shape validator yields a structural start-production witness. -/
theorem mirrorsGrammar_of_matchesGrammar {plan : ScanPlan} {grammar : Grammar}
    (hmatch : plan.matchesGrammar grammar = true) :
    MirrorsGrammar plan grammar := by
  unfold matchesGrammar at hmatch
  have hand := Bool.and_eq_true_iff.mp hmatch
  have hstart : plan.start = grammar.start := by
    simpa using hand.1
  cases hproduction : grammar.startProd? with
  | none => simp [hproduction] at hand
  | some production =>
      cases halternatives : production.alts with
      | nil => simp [hproduction, halternatives] at hand
      | cons alternative rest =>
          cases rest with
          | nil =>
              have hsequence :
                  plan.pattern.matchesSequence grammar "" grammar.prods.length
                    alternative = true := by
                simpa [hproduction, halternatives] using hand.2
              exact .intro hstart production alternative hproduction halternatives
                (ScanPattern.mirrorsSequence_of_matchesSequence hsequence)
          | cons next rest =>
              simp [hproduction, halternatives] at hand

end ScanPlan

private def compileUniqueScanPlan (grammar : Grammar) : Except String ScanPlan := do
  if !grammar.refsResolve then
    throw "scan plan: every production reference must resolve"
  if let some cycle := grammar.cycle? then
    throw s!"scan plan: recursive grammars are unsupported: {String.intercalate " -> " cycle}"
  let root ← match grammar.startProd? with
    | some production => pure production
    | none => throw s!"scan plan: start production `{grammar.start}` is missing"
  let alternative ← match root.alts with
    | [alternative] => pure alternative
    | _ => throw "scan plan: the start production must have exactly one alternative"
  let compiled ← compileSequence grammar "" grammar.prods.length alternative
  let operations := compiled.pattern.operations
  let captureKeys := compiled.pattern.captureKeys
  let captures := captureKeys.map (·.1)
  if duplicate? captures then
    throw "scan plan: each named capture may occur at most once"
  if !boundariesSafe operations then
    throw "scan plan: a variable-width or optional field has no deterministic character boundary"
  pure { start := grammar.start, pattern := compiled.pattern }

/-- Compile a deterministic acyclic grammar into a direct single-cursor plan. -/
def compileScanPlan (grammar : Grammar) : Except String ScanPlan := do
  if grammar.staticUnique then
    let plan ← compileUniqueScanPlan grammar
    if plan.certifiedFor grammar then
      pure plan
    else
      throw "scan plan: internal certification failed"
  else
    throw "scan plan: the grammar must pass the static uniqueness checker"

/-- Every successfully compiled plan comes from a grammar with an all-input uniqueness
    certificate available through `GrammarDecodeUnique.of_staticUnique`. -/
theorem compileScanPlan_staticUnique {grammar : Grammar} {plan : ScanPlan}
    (hcompile : compileScanPlan grammar = .ok plan) :
    grammar.staticUnique = true := by
  cases hunique : grammar.staticUnique with
  | false => simp [compileScanPlan, hunique] at hcompile
  | true => rfl

/-- A successfully compiled plan has passed the executable structural certificate checked by
    every direct backend. -/
theorem compileScanPlan_certifiedFor {grammar : Grammar} {plan : ScanPlan}
    (hcompile : compileScanPlan grammar = .ok plan) :
    plan.certifiedFor grammar = true := by
  unfold compileScanPlan at hcompile
  split at hcompile
  · cases hplan : compileUniqueScanPlan grammar with
    | error message =>
        rw [hplan] at hcompile
        change Except.error message = Except.ok plan at hcompile
        contradiction
    | ok candidate =>
        rw [hplan] at hcompile
        change
          (if candidate.certifiedFor grammar then
            Except.ok candidate
          else
            Except.error "scan plan: internal certification failed") =
            Except.ok plan at hcompile
        by_cases hcertified : candidate.certifiedFor grammar = true
        · rw [if_pos hcertified] at hcompile
          injection hcompile with heq
          subst candidate
          exact hcertified
        · rw [if_neg hcertified] at hcompile
          contradiction
  · change
      Except.error "scan plan: the grammar must pass the static uniqueness checker" =
        Except.ok plan at hcompile
    contradiction

/-- A successfully compiled plan has passed the executable structural certificate checked by
    every direct backend. -/
theorem compileScanPlan_certified {grammar : Grammar} {plan : ScanPlan}
    (hcompile : compileScanPlan grammar = .ok plan) :
    plan.certified = true :=
  (Bool.and_eq_true_iff.mp (compileScanPlan_certifiedFor hcompile)).1

/-- A successfully compiled pattern independently validates against its source grammar. -/
theorem compileScanPlan_matchesGrammar {grammar : Grammar} {plan : ScanPlan}
    (hcompile : compileScanPlan grammar = .ok plan) :
    plan.matchesGrammar grammar = true :=
  (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp (compileScanPlan_certifiedFor hcompile)).2).1

/-- The complete plan certificate includes the source grammar's all-input uniqueness check. -/
theorem compileScanPlan_certifiedStaticUnique {grammar : Grammar} {plan : ScanPlan}
    (hcompile : compileScanPlan grammar = .ok plan) :
    grammar.staticUnique = true :=
  (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp (compileScanPlan_certifiedFor hcompile)).2).2

/-- Successful compilation returns a structural witness connecting the plan to the source
    grammar's start production and every recursively inlined reference. -/
theorem compileScanPlan_mirrorsGrammar {grammar : Grammar} {plan : ScanPlan}
    (hcompile : compileScanPlan grammar = .ok plan) :
    ScanPlan.MirrorsGrammar plan grammar :=
  ScanPlan.mirrorsGrammar_of_matchesGrammar (compileScanPlan_matchesGrammar hcompile)

/-- Successful compilation guarantees unique generated capture slots. -/
theorem compileScanPlan_captureNamesUnique {grammar : Grammar} {plan : ScanPlan}
    (hcompile : compileScanPlan grammar = .ok plan) :
    plan.captureNamesUnique = true :=
  (Bool.and_eq_true_iff.mp (compileScanPlan_certified hcompile)).1

/-- Successful compilation guarantees deterministic greedy and optional boundaries. -/
theorem compileScanPlan_deterministicBoundaries {grammar : Grammar} {plan : ScanPlan}
    (hcompile : compileScanPlan grammar = .ok plan) :
    plan.deterministicBoundaries = true :=
  (Bool.and_eq_true_iff.mp (compileScanPlan_certified hcompile)).2

namespace ScanPlan

/-- One open capture frame. `captureMark` records where nested captures begin in the ordered
    capture map, so closing the frame can insert its own entries before those children. -/
structure OpenCapture where
  name : String
  keys : List String
  start : Nat
  captureMark : Nat

/-- Internal cursor state shared with verified lowerings. -/
structure ExecutionState where
  position : Nat := 0
  starts : List OpenCapture := []
  captures : List ScanCapture := []
  captureMap : CaptureMap := []

/-- Remove and return the open frame for a named capture. -/
def takeStart? (name : String) :
    List OpenCapture → Option (OpenCapture × List OpenCapture)
  | [] => none
  | entry :: rest =>
      if entry.name == name then
        some (entry, rest)
      else
        (takeStart? name rest).map fun result => (result.1, entry :: result.2)

/-- Select the width used by the abstract scan-plan operation. -/
def tokenWidth (token : TokClass) (length : LenSpec) (input : List Char) : Nat :=
  match length with
  | .exactly width => width
  | _ => (input.takeWhile fun character => decide (token.mem character)).length

/-- Recover the text consumed between two cursor positions. The length-difference form mirrors
    the suffix-based specification matcher and avoids any hidden arithmetic assumption. -/
def capturedText (input : List Char) (start stop : Nat) : String :=
  String.ofList
    ((input.drop start).take ((input.drop start).length - (input.drop stop).length))

/-- Execute one abstract scan-plan operation. -/
def executeOperation (input : List Char) (operation : ScanOp)
    (state : ExecutionState) : Option ExecutionState :=
  match operation with
  | .beginCapture name keys =>
      some
        { state with
          starts :=
            { name, keys, start := state.position, captureMark := state.captureMap.length } ::
              state.starts }
  | .endCapture name => do
      let (frame, starts) ← takeStart? name state.starts
      let text := capturedText input frame.start state.position
      let ownCaptures := frame.keys.map fun key => (key, text)
      let captureMap :=
        state.captureMap.take frame.captureMark ++ ownCaptures ++
          state.captureMap.drop frame.captureMark
      some
        { state with
          starts
          captures :=
            state.captures ++ [{ name, start := frame.start, stop := state.position }]
          captureMap }
  | .literal character =>
      match (input.drop state.position).head? with
      | some actual =>
          if actual == character then
            some { state with position := state.position + 1 }
          else
            none
      | none => none
  | .optionalLiteral character =>
      let next :=
        match (input.drop state.position).head? with
        | some actual => if actual == character then state.position + 1 else state.position
        | none => state.position
      some { state with position := next }
  | .tokenRun token length =>
      let suffix := input.drop state.position
      let width := tokenWidth token length suffix
      if termPrefixOk token length suffix width then
        some { state with position := state.position + width }
      else
        none

/-- Reference execution of abstract scan-plan operations. -/
def executeOperations (input : List Char) :
    List ScanOp → ExecutionState → Option ExecutionState
  | [], state => some state
  | operation :: rest, state => do
      let next ← executeOperation input operation state
      executeOperations input rest next

/-- Execute the structured pattern before flattening. -/
def executePattern (input : List Char) :
    ScanPattern → ExecutionState → Option ExecutionState
  | .empty, state => some state
  | .literal character rest, state => do
      let next ← executeOperation input (.literal character) state
      executePattern input rest next
  | .optionalLiteral character rest, state => do
      let next ← executeOperation input (.optionalLiteral character) state
      executePattern input rest next
  | .tokenRun token length rest, state => do
      let next ← executeOperation input (.tokenRun token length) state
      executePattern input rest next
  | .capture name keys body rest, state => do
      let opened ← executeOperation input (.beginCapture name keys) state
      let afterBody ← executePattern input body opened
      let closed ← executeOperation input (.endCapture name) afterBody
      executePattern input rest closed

/-- Operation execution composes over list append. -/
theorem executeOperations_append (input : List Char) (left right : List ScanOp)
    (state : ExecutionState) :
    executeOperations input (left ++ right) state =
      (executeOperations input left state).bind (executeOperations input right) := by
  induction left generalizing state with
  | nil => rfl
  | cons operation left ih =>
      simp only [List.cons_append, executeOperations]
      cases hstep : executeOperation input operation state with
      | none => simp
      | some next =>
          simp [ih]

/-- Flattening a structured pattern preserves its complete execution state. -/
theorem executePattern_eq_operations (input : List Char) (pattern : ScanPattern)
    (state : ExecutionState) :
    executePattern input pattern state =
      executeOperations input pattern.operations state := by
  induction pattern generalizing state with
  | empty => rfl
  | literal character rest ih
  | optionalLiteral character rest ih
  | tokenRun token length rest ih =>
      simp only [executePattern, ScanPattern.operations, executeOperations]
      cases hstep : executeOperation input _ state with
      | none => simp
      | some next => simp [ih]
  | capture name keys body rest bodyIH restIH =>
      simp [executePattern, ScanPattern.operations, executeOperations,
        executeOperations_append, bodyIH, restIH]

/-- Execute a plan directly in Lean. Backends should compile this behavior into straight-line
    target code rather than ship this interpreter in generated artifacts. -/
def run (plan : ScanPlan) (source : String) : Option ScanResult := do
  let input := source.toList
  let state ← executeOperations input plan.operations {}
  if state.position == input.length && state.starts.isEmpty then
    some
      { stop := state.position
        captures := state.captures
        captureMap := state.captureMap }
  else
    none

/-- Execute the structured pattern before flattening. This is a proof-facing definition;
    generated backends consume `operations` or its verified cursor lowering. -/
def runPattern (plan : ScanPlan) (source : String) : Option ScanResult := do
  let input := source.toList
  let state ← executePattern input plan.pattern {}
  if state.position == input.length && state.starts.isEmpty then
    some
      { stop := state.position
        captures := state.captures
        captureMap := state.captureMap }
  else
    none

/-- The flat operation program and structured pattern have identical complete results. -/
@[simp] theorem run_eq_runPattern (plan : ScanPlan) (source : String) :
    plan.run source = plan.runPattern source := by
  unfold run runPattern ScanPlan.operations
  simp only
  rw [← executePattern_eq_operations]

/-- Recover a captured substring from a successful plan result. -/
def captureText (capture : ScanCapture) (source : String) : String :=
  String.ofList ((source.toList.drop capture.start).take (capture.stop - capture.start))

/-- Return the ordered capture map accumulated by the scanner. -/
def toCaptureMap (_plan : ScanPlan) (result : ScanResult) (_source : String) : CaptureMap :=
  result.captureMap

/-- Execute a plan and return its captured strings. -/
def decode (plan : ScanPlan) (source : String) : Option CaptureMap :=
  (plan.run source).map fun result => plan.toCaptureMap result source

/-- Execute the direct plan as a fast path, then continue with the complete scanner if the
    straight-line program rejects. Soundness of the fast result and completeness of the
    fallback are proved in `Triptych.Theorems.ScanPlan`. -/
def decodeCertified (plan : ScanPlan) (grammar : Grammar) (source : String) :
    Option CaptureMap :=
  (plan.decode source).orElse fun _ => scanSearch grammar source

/-- A successful direct result is returned without consulting the complete scanner. -/
theorem decodeCertified_eq_of_decode_eq_some {plan : ScanPlan} {grammar : Grammar}
    {source : String} {captures : CaptureMap}
    (hdecode : plan.decode source = some captures) :
    plan.decodeCertified grammar source = some captures := by
  simp [decodeCertified, hdecode]

/-- When the direct path rejects, certified decoding continues with the complete scanner. -/
theorem decodeCertified_eq_scanSearch_of_decode_eq_none {plan : ScanPlan} {grammar : Grammar}
    {source : String}
    (hdecode : plan.decode source = none) :
    plan.decodeCertified grammar source = scanSearch grammar source := by
  simp [decodeCertified, hdecode]

/-- Decode through the structured pattern before operation flattening. -/
def decodePattern (plan : ScanPlan) (source : String) : Option CaptureMap :=
  (plan.runPattern source).map fun result => plan.toCaptureMap result source

/-- Structured and flattened plan decoding are extensionally identical. -/
@[simp] theorem decode_eq_decodePattern (plan : ScanPlan) (source : String) :
    plan.decode source = plan.decodePattern source := by
  simp [decode, decodePattern]

end ScanPlan

end Triptych
