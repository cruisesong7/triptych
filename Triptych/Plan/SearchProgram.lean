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

import Triptych.Plan.SearchPlan

/-!
# Continuation-fused ordered-search programs

`SearchPlan` removes production lookup while retaining source sequences and alternatives as
lists. `SearchProgram` performs the next staging step: sequence tails become explicit
continuations and ordered alternatives become binary choices. Backends can compile this tree
into parser states instead of interpreting grammar tables or walking sequence lists.

The program remains complete for the full acyclic grammar surface accepted by `SearchPlan`.
Choice preserves source order, optional bodies are tried before absence, and repetition retains
the scanner's stop-before-continue policy.
-/

namespace Triptych

/-- Backend-neutral control flow for complete ordered search. -/
inductive SearchCode where
  | accept
  | fail
  | literal (text : String) (next : SearchCode)
  | stringLiteral (next : SearchCode)
  | tokenRun (token : TokClass) (length : LenSpec) (next : SearchCode)
  | capture (keys : List String) (body next : SearchCode)
  | choice (first second : SearchCode)
  | repetition (separator : String) (item : SearchCode)
      (lower : Nat) (upper : Option Nat) (countKey : String) (next : SearchCode)
  deriving Repr, Inhabited, DecidableEq

/-- A staged complete parser for one resolved search plan. -/
structure SearchProgram where
  start : String
  code : SearchCode
  deriving Repr, Inhabited, DecidableEq

namespace SearchCode

/-- Whether a token length admits exactly one candidate width before consulting the
    continuation. -/
def fixedWidth : LenSpec → Bool
  | .exactly _ => true
  | .between lower upper => lower == upper
  | .atLeastOne => false

/-- A conservative check that execution selects at most one candidate before consulting its
    continuation. This deliberately excludes alternatives, variable-width runs, strings, and
    repetitions. -/
def committed : SearchCode → Bool
  | .accept | .fail => true
  | .literal _ next => next.committed
  | .tokenRun _ length next => fixedWidth length && next.committed
  | .capture _ body next => body.committed && next.committed
  | .stringLiteral _ | .choice _ _ | .repetition _ _ _ _ _ _ => false

/-- Merge two ordered branches while sharing only prefixes whose execution is mechanically
    known to be continuation-independent. -/
def merge : SearchCode → SearchCode → SearchCode
  | .fail, second => second
  | first, .fail => first
  | .literal firstText firstNext, .literal secondText secondNext =>
      if firstText = secondText then
        .literal firstText (merge firstNext secondNext)
      else
        .choice (.literal firstText firstNext) (.literal secondText secondNext)
  | first@(.tokenRun firstToken firstLength firstNext),
      second@(.tokenRun secondToken secondLength secondNext) =>
      if firstToken = secondToken ∧ firstLength = secondLength ∧
          fixedWidth firstLength = true then
        .tokenRun firstToken firstLength (merge firstNext secondNext)
      else
        .choice first second
  | first@(.capture firstKeys firstBody firstNext),
      second@(.capture secondKeys secondBody secondNext) =>
      if firstKeys = secondKeys ∧ firstBody = secondBody ∧ firstBody.committed = true then
        .capture firstKeys firstBody (merge firstNext secondNext)
      else
        .choice first second
  | first, second => .choice first second
termination_by structural first _ => first

/-- Number of control-flow constructors in a staged search program. This is a static generated-code
    size measure, not a runtime step count. -/
def nodeCount : SearchCode → Nat
  | .accept | .fail => 1
  | .literal _ next | .stringLiteral next | .tokenRun _ _ next =>
      1 + next.nodeCount
  | .capture _ body next =>
      1 + body.nodeCount + next.nodeCount
  | .choice first second =>
      1 + first.nodeCount + second.nodeCount
  | .repetition _ item _ _ _ next =>
      1 + item.nodeCount + next.nodeCount

/-- Remove statically dead failure arms and share certified single-result prefixes.

`compileAlternatives` deliberately has a uniform list-shaped definition and therefore leaves
`choice branch fail` at the end of every alternative list. It also duplicates common prefixes
across source alternatives. This pass erases the administrative states and shares a common
literal or capture only when doing so preserves the exact source-ordered search. -/
def reduce : SearchCode → SearchCode
  | .accept => .accept
  | .fail => .fail
  | .literal text next => .literal text next.reduce
  | .stringLiteral next => .stringLiteral next.reduce
  | .tokenRun token length next => .tokenRun token length next.reduce
  | .capture keys body next => .capture keys body.reduce next.reduce
  | .choice first second => merge first.reduce second.reduce
  | .repetition separator item lower upper countKey next =>
      .repetition separator item.reduce lower upper countKey next.reduce
termination_by structural code => code

mutual

/-- Fuse one resolved pattern with an explicit continuation. -/
def compilePattern : SearchPattern → SearchCode → SearchCode
  | .literal text, next => .literal text next
  | .stringLiteral, next => .stringLiteral next
  | .tokenRun token length, next => .tokenRun token length next
  | .capture _ keys alternatives, next =>
      .capture keys (compileAlternatives alternatives .accept) next
  | .repetition separator item lower upper countKey, next =>
      .repetition separator (compilePattern item .accept)
        lower upper countKey next
  | .optional body, next =>
      .choice (compilePattern body next) next

/-- Fuse a source sequence with an explicit continuation. -/
def compileSequence : List SearchPattern → SearchCode → SearchCode
  | [], next => next
  | pattern :: rest, next =>
      compilePattern pattern (compileSequence rest next)

/-- Fuse source-ordered alternatives with an explicit continuation. -/
def compileAlternatives :
    List (List SearchPattern) → SearchCode → SearchCode
  | [], _next => .fail
  | alternative :: alternatives, next =>
      .choice
        (compileSequence alternative next)
        (compileAlternatives alternatives next)

end

mutual

/-- Structural evidence that one fused state was compiled from a resolved pattern and
    continuation. -/
inductive CompilesPattern : SearchPattern → SearchCode → SearchCode → Prop
  | literal :
      CompilesPattern (.literal text) next (.literal text next)
  | stringLiteral :
      CompilesPattern .stringLiteral next (.stringLiteral next)
  | tokenRun :
      CompilesPattern (.tokenRun token length) next (.tokenRun token length next)
  | capture
      (body : CompilesAlternatives alternatives .accept bodyCode) :
      CompilesPattern (.capture name keys alternatives) next
        (.capture keys bodyCode next)
  | repetition
      (body : CompilesPattern item .accept itemCode) :
      CompilesPattern (.repetition separator item lower upper countKey) next
        (.repetition separator itemCode lower upper countKey next)
  | optional
      (body : CompilesPattern pattern next bodyCode) :
      CompilesPattern (.optional pattern) next (.choice bodyCode next)

/-- Structural evidence for continuation fusion of one sequence. -/
inductive CompilesSequence : List SearchPattern → SearchCode → SearchCode → Prop
  | empty :
      CompilesSequence [] next next
  | cons
      (tail : CompilesSequence patterns next tailCode)
      (head : CompilesPattern pattern tailCode headCode) :
      CompilesSequence (pattern :: patterns) next headCode

/-- Structural evidence for continuation fusion of ordered alternatives. -/
inductive CompilesAlternatives :
    List (List SearchPattern) → SearchCode → SearchCode → Prop
  | empty :
      CompilesAlternatives [] next .fail
  | cons
      (head : CompilesSequence alternative next headCode)
      (tail : CompilesAlternatives alternatives next tailCode) :
      CompilesAlternatives (alternative :: alternatives) next
        (.choice headCode tailCode)

end

mutual

/-- Every compiled pattern carries a structural lowering certificate. -/
theorem compilePattern_correct (pattern : SearchPattern) (next : SearchCode) :
    CompilesPattern pattern next (compilePattern pattern next) := by
  cases pattern with
  | literal => exact .literal
  | stringLiteral => exact .stringLiteral
  | tokenRun => exact .tokenRun
  | capture name keys alternatives =>
      exact .capture (compileAlternatives_correct alternatives .accept)
  | repetition separator item lower upper countKey =>
      exact .repetition (compilePattern_correct item .accept)
  | optional pattern =>
      exact .optional (compilePattern_correct pattern next)

/-- Every compiled sequence carries a structural lowering certificate. -/
theorem compileSequence_correct (patterns : List SearchPattern) (next : SearchCode) :
    CompilesSequence patterns next (compileSequence patterns next) := by
  cases patterns with
  | nil => exact .empty
  | cons pattern patterns =>
      exact .cons
        (compileSequence_correct patterns next)
        (compilePattern_correct pattern (compileSequence patterns next))

/-- Every compiled alternative list carries a structural lowering certificate. -/
theorem compileAlternatives_correct (alternatives : List (List SearchPattern))
    (next : SearchCode) :
    CompilesAlternatives alternatives next (compileAlternatives alternatives next) := by
  cases alternatives with
  | nil => exact .empty
  | cons alternative alternatives =>
      exact .cons
        (compileSequence_correct alternative next)
        (compileAlternatives_correct alternatives next)

end

end SearchCode

/-- Fuse a resolved search plan into uniform continuation control flow. -/
def lowerSearchPlanRaw (plan : SearchPlan) : SearchProgram :=
  { start := plan.start
    code := SearchCode.compileAlternatives plan.alternatives .accept }

/-- Fuse a resolved search plan and erase administrative failure states before emission. -/
def lowerSearchPlan (plan : SearchPlan) : SearchProgram :=
  let raw := lowerSearchPlanRaw plan
  { raw with code := raw.code.reduce }

namespace SearchCode

mutual

/-- Execute one staged parser state and pass its selected capture map and suffix to `k`. -/
def runK {α : Type} (code : SearchCode) (input : List Char)
    (k : CaptureMap → List Char → Option α) : Option α :=
  match code with
  | .accept => k [] input
  | .fail => none
  | .literal text next =>
      let characters := text.toList
      if characters.isPrefixOf input then
        runK next (input.drop characters.length) k
      else
        none
  | .stringLiteral next =>
      (List.range (input.length + 1)).findSome? fun width =>
        if stringPrefixOk input width then runK next (input.drop width) k else none
  | .tokenRun token length next =>
      (List.range (input.length + 1)).findSome? fun width =>
        if termPrefixOk token length input width then
          runK next (input.drop width) k
        else
          none
  | .capture keys body next =>
      runK body input fun bodyCaptures remaining =>
        let consumed := String.ofList (input.take (input.length - remaining.length))
        runK next remaining fun tailCaptures suffix =>
          k (keys.map (·, consumed) ++ bodyCaptures ++ tailCaptures) suffix
  | .choice first second =>
      scanOrElse (runK first input k) fun _ => runK second input k
  | .repetition separator item lower upper countKey next =>
      runK item input fun firstCaptures remaining =>
        scanStarK (fun itemInput itemK => runK item itemInput itemK)
          separator.toList lower upper input.length
          remaining firstCaptures 1 fun captures suffix itemCount =>
            runK next suffix fun tailCaptures finalSuffix =>
              k (((countKey ++ "#count", toString itemCount) :: captures) ++
                tailCaptures) finalSuffix
termination_by sizeOf code

end

end SearchCode

namespace SearchProgram

/-- Execute a staged search program on one complete source string. -/
def decode (program : SearchProgram) (source : String) : Option CaptureMap :=
  program.code.runK source.toList fun captures remaining =>
    if remaining.isEmpty then some captures else none

end SearchProgram

end Triptych
