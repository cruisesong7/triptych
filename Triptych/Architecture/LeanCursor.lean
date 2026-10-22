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

import Triptych.Architecture.CursorProgram

/-!
# Streaming Lean cursor

`CursorProgram` is the backend-neutral verified IR. Its reference Lean executor stores a numeric
position and recovers the current suffix with `List.drop` at every instruction. This module keeps
the same proof-facing state while threading the unconsumed suffix directly.

The streaming executor is extensionally equal to `CursorProgram.run`, including captures. It is
therefore a backend implementation of the verified IR rather than a second parser specification.
-/

namespace Triptych

namespace LeanCursor

/-- Runtime state for the Lean backend. `remaining` caches the suffix at `core.position`. -/
structure State where
  core : CursorProgram.ExecutionState := {}
  remaining : List Char := []

/-- Recover the canonical streaming state associated with a reference cursor state. -/
def ofCore (input : List Char) (core : CursorProgram.ExecutionState) : State :=
  { core
    remaining := input.drop core.position }

/-- Initial state for one input. -/
def initial (input : List Char) : State :=
  { remaining := input }

/-- Open a capture without touching the source cursor. -/
@[inline] def beginCapture (name : String) (keys : List String) (state : State) :
    Option State :=
  some
    { state with
      core :=
        { state.core with
          starts :=
            { name
              keys
              start := state.core.position
              captureMark := state.core.captureMap.length } :: state.core.starts } }

/-- Close a capture. Captured text is still materialized here; a later lowering can defer that
    allocation until the complete input has been accepted. -/
@[inline] def endCapture (input : List Char) (name : String) (state : State) :
    Option State :=
  (CursorProgram.executeOperation input (.endCapture name) state.core).map fun core =>
    { state with core }

/-- Consume one required character from the cached suffix. -/
@[inline] def expect (character : Char) (state : State) : Option State :=
  match state.remaining with
  | actual :: tail =>
      if actual == character then
        some
          { core := { state.core with position := state.core.position + 1 }
            remaining := tail }
      else
        none
  | [] => none

/-- Consume one optional character from the cached suffix. -/
@[inline] def consumeOptional (character : Char) (state : State) : Option State :=
  match state.remaining with
  | actual :: tail =>
      if actual == character then
        some
          { core := { state.core with position := state.core.position + 1 }
            remaining := tail }
      else
        some state
  | [] => some state

/-- Scan the maximal prefix accepted by one token class, returning its character length and the
    unconsumed suffix in one traversal. -/
def scanToken (token : TokClass) : List Char → Nat × List Char
  | [] => (0, [])
  | input@(character :: rest) =>
      if token.mem character then
        let (width, remaining) := scanToken token rest
        (width + 1, remaining)
      else
        (0, input)

/-- The fused token scan computes the same width and suffix as `takeWhile` followed by `drop`. -/
theorem scanToken_eq (token : TokClass) (input : List Char) :
    scanToken token input =
      let width := (input.takeWhile fun character => decide (token.mem character)).length
      (width, input.drop width) := by
  induction input with
  | nil => rfl
  | cons character rest ih =>
      by_cases hmem : token.mem character
      · simp only [scanToken, hmem, ite_true, ih, decide_eq_true_eq, List.takeWhile_cons,
          List.length_cons]
        rw [List.drop_succ_cons]
      · simp [scanToken, hmem]

/-- Consume one lowered token run from the cached suffix. -/
@[inline] def consumeRun (token : TokClass) (run : CursorRun) (state : State) :
    Option State :=
  match run with
  | .fixed width =>
      if termPrefixOk token run.toLenSpec state.remaining width then
        some
          { core := { state.core with position := state.core.position + width }
            remaining := state.remaining.drop width }
      else
        none
  | .greedyBetween _ _ | .greedyAtLeastOne =>
      let (width, remaining) := scanToken token state.remaining
      if termPrefixOk token run.toLenSpec state.remaining width then
        some
          { core := { state.core with position := state.core.position + width }
            remaining }
      else
        none

/-- Execute one instruction using the streaming representation. -/
@[inline] def executeOperation (input : List Char) (operation : CursorOp) (state : State) :
    Option State :=
  match operation with
  | .beginCapture name keys => beginCapture name keys state
  | .endCapture name => endCapture input name state
  | .expect character => expect character state
  | .consumeOptional character => consumeOptional character state
  | .consumeRun token run => consumeRun token run state

/-- Execute a sequence of instructions while retaining the current suffix. -/
def executeOperations (input : List Char) :
    List CursorOp → State → Option State
  | [], state => some state
  | operation :: rest, state => do
      let next ← executeOperation input operation state
      executeOperations input rest next

/-- Execute a lowered cursor program with constant-time access to the current list suffix. -/
def run (program : CursorProgram) (source : String) : Option ScanResult := do
  let input := source.toList
  let state ← executeOperations input program.operations (initial input)
  if state.core.position == input.length && state.core.starts.isEmpty then
    some
      { stop := state.core.position
        captures := state.core.captures
        captureMap := state.core.captureMap }
  else
    none

/-- Execute a lowered program and recover captured strings. -/
def decode (program : CursorProgram) (source : String) : Option CaptureMap :=
  (run program source).map (·.captureMap)

private theorem drop_succ_of_drop_eq_cons {input : List Char} {position : Nat}
    {actual : Char} {tail : List Char}
    (hdrop : input.drop position = actual :: tail) :
    input.drop (position + 1) = tail := by
  have hposition : position < input.length := by
    have hlength := congrArg List.length hdrop
    simp only [List.length_drop, List.length_cons] at hlength
    omega
  have hsplit :=
    congrArg List.tail (List.drop_eq_getElem_cons (l := input) hposition)
  rw [hdrop] at hsplit
  simpa only [List.tail_cons] using hsplit.symm

/-- One streaming instruction is the reference instruction followed by suffix caching. -/
theorem executeOperation_ofCore (input : List Char) (operation : CursorOp)
    (core : CursorProgram.ExecutionState) :
    executeOperation input operation (ofCore input core) =
      (CursorProgram.executeOperation input operation core).map (ofCore input) := by
  cases operation with
  | beginCapture name keys =>
      rfl
  | endCapture name =>
      unfold executeOperation endCapture
      cases hstart : ScanPlan.takeStart? name core.starts with
      | none =>
          simp [CursorProgram.executeOperation, hstart, ofCore]
      | some result =>
          simp [CursorProgram.executeOperation, hstart, ofCore]
  | expect character =>
      unfold executeOperation expect ofCore CursorProgram.executeOperation
      cases hdrop : input.drop core.position with
      | nil => simp
      | cons actual tail =>
          by_cases heq : actual == character
          · have htail := drop_succ_of_drop_eq_cons hdrop
            simp [heq, htail]
          · simp [heq]
  | consumeOptional character =>
      unfold executeOperation consumeOptional ofCore CursorProgram.executeOperation
      cases hdrop : input.drop core.position with
      | nil => simp [hdrop]
      | cons actual tail =>
          by_cases heq : actual == character
          · have htail := drop_succ_of_drop_eq_cons hdrop
            simp [heq, htail]
          · simp [hdrop, heq]
  | consumeRun token run =>
      cases run with
      | fixed width =>
          simp only [executeOperation, consumeRun, ofCore, CursorProgram.executeOperation]
          by_cases hprefix :
              termPrefixOk token (CursorRun.fixed width).toLenSpec
                (input.drop core.position) width = true
          · simp only [CursorRun.width, hprefix, ite_true, Option.map_some]
            simp [ofCore, List.drop_drop]
          · simp [CursorRun.width, hprefix]
      | greedyBetween lower upper =>
          simp only [executeOperation, consumeRun, ofCore, CursorProgram.executeOperation]
          simp only [scanToken_eq]
          by_cases hprefix :
              termPrefixOk token (CursorRun.greedyBetween lower upper).toLenSpec
                (input.drop core.position)
                ((input.drop core.position).takeWhile
                  fun character => decide (token.mem character)).length = true
          · simp only [CursorRun.width, hprefix, ite_true, Option.map_some]
            simp [ofCore, List.drop_drop]
          · simp [CursorRun.width, hprefix]
      | greedyAtLeastOne =>
          simp only [executeOperation, consumeRun, ofCore, CursorProgram.executeOperation]
          simp only [scanToken_eq]
          by_cases hprefix :
              termPrefixOk token CursorRun.greedyAtLeastOne.toLenSpec
                (input.drop core.position)
                ((input.drop core.position).takeWhile
                  fun character => decide (token.mem character)).length = true
          · simp only [CursorRun.width, hprefix, ite_true, Option.map_some]
            simp [ofCore, List.drop_drop]
          · simp [CursorRun.width, hprefix]

/-- Streaming execution preserves the complete reference state after every operation sequence. -/
theorem executeOperations_ofCore (input : List Char) (operations : List CursorOp)
    (core : CursorProgram.ExecutionState) :
    executeOperations input operations (ofCore input core) =
      (CursorProgram.executeOperations input operations core).map (ofCore input) := by
  induction operations generalizing core with
  | nil => rfl
  | cons operation operations ih =>
      simp only [executeOperations, CursorProgram.executeOperations]
      rw [executeOperation_ofCore]
      cases hstep : CursorProgram.executeOperation input operation core with
      | none => simp
      | some next => simp [ih]

@[simp] theorem initial_eq_ofCore (input : List Char) :
    initial input = ofCore input {} := by
  simp [initial, ofCore]

/-- The streaming Lean runtime is extensionally equal to the verified cursor-program semantics. -/
@[simp] theorem run_eq_cursorProgram (program : CursorProgram) (source : String) :
    run program source = CursorProgram.run program source := by
  unfold run CursorProgram.run
  dsimp only
  rw [initial_eq_ofCore, executeOperations_ofCore]
  cases hrun :
      CursorProgram.executeOperations source.toList program.operations
        ({} : CursorProgram.ExecutionState) with
  | none => simp
  | some state => simp [ofCore]

/-- Streaming decoding preserves the complete captured-string result. -/
@[simp] theorem decode_eq_cursorProgram (program : CursorProgram) (source : String) :
    decode program source = CursorProgram.decode program source := by
  simp [decode, CursorProgram.decode]

end LeanCursor

end Triptych
