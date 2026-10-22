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

import Triptych.Runtime.LeanCursor

/-!
# Deferred-capture Lean cursor

The proof-facing cursor materializes every captured substring while parsing. This runtime stores
only source spans, so rejected inputs allocate no captured strings and successful parsers can
project generated typed views without first constructing a string-keyed `CaptureMap`.

`run_eq_cursorProgram` proves that materializing the deferred spans recovers the complete
proof-facing result. The emitter can therefore use this runtime without changing any generated
specification or parser contract.
-/

namespace Triptych

namespace LeanSpanCursor

/-- One capture-map entry represented by its source span. -/
structure SpanBinding where
  key : String
  start : Nat
  stop : Nat
  deriving Repr, Inhabited, DecidableEq

abbrev SpanMap := List SpanBinding

namespace SpanMap

/-- Materialize deferred source spans as the legacy capture-map representation. -/
def materialize (input : List Char) : SpanMap → CaptureMap
  | [] => []
  | binding :: bindings =>
      (binding.key, ScanPlan.capturedText input binding.start binding.stop) ::
        materialize input bindings

/-- Read the first captured string stored under a key. -/
def toEnv (input : List Char) : SpanMap → String → Option String
  | [], _ => none
  | binding :: bindings, key =>
      if binding.key == key then
        some (ScanPlan.capturedText input binding.start binding.stop)
      else
        toEnv input bindings key

/-- Read every captured string stored under a key. -/
def toEnvList (input : List Char) : SpanMap → String → List String
  | [], _ => []
  | binding :: bindings, key =>
      if binding.key == key then
        ScanPlan.capturedText input binding.start binding.stop :: toEnvList input bindings key
      else
        toEnvList input bindings key

@[simp] theorem materialize_length (input : List Char) (bindings : SpanMap) :
    (materialize input bindings).length = bindings.length := by
  induction bindings <;> simp [materialize, *]

@[simp] theorem materialize_append (input : List Char) (left right : SpanMap) :
    materialize input (left ++ right) =
      materialize input left ++ materialize input right := by
  induction left <;> simp [materialize, *]

@[simp] theorem materialize_take (input : List Char) (bindings : SpanMap) (n : Nat) :
    materialize input (bindings.take n) = (materialize input bindings).take n := by
  induction bindings generalizing n with
  | nil => simp [materialize]
  | cons binding bindings ih =>
      cases n <;> simp [materialize, ih]

@[simp] theorem materialize_drop (input : List Char) (bindings : SpanMap) (n : Nat) :
    materialize input (bindings.drop n) = (materialize input bindings).drop n := by
  induction bindings generalizing n with
  | nil => simp [materialize]
  | cons binding bindings ih =>
      cases n <;> simp [materialize, ih]

@[simp] theorem materialize_keySpans (input : List Char) (keys : List String)
    (start stop : Nat) :
    materialize input
        (keys.map fun key => { key, start, stop : SpanBinding }) =
      keys.map fun key => (key, ScanPlan.capturedText input start stop) := by
  induction keys <;> simp [materialize, *]

theorem captureMap_toEnv (input : List Char) (bindings : SpanMap) (key : String) :
    CaptureMap.toEnv (materialize input bindings) key = toEnv input bindings key := by
  induction bindings with
  | nil => rfl
  | cons binding bindings ih =>
      simp only [materialize, CaptureMap.toEnv, List.find?_cons]
      by_cases hkey : binding.key == key
      · simp [toEnv, hkey]
      · simp [toEnv, hkey, ← ih, CaptureMap.toEnv]

theorem captureMap_toEnvList (input : List Char) (bindings : SpanMap) (key : String) :
    CaptureMap.toEnvList (materialize input bindings) key = toEnvList input bindings key := by
  induction bindings with
  | nil => rfl
  | cons binding bindings ih =>
      by_cases hkey : binding.key == key
      · simp only [materialize, toEnvList, hkey, ite_true]
        simp only [CaptureMap.toEnvList, List.filter_cons, hkey]
        congr
        simpa [CaptureMap.toEnvList] using ih
      · simp only [materialize, toEnvList, hkey]
        simp only [CaptureMap.toEnvList, List.filter_cons, hkey]
        simpa [CaptureMap.toEnvList] using ih

end SpanMap

/-- Runtime state with cached input suffix and deferred capture bindings. The `captureMap` field
    inside `core` is intentionally unused; `toCore` reconstructs it from `spans` for proofs. -/
structure State where
  core : CursorProgram.ExecutionState := {}
  spans : SpanMap := []
  remaining : List Char := []

/-- Materialize one runtime state as the proof-facing cursor state. -/
def State.toCore (input : List Char) (state : State) : CursorProgram.ExecutionState :=
  { state.core with captureMap := state.spans.materialize input }

@[simp] theorem State.toCore_position (input : List Char) (state : State) :
    (state.toCore input).position = state.core.position := rfl

@[simp] theorem State.toCore_starts (input : List Char) (state : State) :
    (state.toCore input).starts = state.core.starts := rfl

@[simp] theorem State.toCore_captures (input : List Char) (state : State) :
    (state.toCore input).captures = state.core.captures := rfl

@[simp] theorem State.toCore_captureMap (input : List Char) (state : State) :
    (state.toCore input).captureMap = state.spans.materialize input := rfl

/-- The cached suffix agrees with the numeric cursor. -/
def State.Consistent (input : List Char) (state : State) : Prop :=
  state.remaining = input.drop state.core.position

def initial (input : List Char) : State :=
  { remaining := input }

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
              captureMark := state.spans.length } :: state.core.starts } }

@[inline] def endCapture (name : String) (state : State) : Option State := do
  let (frame, starts) ← ScanPlan.takeStart? name state.core.starts
  let ownSpans :=
    frame.keys.map fun key =>
      { key, start := frame.start, stop := state.core.position : SpanBinding }
  let spans :=
    state.spans.take frame.captureMark ++ ownSpans ++
      state.spans.drop frame.captureMark
  some
    { state with
      core :=
        { state.core with
          starts
          captures :=
            state.core.captures ++
              [{ name, start := frame.start, stop := state.core.position }] }
      spans }

@[inline] def expect (character : Char) (state : State) : Option State :=
  LeanCursor.expect character { core := state.core, remaining := state.remaining } |>.map fun next =>
    { state with core := next.core, remaining := next.remaining }

@[inline] def consumeOptional (character : Char) (state : State) : Option State :=
  LeanCursor.consumeOptional character
      { core := state.core, remaining := state.remaining } |>.map fun next =>
    { state with core := next.core, remaining := next.remaining }

@[inline] def consumeRun (token : TokClass) (run : CursorRun) (state : State) :
    Option State :=
  LeanCursor.consumeRun token run
      { core := state.core, remaining := state.remaining } |>.map fun next =>
    { state with core := next.core, remaining := next.remaining }

@[inline] def executeOperation (operation : CursorOp) (state : State) : Option State :=
  match operation with
  | .beginCapture name keys => beginCapture name keys state
  | .endCapture name => endCapture name state
  | .expect character => expect character state
  | .consumeOptional character => consumeOptional character state
  | .consumeRun token run => consumeRun token run state

def executeOperations : List CursorOp → State → Option State
  | [], state => some state
  | operation :: rest, state => do
      let next ← executeOperation operation state
      executeOperations rest next

/-- Successful cursor execution before any captured strings are allocated. -/
structure Result where
  stop : Nat
  captures : List ScanCapture
  spans : SpanMap
  deriving Repr, Inhabited, DecidableEq

/-- Materialize a deferred result when compatibility with the proof-facing scanner is required. -/
def Result.toScanResult (input : List Char) (result : Result) : ScanResult :=
  { stop := result.stop
    captures := result.captures
    captureMap := result.spans.materialize input }

/-- Complete a successful cursor state without materializing its captured strings. -/
def finishSpans (input : List Char) (state : State) : Option Result :=
  if state.core.position == input.length && state.core.starts.isEmpty then
    some
      { stop := state.core.position
        captures := state.core.captures
        spans := state.spans }
  else
    none

/-- Execute a cursor program while retaining deferred captures. -/
def runSpans (program : CursorProgram) (source : String) : Option Result := do
  let input := source.toList
  let state ← executeOperations program.operations (initial input)
  finishSpans input state

/-- Compatibility execution that materializes the proof-facing result after acceptance. -/
def run (program : CursorProgram) (source : String) : Option ScanResult :=
  (runSpans program source).map (·.toScanResult source.toList)

def decode (program : CursorProgram) (source : String) : Option CaptureMap :=
  (run program source).map (·.captureMap)

@[simp] theorem initial_consistent (input : List Char) :
    (initial input).Consistent input := by
  simp [initial, State.Consistent]

@[simp] theorem initial_toCore (input : List Char) :
    (initial input).toCore input = {} := rfl

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

theorem executeOperation_toCore (input : List Char) (operation : CursorOp) (state : State)
    (hconsistent : state.Consistent input) :
    (executeOperation operation state).map (State.toCore input) =
      CursorProgram.executeOperation input operation (state.toCore input) := by
  cases operation with
  | beginCapture name keys =>
      simp [executeOperation, beginCapture, CursorProgram.executeOperation, State.toCore]
  | endCapture name =>
      unfold executeOperation endCapture CursorProgram.executeOperation
      simp only [State.toCore_starts, State.toCore_position, State.toCore_captures,
        State.toCore_captureMap]
      cases hstart : ScanPlan.takeStart? name state.core.starts with
      | none => simp []
      | some result =>
          obtain ⟨frame, starts⟩ := result
          congr 1
          simp [State.toCore]
  | expect character =>
      unfold executeOperation expect LeanCursor.expect CursorProgram.executeOperation
      unfold State.Consistent at hconsistent
      rw [hconsistent]
      cases hdrop : input.drop state.core.position with
      | nil => simp [hdrop]
      | cons actual tail =>
          by_cases heq : actual == character
          · have htail := drop_succ_of_drop_eq_cons hdrop
            simp [hdrop, heq, State.toCore]
          · simp [hdrop, heq]
  | consumeOptional character =>
      unfold executeOperation consumeOptional LeanCursor.consumeOptional
        CursorProgram.executeOperation
      unfold State.Consistent at hconsistent
      rw [hconsistent]
      cases hdrop : input.drop state.core.position with
      | nil => simp [hdrop, State.toCore]
      | cons actual tail =>
          by_cases heq : actual == character
          · have htail := drop_succ_of_drop_eq_cons hdrop
            simp [hdrop, heq, State.toCore]
          · simp [hdrop, heq, State.toCore]
  | consumeRun token run =>
      unfold executeOperation consumeRun LeanCursor.consumeRun CursorProgram.executeOperation
      unfold State.Consistent at hconsistent
      rw [hconsistent]
      cases run with
      | fixed width =>
          by_cases hprefix :
              termPrefixOk token (CursorRun.fixed width).toLenSpec
                (input.drop state.core.position) width = true
          · simp [CursorRun.width, hprefix, State.toCore, List.drop_drop]
          · simp [CursorRun.width, hprefix]
      | greedyBetween lower upper =>
          simp only [LeanCursor.scanToken_eq]
          by_cases hprefix :
              termPrefixOk token (CursorRun.greedyBetween lower upper).toLenSpec
                (input.drop state.core.position)
                ((input.drop state.core.position).takeWhile
                  fun character => decide (token.mem character)).length = true
          · simp [CursorRun.width, hprefix, State.toCore, List.drop_drop]
          · simp [CursorRun.width, hprefix]
      | greedyAtLeastOne =>
          simp only [LeanCursor.scanToken_eq]
          by_cases hprefix :
              termPrefixOk token CursorRun.greedyAtLeastOne.toLenSpec
                (input.drop state.core.position)
                ((input.drop state.core.position).takeWhile
                  fun character => decide (token.mem character)).length = true
          · simp [CursorRun.width, hprefix, State.toCore, List.drop_drop]
          · simp [CursorRun.width, hprefix]

theorem executeOperation_consistent (input : List Char) (operation : CursorOp)
    (state next : State) (hconsistent : state.Consistent input)
    (hexecute : executeOperation operation state = some next) :
    next.Consistent input := by
  cases operation with
  | beginCapture name keys =>
      simp only [executeOperation] at hexecute
      simp [beginCapture] at hexecute
      subst next
      exact hconsistent
  | endCapture name =>
      simp only [executeOperation] at hexecute
      unfold endCapture at hexecute
      cases hstart : ScanPlan.takeStart? name state.core.starts with
      | none => simp [hstart] at hexecute
      | some result =>
          obtain ⟨frame, starts⟩ := result
          simp [hstart] at hexecute
          subst next
          exact hconsistent
  | expect character =>
      simp only [executeOperation] at hexecute
      unfold expect LeanCursor.expect at hexecute
      unfold State.Consistent at hconsistent ⊢
      cases hremaining : state.remaining with
      | nil => simp [hremaining] at hexecute
      | cons actual tail =>
        by_cases heq : actual == character
        · simp [hremaining, heq] at hexecute
          subst next
          dsimp
          have hdrop : input.drop state.core.position = actual :: tail := by
            simpa [hremaining] using hconsistent.symm
          exact (drop_succ_of_drop_eq_cons hdrop).symm
        · simp [hremaining, heq] at hexecute
  | consumeOptional character =>
      simp only [executeOperation] at hexecute
      unfold consumeOptional LeanCursor.consumeOptional at hexecute
      unfold State.Consistent at hconsistent ⊢
      cases hremaining : state.remaining with
      | nil =>
          simp [hremaining] at hexecute
          subst next
          dsimp
          simpa [hremaining] using hconsistent
      | cons actual tail =>
        by_cases heq : actual == character
        · simp [hremaining, heq] at hexecute
          subst next
          dsimp
          have hdrop : input.drop state.core.position = actual :: tail := by
            simpa [hremaining] using hconsistent.symm
          exact (drop_succ_of_drop_eq_cons hdrop).symm
        · simp [hremaining, heq] at hexecute
          subst next
          dsimp
          simpa [hremaining] using hconsistent
  | consumeRun token run =>
      simp only [executeOperation] at hexecute
      unfold consumeRun LeanCursor.consumeRun at hexecute
      unfold State.Consistent at hconsistent ⊢
      cases run with
      | fixed width =>
          by_cases hprefix :
              termPrefixOk token (CursorRun.fixed width).toLenSpec
                state.remaining width = true
          · simp [hprefix] at hexecute
            subst next
            rw [hconsistent, List.drop_drop]
          · simp [hprefix] at hexecute
      | greedyBetween lower upper =>
          cases hscan : LeanCursor.scanToken token state.remaining with
          | mk width remaining =>
              by_cases hprefix :
                  termPrefixOk token (CursorRun.greedyBetween lower upper).toLenSpec
                    state.remaining width = true
              · simp [hscan, hprefix] at hexecute
                subst next
                dsimp
                have hscanEq := LeanCursor.scanToken_eq token state.remaining
                rw [hscan] at hscanEq
                obtain ⟨hwidth, hremaining⟩ := Prod.mk.inj hscanEq
                subst width
                subst remaining
                rw [hconsistent, List.drop_drop]
              · simp [hscan, hprefix] at hexecute
      | greedyAtLeastOne =>
          cases hscan : LeanCursor.scanToken token state.remaining with
          | mk width remaining =>
              by_cases hprefix :
                  termPrefixOk token CursorRun.greedyAtLeastOne.toLenSpec
                    state.remaining width = true
              · simp [hscan, hprefix] at hexecute
                subst next
                dsimp
                have hscanEq := LeanCursor.scanToken_eq token state.remaining
                rw [hscan] at hscanEq
                obtain ⟨hwidth, hremaining⟩ := Prod.mk.inj hscanEq
                subst width
                subst remaining
                rw [hconsistent, List.drop_drop]
              · simp [hscan, hprefix] at hexecute

theorem executeOperations_toCore (input : List Char) (operations : List CursorOp)
    (state : State) (hconsistent : state.Consistent input) :
    (executeOperations operations state).map (State.toCore input) =
      CursorProgram.executeOperations input operations (state.toCore input) := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation operations ih =>
      simp only [executeOperations, CursorProgram.executeOperations]
      cases hstep : executeOperation operation state with
      | none =>
          have href := executeOperation_toCore input operation state hconsistent
          simp [hstep] at href
          rw [← href]
          rfl
      | some next =>
          have href := executeOperation_toCore input operation state hconsistent
          have hnext := executeOperation_consistent input operation state next hconsistent hstep
          simp [hstep] at href
          rw [← href]
          exact ih next hnext

@[simp] theorem run_eq_cursorProgram (program : CursorProgram) (source : String) :
    run program source = CursorProgram.run program source := by
  unfold run runSpans CursorProgram.run
  dsimp only
  cases hrun : executeOperations program.operations (initial source.toList) with
  | none =>
      have hcore :=
        executeOperations_toCore source.toList program.operations
          (initial source.toList) (initial_consistent source.toList)
      simp [hrun] at hcore
      simp [← hcore]
  | some state =>
      have hcore :=
        executeOperations_toCore source.toList program.operations
          (initial source.toList) (initial_consistent source.toList)
      simp [hrun] at hcore
      simp [← hcore, finishSpans, Result.toScanResult, State.toCore]

@[simp] theorem decode_eq_cursorProgram (program : CursorProgram) (source : String) :
    decode program source = CursorProgram.decode program source := by
  simp [decode, CursorProgram.decode]

end LeanSpanCursor

end Triptych
