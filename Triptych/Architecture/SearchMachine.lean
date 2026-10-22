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

import Triptych.Architecture.ScanPlan
import Triptych.Architecture.SearchProgram

/-!
# First-order ordered-search machines

`SearchCode` exposes the continuation structure needed by a code generator, but captures still
use a semantic callback: run the body, prepend the enclosing capture, and then run the tail.

`SearchMachineCode` makes that control flow first order. `save` pushes the current input boundary
and capture count; `capture` closes that frame and inserts the enclosing capture before the
body's captures. `repetition` records its item and tail as explicit machine states. Backends can
turn these constructors into ordinary named states without reconstructing source grammar tables.
-/

namespace Triptych

/-- Callback-free control flow for ordered search. -/
inductive SearchMachineCode where
  | accept
  | fail
  | literal (text : String) (next : SearchMachineCode)
  | stringLiteral (next : SearchMachineCode)
  | tokenRun (token : TokClass) (length : LenSpec) (next : SearchMachineCode)
  | greedyTokenRun (token : TokClass) (length : LenSpec) (next : SearchMachineCode)
  | save (next : SearchMachineCode)
  | capture (keys : List String) (next : SearchMachineCode)
  | choice (first second : SearchMachineCode)
  | repetition (separator : String) (item : SearchMachineCode)
      (lower : Nat) (upper : Option Nat) (countKey : String) (next : SearchMachineCode)
  deriving Repr, Inhabited, DecidableEq, BEq

namespace SearchMachineCode

/-- A character that every successful execution of this state must consume next. Administrative
    capture states do not obscure the boundary. Choices expose a boundary only when both arms
    require the same character. -/
def requiredHead? : SearchMachineCode → Option Char
  | .literal text next =>
      match text.toList with
      | character :: _ => some character
      | [] => next.requiredHead?
  | .save next
  | .capture _ next => next.requiredHead?
  | .choice first second =>
      match first.requiredHead?, second.requiredHead? with
      | some firstCharacter, some secondCharacter =>
          if firstCharacter == secondCharacter then some firstCharacter else none
      | _, _ => none
  | _ => none

/-- Replace ordered width search by one greedy token scan when the continuation has a certified
    incompatible delimiter. The remaining constructors are optimized recursively. -/
def fuse : SearchMachineCode → SearchMachineCode
  | .accept => .accept
  | .fail => .fail
  | .literal text next => .literal text next.fuse
  | .stringLiteral next => .stringLiteral next.fuse
  | .tokenRun token length next =>
      let fusedNext := next.fuse
      match length, fusedNext.requiredHead? with
      | .exactly _, _ => .tokenRun token length fusedNext
      | _, some character =>
          if decide (token.mem character) then
            .tokenRun token length fusedNext
          else
            .greedyTokenRun token length fusedNext
      | _, none => .tokenRun token length fusedNext
  | .greedyTokenRun token length next => .greedyTokenRun token length next.fuse
  | .save next => .save next.fuse
  | .capture keys next => .capture keys next.fuse
  | .choice first second => .choice first.fuse second.fuse
  | .repetition separator item lower upper countKey next =>
      .repetition separator item.fuse lower upper countKey next.fuse
termination_by code => sizeOf code

/-- Share deterministic machine prefixes across ordered alternatives. Width-searching token
    states and repetitions are deliberately left as choice boundaries. -/
def merge : SearchMachineCode → SearchMachineCode → SearchMachineCode
  | .fail, second => second
  | first, .fail => first
  | first@(.literal firstText firstNext), second@(.literal secondText secondNext) =>
      if firstText = secondText then
        .literal firstText (merge firstNext secondNext)
      else
        .choice first second
  | first@(.greedyTokenRun firstToken firstLength firstNext),
      second@(.greedyTokenRun secondToken secondLength secondNext) =>
      if firstToken = secondToken ∧ firstLength = secondLength then
        .greedyTokenRun firstToken firstLength (merge firstNext secondNext)
      else
        .choice first second
  | .save firstNext, .save secondNext =>
      .save (merge firstNext secondNext)
  | first@(.capture firstKeys firstNext), second@(.capture secondKeys secondNext) =>
      if firstKeys = secondKeys then
        .capture firstKeys (merge firstNext secondNext)
      else
        .choice first second
  | first, second => .choice first second
termination_by first second => sizeOf first + sizeOf second

/-- Recursively factor deterministic common prefixes without changing ordered-search behavior. -/
def reduce : SearchMachineCode → SearchMachineCode
  | .accept => .accept
  | .fail => .fail
  | .literal text next => .literal text next.reduce
  | .stringLiteral next => .stringLiteral next.reduce
  | .tokenRun token length next => .tokenRun token length next.reduce
  | .greedyTokenRun token length next => .greedyTokenRun token length next.reduce
  | .save next => .save next.reduce
  | .capture keys next => .capture keys next.reduce
  | .choice first second => merge first.reduce second.reduce
  | .repetition separator item lower upper countKey next =>
      .repetition separator item.reduce lower upper countKey next.reduce
termination_by code => sizeOf code

end SearchMachineCode

namespace SearchMachine

/-- A saved capture boundary and the length of the capture prefix preceding its body. -/
structure Marker where
  start : List Char
  captureCount : Nat
  deriving Repr, Inhabited, DecidableEq

/-- Runtime state for one callback-free search machine. -/
structure State where
  input : List Char
  captures : CaptureMap
  markers : List Marker
  deriving Repr, Inhabited, DecidableEq

/-- Close the innermost capture frame, preserving the scanner's outer-before-inner ordering. -/
def closeCapture (keys : List String) (state : State) : Option State :=
  match state.markers with
  | [] => none
  | marker :: markers =>
      let consumed :=
        String.ofList
          (marker.start.take (marker.start.length - state.input.length))
      let outer := state.captures.take marker.captureCount
      let inner := state.captures.drop marker.captureCount
      some
        { state with
          captures := outer ++ keys.map (·, consumed) ++ inner
          markers := markers }

/-- Insert one capture at a saved boundary without disturbing captures produced after it. -/
def insertCaptureAt (captureCount : Nat) (capture : String × String) (state : State) : State :=
  { state with
    captures :=
      state.captures.take captureCount ++
        [capture] ++
        state.captures.drop captureCount }

/-- Lazily scan the tail of a separated repetition while carrying first-order machine state. -/
def scanStarStateK {α : Type} (scanItem : State → (State → Option α) → Option α)
    (separator : List Char) (lower : Nat) (upper : Option Nat) :
    Nat → State → Nat → (State → Nat → Option α) → Option α
  | 0, state, itemCount, finish =>
      if repetitionCountOk lower upper itemCount then finish state itemCount else none
  | fuel + 1, state, itemCount, finish =>
      let stop :=
        if repetitionCountOk lower upper itemCount then finish state itemCount else none
      scanOrElse stop fun _ =>
        if separator.isPrefixOf state.input then
          scanItem { state with input := state.input.drop separator.length } fun nextState =>
            scanStarStateK scanItem separator lower upper fuel nextState
              (itemCount + 1) finish
        else
          none

mutual

/-- Execute callback-free ordered-search control flow. -/
def runK {α : Type} :
    SearchMachineCode → State → (State → Option α) → Option α
  | .accept, state, finish => finish state
  | .fail, _, _ => none
  | .literal text next, state, finish =>
      let characters := text.toList
      if characters.isPrefixOf state.input then
        runK next { state with input := state.input.drop characters.length } finish
      else
        none
  | .stringLiteral next, state, finish =>
      (List.range (state.input.length + 1)).findSome? fun width =>
        if stringPrefixOk state.input width then
          runK next { state with input := state.input.drop width } finish
        else
          none
  | .tokenRun token length next, state, finish =>
      (List.range (state.input.length + 1)).findSome? fun width =>
        if termPrefixOk token length state.input width then
          runK next { state with input := state.input.drop width } finish
        else
          none
  | .greedyTokenRun token length next, state, finish =>
      let width := ScanPlan.tokenWidth token length state.input
      if termPrefixOk token length state.input width then
        runK next { state with input := state.input.drop width } finish
      else
        none
  | .save next, state, finish =>
      runK next
        { state with
          markers := { start := state.input, captureCount := state.captures.length } ::
            state.markers }
        finish
  | .capture keys next, state, finish =>
      (closeCapture keys state).bind fun closed => runK next closed finish
  | .choice first second, state, finish =>
      scanOrElse (runK first state finish) fun _ => runK second state finish
  | .repetition separator item lower upper countKey next, state, finish =>
      let captureCount := state.captures.length
      runK item state fun firstState =>
        scanStarStateK (runK item) separator.toList lower upper state.input.length
          firstState 1 fun repeatedState itemCount =>
            let counted :=
              insertCaptureAt captureCount
                (countKey ++ "#count", toString itemCount) repeatedState
            runK next counted finish
termination_by code => sizeOf code

end

/-- Execute a machine and return its final state. -/
def run (code : SearchMachineCode) (state : State) : Option State :=
  runK code state some

end SearchMachine

/-- Structural evidence that a continuation-based search was lowered to first-order states. -/
inductive SearchMachineCode.Lowers :
    SearchCode → SearchMachineCode → SearchMachineCode → Prop
  | accept :
      Lowers .accept continuation continuation
  | fail :
      Lowers .fail continuation .fail
  | literal
      (next : Lowers sourceNext continuation machineNext) :
      Lowers (.literal text sourceNext) continuation (.literal text machineNext)
  | stringLiteral
      (next : Lowers sourceNext continuation machineNext) :
      Lowers (.stringLiteral sourceNext) continuation (.stringLiteral machineNext)
  | tokenRun
      (next : Lowers sourceNext continuation machineNext) :
      Lowers (.tokenRun token length sourceNext) continuation
        (.tokenRun token length machineNext)
  | capture
      (next : Lowers sourceNext continuation machineNext)
      (body : Lowers sourceBody (.capture keys machineNext) machineBody) :
      Lowers (.capture keys sourceBody sourceNext) continuation (.save machineBody)
  | choice
      (first : Lowers sourceFirst continuation machineFirst)
      (second : Lowers sourceSecond continuation machineSecond) :
      Lowers (.choice sourceFirst sourceSecond) continuation
        (.choice machineFirst machineSecond)
  | repetition
      (item : Lowers sourceItem .accept machineItem)
      (next : Lowers sourceNext continuation machineNext) :
      Lowers (.repetition separator sourceItem lower upper countKey sourceNext) continuation
        (.repetition separator machineItem lower upper countKey machineNext)

/-- Lower continuation-based search to callback-free machine control flow. -/
def lowerSearchCode :
    SearchCode → SearchMachineCode → SearchMachineCode
  | .accept, continuation => continuation
  | .fail, _ => .fail
  | .literal text next, continuation =>
      .literal text (lowerSearchCode next continuation)
  | .stringLiteral next, continuation =>
      .stringLiteral (lowerSearchCode next continuation)
  | .tokenRun token length next, continuation =>
      .tokenRun token length (lowerSearchCode next continuation)
  | .capture keys body next, continuation =>
      let machineNext := lowerSearchCode next continuation
      .save (lowerSearchCode body (.capture keys machineNext))
  | .choice first second, continuation =>
      .choice
        (lowerSearchCode first continuation)
        (lowerSearchCode second continuation)
  | .repetition separator item lower upper countKey next, continuation =>
      .repetition separator
        (lowerSearchCode item .accept)
        lower upper countKey
        (lowerSearchCode next continuation)
termination_by code _continuation => sizeOf code

/-- A callback-free machine for one complete search program. -/
structure SearchMachine where
  start : String
  code : SearchMachineCode
  deriving Repr, Inhabited

namespace SearchMachine

/-- Execute one complete callback-free machine. -/
def decode (machine : SearchMachine) (source : String) : Option CaptureMap := do
  runK machine.code
    { input := source.toList, captures := [], markers := [] }
    fun result =>
      if result.input.isEmpty then
        some result.captures
      else
        none

end SearchMachine

/-- Lower a complete search program to callback-free machine control flow. -/
def lowerSearchProgram (program : SearchProgram) : SearchMachine :=
  { start := program.start, code := (lowerSearchCode program.code .accept).fuse.reduce }

end Triptych
