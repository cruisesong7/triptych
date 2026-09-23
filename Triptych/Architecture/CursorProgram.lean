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

/-!
# Verified cursor-program lowering

`ScanPlan` still describes token runs using the grammar-facing `LenSpec`. This module lowers that
IR to the smaller execution vocabulary consumed by direct parser backends:

* fixed-width runs consume exactly their declared width;
* variable-width runs greedily scan a token class and then check explicit bounds.

The lowering theorem proves equality of the complete result, including capture spans, for every
plan and source string. Backend emitters can therefore compile `CursorProgram` rather than
reimplementing the `LenSpec` dispatch independently.
-/

namespace Triptych

/-- Runtime policy for one token-class run after grammar-facing lengths have been lowered. -/
inductive CursorRun where
  | fixed (width : Nat)
  | greedyBetween (lower upper : Nat)
  | greedyAtLeastOne
  deriving Repr, Inhabited, DecidableEq

namespace CursorRun

/-- Recover the grammar-facing length represented by a lowered run policy. -/
def toLenSpec : CursorRun → LenSpec
  | .fixed width => .exactly width
  | .greedyBetween lower upper => .between lower upper
  | .greedyAtLeastOne => .atLeastOne

/-- Select the single width inspected by a direct cursor program. -/
def width (run : CursorRun) (token : TokClass) (input : List Char) : Nat :=
  match run with
  | .fixed width => width
  | .greedyBetween _ _ | .greedyAtLeastOne =>
      (input.takeWhile fun character => decide (token.mem character)).length

end CursorRun

/-- One lower-level cursor instruction. -/
inductive CursorOp where
  | beginCapture (name : String) (keys : List String)
  | endCapture (name : String)
  | expect (character : Char)
  | consumeOptional (character : Char)
  | consumeRun (token : TokClass) (run : CursorRun)
  deriving Repr, Inhabited, DecidableEq

/-- A lower-level cursor program ready for backend-specific code generation. -/
structure CursorProgram where
  start : String
  operations : List CursorOp
  captures : List String
  captureKeys : List (String × List String) := []
  deriving Repr, Inhabited, DecidableEq

/-- Lower one abstract scan-plan operation. -/
def lowerScanOp : ScanOp → CursorOp
  | .beginCapture name keys => .beginCapture name keys
  | .endCapture name => .endCapture name
  | .literal character => .expect character
  | .optionalLiteral character => .consumeOptional character
  | .tokenRun token (.exactly width) => .consumeRun token (.fixed width)
  | .tokenRun token (.between lower upper) =>
      .consumeRun token (.greedyBetween lower upper)
  | .tokenRun token .atLeastOne => .consumeRun token .greedyAtLeastOne

/-- Lower a scan plan to the cursor-program IR consumed by direct parser backends. -/
def lowerScanPlan (plan : ScanPlan) : CursorProgram :=
  { start := plan.start
    operations := plan.operations.map lowerScanOp
    captures := plan.captures
    captureKeys := plan.captureKeys }

namespace CursorProgram

abbrev ExecutionState := ScanPlan.ExecutionState

/-- Execute one lowered cursor instruction in Lean. -/
@[inline] def executeOperation (input : List Char) (operation : CursorOp)
    (state : ExecutionState) : Option ExecutionState :=
  match operation with
  | .beginCapture name keys =>
      some
        { state with
          starts :=
            { name, keys, start := state.position, captureMark := state.captureMap.length } ::
              state.starts }
  | .endCapture name => do
      let (frame, starts) ← ScanPlan.takeStart? name state.starts
      let text := ScanPlan.capturedText input frame.start state.position
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
  | .expect character =>
      match (input.drop state.position).head? with
      | some actual =>
          if actual == character then
            some { state with position := state.position + 1 }
          else
            none
      | none => none
  | .consumeOptional character =>
      let next :=
        match (input.drop state.position).head? with
        | some actual => if actual == character then state.position + 1 else state.position
        | none => state.position
      some { state with position := next }
  | .consumeRun token run =>
      let suffix := input.drop state.position
      let width := run.width token suffix
      if termPrefixOk token run.toLenSpec suffix width then
        some { state with position := state.position + width }
      else
        none

/-- Execute lowered cursor instructions in Lean. -/
def executeOperations (input : List Char) :
    List CursorOp → ExecutionState → Option ExecutionState
  | [], state => some state
  | operation :: rest, state => do
      let next ← executeOperation input operation state
      executeOperations input rest next

/-- Execute a lowered cursor program. -/
def run (program : CursorProgram) (source : String) : Option ScanResult := do
  let input := source.toList
  let state ← executeOperations input program.operations {}
  if state.position == input.length && state.starts.isEmpty then
    some
      { stop := state.position
        captures := state.captures
        captureMap := state.captureMap }
  else
    none

/-- Execute a lowered program and recover captured strings. -/
def decode (program : CursorProgram) (source : String) : Option CaptureMap :=
  (program.run source).map (·.captureMap)

/-- Execute the lowered cursor program as a fast path, falling back to the complete scanner only
    when the direct program rejects. -/
def decodeCertified (program : CursorProgram) (grammar : Grammar) (source : String) :
    Option CaptureMap :=
  (program.decode source).orElse fun _ => scanSearch grammar source

end CursorProgram

namespace CursorProgram

@[simp] theorem lowerScanOp_toLenSpec (operation : ScanOp) :
    (match lowerScanOp operation with
     | .consumeRun _ run => some run.toLenSpec
     | _ => none) =
      (match operation with
       | .tokenRun _ length => some length
       | _ => none) := by
  cases operation <;> simp [lowerScanOp]
  next length =>
    cases length <;> rfl

private theorem executeOperation_lower (input : List Char) (operation : ScanOp)
    (state : ScanPlan.ExecutionState) :
    CursorProgram.executeOperation input (lowerScanOp operation) state =
      ScanPlan.executeOperation input operation state := by
  cases operation with
  | beginCapture name keys | endCapture name | literal name | optionalLiteral name =>
      rfl
  | tokenRun token length =>
      cases length <;> rfl

private theorem executeOperations_lower (input : List Char) (operations : List ScanOp)
    (state : ScanPlan.ExecutionState) :
    CursorProgram.executeOperations input (operations.map lowerScanOp) state =
      ScanPlan.executeOperations input operations state := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation operations ih =>
      simp only [List.map_cons, CursorProgram.executeOperations, ScanPlan.executeOperations]
      rw [executeOperation_lower]
      cases hstep : ScanPlan.executeOperation input operation state with
      | none => simp
      | some next => simp [ih]

/-- Lowering preserves complete execution, including positions and capture spans. -/
@[simp] theorem lowerScanPlan_run (plan : ScanPlan) (source : String) :
    (lowerScanPlan plan).run source = plan.run source := by
  simp only [CursorProgram.run, ScanPlan.run, lowerScanPlan]
  rw [executeOperations_lower]

/-- Lowering preserves the captured-string result used by value computation. -/
@[simp] theorem lowerScanPlan_decode (plan : ScanPlan) (source : String) :
    (lowerScanPlan plan).decode source = plan.decode source := by
  unfold CursorProgram.decode ScanPlan.decode
  rw [lowerScanPlan_run]
  congr 1

/-- Lowering also preserves the complete fast-path-plus-fallback parser. -/
@[simp] theorem lowerScanPlan_decodeCertified (plan : ScanPlan) (grammar : Grammar)
    (source : String) :
    (lowerScanPlan plan).decodeCertified grammar source =
      plan.decodeCertified grammar source := by
  simp [CursorProgram.decodeCertified, ScanPlan.decodeCertified]

/-- The complete direct-backend pipeline agrees with the structured proof-facing pattern. -/
@[simp] theorem lowerScanPlan_decodePattern (plan : ScanPlan) (source : String) :
    (lowerScanPlan plan).decode source = plan.decodePattern source := by
  rw [lowerScanPlan_decode, ScanPlan.decode_eq_decodePattern]

end CursorProgram

end Triptych
