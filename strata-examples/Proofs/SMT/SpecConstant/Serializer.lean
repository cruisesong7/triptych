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

import Outputs.SMT.SpecConstant.parser

namespace StrataExamples.SMT.SpecConstant

/-- Return the lexical serialization only when the verified parser recovers the same value. -/
def checkedSerialize (literal : Value) : Option String :=
  serialize literal |>.bind fun output =>
    if SpecConstant.parse output = some literal then some output else none

theorem checkedSerialize_sound (literal : Value) (output : String) :
    checkedSerialize literal = some output → SpecConstant.parse output = some literal := by
  simp only [checkedSerialize]
  cases hserialize : serialize literal with
  | none => simp
  | some candidate =>
    simp only [Option.bind_some]
    split <;> rename_i hparse
    · intro houtput
      have htext : candidate = output := Option.some.inj houtput
      rw [← htext]
      exact hparse
    · simp

end StrataExamples.SMT.SpecConstant
