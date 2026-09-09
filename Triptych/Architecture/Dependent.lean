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

import Triptych.Architecture.Scanner

/-!
# Left-to-right dependent formats

`scanDependent header body input` parses a header prefix, uses its captures to construct the
grammar for the remaining input, and then scans that tail. This is the first dependent-format
primitive: a length, tag, or mode decoded by the header can determine the exact grammar used for
the payload.

The `triptych` surface supports one delimiter-bounded final field such as
`Cells ::= bit{width Header}`. That restricted form lowers to an ordinary lexical grammar plus
an automatically generated exact-width well-formedness condition. `scanDependent` handles the
broader case where accepting a tail may require reconsidering a header candidate. Automatic
surface lowering for those delimiter-free or internal dependent boundaries remains future work.
-/

namespace Triptych

/-- Scan a header prefix and continue with a grammar computed from its captures. Header
    alternatives retain their source order. A header candidate is accepted only when its
    generated tail grammar consumes the entire remaining input. -/
def scanDependent (header : Grammar) (body : CaptureMap → Grammar)
    (input : String) : Option CaptureMap :=
  match header.startProd? with
  | none => none
  | some headerProduction =>
      scanProdK header "" header.prods.length headerProduction input.toList
        fun headerCaptures remaining =>
          (scan (body headerCaptures) (String.ofList remaining)).map
            fun bodyCaptures => headerCaptures ++ bodyCaptures

/-- Compute a semantic value from one dependent scan. -/
def dependentComputeValueMap {α : Type} (header : Grammar) (body : CaptureMap → Grammar)
    (valueFn : CaptureMap → α) (input : String) : Option α :=
  (scanDependent header body input).map valueFn

end Triptych
