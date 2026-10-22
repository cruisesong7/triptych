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

import Triptych.Elab.Syntax

/-!
# Two dependent-width rows

The decimal header fixes two later field widths. `First` is internal and ends at `/`; `Second`
is final. This exercises several dependent fields and an internal delimiter-bounded field through
the same public `triptych` declaration used by ordinary formats.
-/

namespace BitRowsExample

open Triptych

structure BitRows where
  width : Nat
  first : String
  second : String
  deriving Repr, DecidableEq, Inhabited

def rowWidth (width : String) : Nat :=
  readNat width

def toBitRows (width first second : String) : BitRows :=
  { width := readNat width, first, second }

triptych BitRows where
  grammar
    Rows   ::= Width ":" First "/" Second
    Width  ::= digit{1,2}
    First  ::= bit{rowWidth Width}
    Second ::= hexDigit{rowWidth Width}
  value'
    toBitRows Width First Second
  to "Outputs/BitRows"

end BitRowsExample
