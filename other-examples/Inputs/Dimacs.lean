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

import Triptych

/-!
# DIMACS CNF

The DIMACS CNF format, written entirely in the analyzable DSL: no `value'` or `constraints'`
escapes. A file is optional comment lines, the problem line `p cnf V C`, and `C` clauses. A
clause is a sequence of non-zero literals terminated by `0`. Tokens are separated by any mix of
spaces, tabs, carriage returns, and newlines, so clauses may span or share lines.

Each token is preceded by whitespace, so the terminator `0` can never be read as the prefix of a
following literal, and literal magnitudes start with a non-zero digit, so `0` is never a
literal. The problem line's counts are checked by constraints: exactly `C` clauses, and every
literal's variable at most `V`.

The value is the list of clauses, each a list of signed variable indices, computed by a list
comprehension over the grammar. `Proofs/Dimacs/Roundtrip.lean` checks it against
`Std.Sat.CNF.dimacs`, the DIMACS printer used by `bv_decide`.

Not covered: comment lines after the problem line, and the SATLIB `%` trailer.
-/

namespace DimacsExample

open Triptych

-- ANCHOR: dimacsTriptychSource
triptych Dimacs where
  grammar
    File     ::= [Comments] Header [Clauses] [Ws]
    Comments ::= rep Comment +
    Comment  ::= "c" [Text] "\n"
    Text     ::= noneOf "\n"+
    Header   ::= "p" Blank "cnf" Blank Vars Blank Count
    Vars     ::= digit+
    Count    ::= digit+
    Clauses  ::= rep Clause +
    Clause   ::= [Lits] Ws "0"
    Lits     ::= rep WsLit +
    WsLit    ::= Ws Lit
    Lit      ::= Sign Var
    Sign     ::= sign
    Var      ::= NonZero [Digits]
    NonZero  ::= ascii[49,57]{1}
    Digits   ::= digit+
    Blank    ::= oneOf " \t"+
    Ws       ::= oneOf " \t\r\n"+
  value
    [Clause ↦ [Lit ↦ Sign * nat Var]]
  constraints
    count Clause == nat Count
    forall Lit, nat Var ≤ nat Vars
  to "Outputs/Dimacs"
-- ANCHOR_END: dimacsTriptychSource

#guard Dimacs.parse "p cnf 3 2\n1 -3 0\n2 3 -1 0\n" = some [[1, -3], [2, 3, -1]]
#guard Dimacs.parse "c example\nc\np cnf 2 3\n1 0 -2\n 0\t0\n" = some [[1], [-2], []]
#guard Dimacs.parse "p cnf 0 0\n" = some []
#guard Dimacs.parse "p cnf 2 1\n1 3 0\n" = none
#guard Dimacs.parse "p cnf 3 2\n1 0\n" = none
#guard Dimacs.parse "p cnf 3 1\n1 02 0\n" = none

end DimacsExample
