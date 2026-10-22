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

import Triptych.Backend.Verus.Drift

namespace Triptych.Verus.Drift.Tests

#guard syntaxEquivalent
  "fn parse(input: &str) -> bool { input.len() == 1 ==> input == r#\"a b\"# }"
  "fn parse ( input : & str ) -> bool {\n\
    /* nested /* block */ comment */ input.len ( ) == 1\n\
    ==> input == r#\"a b\"# // trailing comment\n\
  }"

#guard syntaxEquivalent
  "pub struct GrammarInput<'a> { symbols: &'a [GrammarSymbol] }"
  "pub struct GrammarInput < 'a > { symbols : & 'a [ GrammarSymbol ] }"

#guard syntaxEquivalent
  "character == 'a' ||| character == '\\n'"
  "character=='a'|||character=='\\n'"

#guard !syntaxEquivalent "fn f() { alpha beta }" "fn f() { alphabeta }"

#guard !syntaxEquivalent "value == expected" "value = = expected"

#guard !syntaxEquivalent "let text = \"not // a comment\";" "let text = \"not\";"

#guard !syntaxEquivalent "let text = r#\"a b\"#;" "let text = r#\"ab\"#;"

#guard
  Drift.compare .exact "fn f() {}" "fn  f() {}" matches .ok (some _)

#guard
  Drift.compare .syntax "fn f() {}" "fn  f() {}" matches .ok none

end Triptych.Verus.Drift.Tests
