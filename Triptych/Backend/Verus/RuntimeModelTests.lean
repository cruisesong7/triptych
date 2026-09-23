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

import Triptych.Backend.Verus.RuntimeModel

namespace Triptych.Backend.Verus.RuntimeModelTests

private def item (symbol : Sym) (optional := false) : SymItem :=
  { sym := symbol, optional }

private def completeGrammar : Grammar :=
  { start := "Root"
    prods :=
      [ { name := "Root"
          alts :=
            [[item (.lit "λ"), item (.str) true, item (.ref "Digits"),
              item (.rep ":" (.ref "Hex") 1 (some 8)),
              item (.term .bit (.between 1 16)),
              item (.term (.asciiRange 32 126) (.exactly 1))]] },
        { name := "Digits", alts := [[item (.term .digit .atLeastOne)]] },
        { name := "Hex", alts := [[item (.term .hexDigit (.between 1 4))]] } ] }

#guard runtimeGrammarSupported completeGrammar
#guard (compileRuntimeGrammar completeGrammar).isOk

#guard
  match compileRuntimeGrammar completeGrammar with
  | .error _ => false
  | .ok runtime =>
      runtime.start == 0 &&
        runtime.productions.length == 3 &&
        (runtime.symbols.any fun symbol => symbol == .stringLiteral) &&
        (runtime.symbols.any fun symbol =>
          symbol == .repetition ":" 3 1 (some 8))

#guard
  match compileFlatGrammar completeGrammar with
  | .error _ => false
  | .ok grammar =>
      grammar.start == 0 &&
        grammar.productions ==
          [{ name := "Root", firstAlternative := 0, alternativeCount := 1 },
           { name := "Digits", firstAlternative := 1, alternativeCount := 1 },
           { name := "Hex", firstAlternative := 2, alternativeCount := 1 }] &&
        grammar.alternatives ==
          [{ firstItem := 0, itemCount := 6 },
           { firstItem := 6, itemCount := 1 },
           { firstItem := 7, itemCount := 1 }] &&
        grammar.items.length == 8

private def ambiguousGrammar : Grammar :=
  { start := "Root"
    prods :=
      [{ name := "Root"
         alts := [[item (.term .digit .atLeastOne)], [item (.term .digit (.exactly 1))]] }] }

-- Runtime support must not depend on the deterministic fast-path classifier.
#guard runtimeGrammarSupported ambiguousGrammar
#guard (compileRuntimeGrammar ambiguousGrammar).isOk

private def unresolvedGrammar : Grammar :=
  { start := "Root"
    prods := [{ name := "Root", alts := [[item (.ref "Missing")]] }] }

#guard !(runtimeGrammarSupported unresolvedGrammar)
#guard !(compileRuntimeGrammar unresolvedGrammar).isOk

private def recursiveGrammar : Grammar :=
  { start := "A"
    prods :=
      [{ name := "A", alts := [[item (.ref "B")]] },
       { name := "B", alts := [[item (.ref "A")]] }] }

#guard !(runtimeGrammarSupported recursiveGrammar)
#guard !(compileRuntimeGrammar recursiveGrammar).isOk

private def invalidRepetitionGrammar : Grammar :=
  { start := "Root"
    prods :=
      [{ name := "Root"
         alts := [[item (.rep "" (.term .digit .atLeastOne) 0 none)]] }] }

#guard !(runtimeGrammarSupported invalidRepetitionGrammar)
#guard !(compileRuntimeGrammar invalidRepetitionGrammar).isOk

end Triptych.Backend.Verus.RuntimeModelTests
