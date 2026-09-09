import Inputs.Graph6
import Triptych.Theorems.Dependent

/-!
# Graph6 dependent-scanner checks

Executable format examples and generic agreement/cost theorems instantiated for Graph6.
-/

namespace Graph6Example

open Triptych

#guard graph6Order? "C" = some 4
#guard graph6Order? "~??~" = some 63
#guard graph6Order? "~~???~??" = some 258048
#guard graph6PayloadLength 4 = 1
#guard parseView "?" = some [("Header", "?"), ("Payload", "")]
#guard parseView "Ch" = some [("Header", "C"), ("Payload", "h")]
#guard parseView "Chx" = none
#guard parseView "C" = none
#guard parse "Bg" =
  some { order := 3, edges := [(0, 1), (1, 2)] }
#guard parse "Bh" = none
#guard parse "Ch" =
  some { order := 4, edges := [(0, 1), (1, 2), (2, 3)] }
#guard parse "C~" =
  some { order := 4, edges := [(0, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, 3)] }

#guard dependentScanProfile graph6HeaderGrammar graph6PayloadGrammar "Ch" =
  {
    result := some [("Header", "C"), ("Payload", "h")]
    headerCandidateChecks := 1
    tailCandidateChecks := 0
  }

#guard dependentCandidateBudget graph6HeaderGrammar graph6PayloadGrammar "Ch" = 2

example (input : String) :
    scanDependent graph6HeaderGrammar graph6PayloadGrammar input =
      decodeDependent graph6HeaderGrammar graph6PayloadGrammar input :=
  scanDependent_eq_decodeDependent graph6HeaderGrammar graph6PayloadGrammar input

example (input : String) :
    (dependentScanProfile graph6HeaderGrammar
        graph6PayloadGrammar input).headerCandidateChecks +
        (dependentScanProfile graph6HeaderGrammar
          graph6PayloadGrammar input).tailCandidateChecks ≤
      dependentCandidateBudget graph6HeaderGrammar graph6PayloadGrammar input :=
  dependentCandidateChecks_le graph6HeaderGrammar graph6PayloadGrammar input

end Graph6Example
