import Triptych.Architecture.Syntax

namespace CedarExamples.LeanWeb

open Triptych

set_option linter.unusedVariables false

triptych SignedNatural where
  grammar
    SignedNatural ::= Sign Digits
    Sign          ::= sign
    Digits        ::= digit+
  value
    Sign * nat Digits
  printer auto

#eval SignedNatural.parse "-42"

-- Add this clause to the triptych block when you want files:
--   to "Outputs/MyFormat"

end CedarExamples.LeanWeb
