import Triptych

open Triptych

set_option linter.unusedVariables false

triptych DirectCoverage where
  grammar
    DirectCoverage ::= Prefix Digits "-" Payload ":" Bits "/" Upper
    Prefix         ::= ["+"]
    Payload        ::= Hex
    Digits         ::= digit+
    Hex            ::= hexDigit{1,4}
    Bits           ::= bit+
    Upper          ::= ascii[65,90]{2}
  value
    len Payload.Hex
  verus "verus-experiments/direct-coverage/src/spec.rs"
