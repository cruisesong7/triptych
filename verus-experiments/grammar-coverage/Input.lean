import Triptych

open Triptych

triptych GrammarCoverage where
  grammar
    GrammarCoverage ::= Payload
    Payload         ::= "λ" [Quoted] Items | digit+ | Upper | Rows | Csv
    Quoted          ::= str
    Items           ::= rep Item sepBy "," {1,4}
    Item            ::= hexDigit{1,4} | bit+
    Upper           ::= ascii[65,90]{2}
    Rows            ::= rep Row sepBy ";" {1,2}
    Row             ::= rep Cell sepBy ":" {1,3}
    Csv             ::= rep Cell sepBy "," +
    Cell            ::= bit{1}
  value
    len Payload
  verus "verus-experiments/grammar-coverage/src/spec.rs"
