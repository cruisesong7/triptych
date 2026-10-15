import Triptych

open Triptych

/-! Regression for ordered choice in the Verus search machine. Both alternatives accept `"ab"`;
    source order selects `Any`, exactly as the Lean scanner does. A literal-guided dispatch may
    skip `Pair` when `"ab"` is absent, but it must never try `Pair` first. -/

triptych SearchOrder where
  grammar
    Root ::= Any | Pair
    Any  ::= ascii[97,98]+
    Pair ::= "ab"
  value
    len Any + 10 * len Pair
  verus "verus-experiments/search-order/src/spec.rs"

#guard scan SearchOrder.grammar "ab" = some [("Any", "ab")]
#guard SearchOrder.parse "ab" = some 2
