module

public import Cedar.Thm.Data.String

import all Cedar.Thm.Data.String

/-! Modern-module wrappers for Cedar's private string lemmas. -/

namespace Triptych.Theorems.Cedar.StringInternals

public theorem noUnderscoreOfIsDigits {s : String} (h : _root_.IsDigits s) :
    s.contains '_' = false :=
  _root_.no_underscore_of_isDigits h

public theorem isNatOfIsDigits {s : String} (h : _root_.IsDigits s) :
    s.isNat = true :=
  _root_.isNat_of_isDigits h

public theorem foldlEqOfDigitChars (l : List Char) (acc : Nat) :
    List.foldl (fun n c => n * 10 + (c.toNat - 48)) acc l =
      Nat.ofDigitChars 10 l acc :=
  _root_.foldl_eq_ofDigitChars l acc

end Triptych.Theorems.Cedar.StringInternals
