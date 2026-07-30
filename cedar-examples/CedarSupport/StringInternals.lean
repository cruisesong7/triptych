module

public import Cedar.Thm.Data.String
public import Triptych.Theorems.String

import all Cedar.Thm.Data.String

/-! Modern-module wrappers for Cedar's private string lemmas. -/

namespace CedarSupport.StringInternals

public theorem noUnderscoreOfIsDigits {s : String} (h : _root_.IsDigits s) :
    s.contains '_' = false :=
  _root_.no_underscore_of_isDigits h

public theorem isNatOfIsDigits {s : String} (h : _root_.IsDigits s) :
    s.isNat = true :=
  _root_.isNat_of_isDigits h

public theorem isDigitsOfToNatIsSome {s : String} (h : (Cedar.Spec.Ext.toNat?' s).isSome = true) :
    _root_.IsDigits s :=
  _root_.isDigits_of_toNat?'_isSome h

public theorem splitToListEq4 (s₁ s₂ s₃ s₄ : String) (p : Char → Bool) (sep : Char)
    (hsep : p sep = true) (h₁ : ∀ c ∈ s₁.toList, p c = false)
    (h₂ : ∀ c ∈ s₂.toList, p c = false) (h₃ : ∀ c ∈ s₃.toList, p c = false)
    (h₄ : ∀ c ∈ s₄.toList, p c = false) :
    (s₁ ++ String.singleton sep ++ s₂ ++ String.singleton sep ++ s₃ ++
        String.singleton sep ++ s₄).splitToList p = [s₁, s₂, s₃, s₄] :=
  Triptych.splitToList_four s₁ s₂ s₃ s₄ p sep hsep h₁ h₂ h₃ h₄

public theorem splitToListNoSep (s : String) (p : Char → Bool)
    (h : ∀ c ∈ s.toList, p c = false) :
    s.splitToList p = [s] :=
  Triptych.splitToList_noSep s p h

public theorem splitToListEq (s₁ s₂ : String) (p : Char → Bool) (sep : Char)
    (hsep : p sep = true) (h₁ : ∀ c ∈ s₁.toList, p c = false)
    (h₂ : ∀ c ∈ s₂.toList, p c = false) :
    (s₁ ++ String.singleton sep ++ s₂).splitToList p = [s₁, s₂] :=
  Triptych.splitToList_two s₁ s₂ p sep hsep h₁ h₂

public theorem foldlEqOfDigitChars (l : List Char) (acc : Nat) :
    List.foldl (fun n c => n * 10 + (c.toNat - 48)) acc l =
      Nat.ofDigitChars 10 l acc :=
  _root_.foldl_eq_ofDigitChars l acc

end CedarSupport.StringInternals
