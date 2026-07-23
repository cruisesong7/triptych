module

public import Cedar.Spec.Ext.Util
public import Cedar.Thm.Ext.Decimal.Grammar
public import Cedar.Thm.Data.String

import all Cedar.Spec.Ext.Decimal
import all Cedar.Thm.Ext.Decimal.Grammar
import all Cedar.Thm.Data.String

/-!
# Cedar Decimal compatibility boundary

Cedar's modern modules keep several useful implementation theorems private, so a normal
`import Cedar.Thm.Data.String` cannot name them from Triptych's legacy generated modules.
This modern module uses `import all` once and republishes only the small, stable interface
needed by the Decimal bridge. The wrappers contain no new proof logic.
-/

namespace Triptych.Theorems.Decimal.CedarInternals

public theorem toNatIsSome_iff_isDigits {s : String} :
    (Cedar.Spec.Ext.toNat?' s).isSome = true ↔ _root_.IsDigits s :=
  ⟨_root_.isDigits_of_toNat?'_isSome, _root_.toNat?'_isSome_of_isDigits⟩

public theorem noUnderscore_of_isDigits {s : String} (h : _root_.IsDigits s) :
    s.contains '_' = false :=
  _root_.no_underscore_of_isDigits h

public theorem isNat_of_isDigits {s : String} (h : _root_.IsDigits s) :
    s.isNat = true :=
  _root_.isNat_of_isDigits h

public theorem splitToList_eq (s₁ s₂ : String) (p : Char → Bool) (sep : Char)
    (hsep : p sep = true) (h₁ : ∀ c ∈ s₁.toList, p c = false)
    (h₂ : ∀ c ∈ s₂.toList, p c = false) :
    (s₁ ++ String.singleton sep ++ s₂).splitToList p = [s₁, s₂] :=
  _root_.splitToList_eq s₁ s₂ p sep hsep h₁ h₂

public theorem foldl_eq_ofDigitChars (l : List Char) (acc : Nat) :
    List.foldl (fun n c => n * 10 + (c.toNat - 48)) acc l =
      Nat.ofDigitChars 10 l acc :=
  _root_.foldl_eq_ofDigitChars l acc

public theorem isWfStr_iff (s : String) :
    Cedar.Thm.Decimal.IsWfStr s ↔
      ∃ left right,
        s.splitToList (· = '.') = [left, right] ∧
        left ≠ "-" ∧
        0 < right.length ∧
        right.length ≤ 4 ∧
        (Cedar.Spec.Ext.toInt?' left).isSome ∧
        (Cedar.Spec.Ext.toNat?' right).isSome := by
  unfold Cedar.Thm.Decimal.IsWfStr
  rfl

public theorem computeValue_eq (s : String) :
    Cedar.Thm.Decimal.computeValue s =
      match s.splitToList (· = '.') with
      | [left, right] =>
        match Cedar.Spec.Ext.toInt?' left, Cedar.Spec.Ext.toNat?' right with
        | some l, some r =>
          if !left.startsWith "-"
          then l * Int.pow 10 4 + r * Int.pow 10 (4 - right.length)
          else l * Int.pow 10 4 - r * Int.pow 10 (4 - right.length)
        | _, _ => 0
      | _ => 0 := by
  unfold Cedar.Thm.Decimal.computeValue
  rfl

end Triptych.Theorems.Decimal.CedarInternals
