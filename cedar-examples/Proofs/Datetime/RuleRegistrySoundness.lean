import Proofs.Datetime.RuleRegistryProof

/-!
# End-to-end Datetime soundness from a registered parser backend

The user-facing theorems compose Triptych's generated views with the registered Cedar/Std.Time
component rule. They contain no direct `Parsec` inversion or Cedar parser-correctness calls.
-/

open CedarExamples.Datetime

namespace Datetime.RuleRegistrySoundness

/-- Cedar's executable parser returns exactly Triptych-valid Datetime denotations. -/
theorem parser_agrees (s : String) (d : Cedar.Spec.Ext.Datetime) :
    Cedar.Spec.Ext.Datetime.parse s = some d ↔
      Datetime.IsValid s ∧ Datetime.computeValue s = some (datetimeMillis d) :=
  Datetime.RuleRegistryProof.parser_agrees s d

theorem parser_sound (s : String) (d : Cedar.Spec.Ext.Datetime) :
    Cedar.Spec.Ext.Datetime.parse s = some d →
      Datetime.IsValid s ∧ Datetime.computeValue s = some (datetimeMillis d) :=
  (parser_agrees s d).mp

theorem parser_complete (s : String) (d : Cedar.Spec.Ext.Datetime) :
    Datetime.IsValid s →
      Datetime.computeValue s = some (datetimeMillis d) →
        Cedar.Spec.Ext.Datetime.parse s = some d := by
  intro hvalid hvalue
  exact (parser_agrees s d).mpr ⟨hvalid, hvalue⟩

theorem parser_rejects_iff (s : String) :
    Cedar.Spec.Ext.Datetime.parse s = none ↔ ¬Datetime.IsValid s := by
  rw [CedarSupport.DatetimeParserRules.parse_eq_none_iff_not_wf,
    ← Datetime.GrammarView.isValid_iff_cedarWf]

theorem parser_eq_some_iff_view (s : String) (d : Cedar.Spec.Ext.Datetime) :
    Cedar.Spec.Ext.Datetime.parse s = some d ↔
      ∃ view : Datetime.View,
        Datetime.decodeView s = some view ∧
        Datetime.View.Valid view ∧
        Datetime.View.denotation view = datetimeMillis d := by
  rw [parser_agrees]
  constructor
  · rintro ⟨hvalid, hvalue⟩
    obtain ⟨view, hview, hvalidView⟩ := (Datetime.IsValid_view s).mp hvalid
    refine ⟨view, hview, hvalidView, ?_⟩
    rw [Datetime.computeValue_view, hview] at hvalue
    exact Option.some.inj hvalue
  · rintro ⟨view, hview, hvalidView, hvalue⟩
    refine ⟨(Datetime.IsValid_view s).mpr ⟨view, hview, hvalidView⟩, ?_⟩
    rw [Datetime.computeValue_view, hview]
    exact congrArg some hvalue

theorem parser_eq_none_iff_view (s : String) :
    Cedar.Spec.Ext.Datetime.parse s = none ↔
      ¬∃ view : Datetime.View,
        Datetime.decodeView s = some view ∧ Datetime.View.Valid view := by
  rw [parser_rejects_iff]
  exact not_congr (Datetime.IsValid_view s)

end Datetime.RuleRegistrySoundness
