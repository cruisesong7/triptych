import Proofs.Datetime.ComponentView
import CedarSupport.DatetimeParserRules
import Triptych.Automation.ExternalParser

/-!
# Datetime external-parser proof through registered rules

The format proof sees Cedar's `Std.Time` parser through its registered component normal form.
All generated-grammar reasoning remains in `Datetime.GrammarView`.
-/

open Cedar.Spec.Ext
open CedarExamples.Datetime
open Triptych

namespace Datetime.RuleRegistryProof

/-- Successful Cedar parsing exposes the parser-independent Datetime components. -/
theorem parts_of_parse_eq_some {s : String} {d : Cedar.Spec.Ext.Datetime}
    (h : Cedar.Spec.Ext.Datetime.parse s = some d) :
    ∃ components : Cedar.Thm.Datetime.DatetimeComponents,
      components.syntaxWf ∧
      components.constraintsWf ∧
      s = components.asString ∧
      components.toMillis = datetimeMillis d := by
  triptych_auto [datetimeMillis]

/-- Cedar's executable parser returns exactly Triptych-valid Datetime denotations. -/
theorem parser_agrees (s : String) (d : Cedar.Spec.Ext.Datetime) :
    Cedar.Spec.Ext.Datetime.parse s = some d ↔
      Datetime.IsValid s ∧ Datetime.computeValue s = some (datetimeMillis d) := by
  constructor
  · intro hparse
    obtain ⟨components, hsyntax, hconstraints, hs, hvalue⟩ :=
      parts_of_parse_eq_some hparse
    have hcedarWf : Cedar.Thm.Datetime.IsWfDatetime s :=
      ⟨components, hsyntax, hconstraints, hs⟩
    refine ⟨(Datetime.GrammarView.isValid_iff_cedarWf s).mpr hcedarWf, ?_⟩
    rw [Datetime.GrammarView.computeValue_eq_cedar s hcedarWf, hs,
      CedarSupport.Datetime.computeValue_asString hsyntax, hvalue]
  · rintro ⟨hvalid, hcompute⟩
    have hcedarWf :=
      (Datetime.GrammarView.isValid_iff_cedarWf s).mp hvalid
    obtain ⟨components, hsyntax, hconstraints, hs⟩ := hcedarWf
    apply CedarSupport.DatetimeParserRules.parse_eq_some_iff_components.mpr
    refine ⟨components, hsyntax, hconstraints, hs, ?_⟩
    rw [Datetime.GrammarView.computeValue_eq_cedar s
      ⟨components, hsyntax, hconstraints, hs⟩] at hcompute
    rw [hs, CedarSupport.Datetime.computeValue_asString hsyntax] at hcompute
    exact Option.some.inj hcompute

/-- Cedar rejects exactly the strings rejected by the generated specification. -/
theorem parser_rejects_iff (s : String) :
    Cedar.Spec.Ext.Datetime.parse s = none ↔ ¬Datetime.IsValid s := by
  triptych_auto [Datetime.GrammarView.isValid_iff_cedarWf]

/-- The generated parser and Cedar's external parser agree on every input after exposing Cedar's
    stored epoch-millisecond value. -/
theorem generated_parse_eq_external (s : String) :
    Datetime.parse s = (Cedar.Spec.Ext.Datetime.parse s).map datetimeMillis := by
  cases hparse : Cedar.Spec.Ext.Datetime.parse s with
  | none =>
      rw [Option.map_none]
      exact (Datetime.parse_reject s).mpr ((parser_rejects_iff s).mp hparse)
  | some d =>
      rw [Option.map_some]
      obtain ⟨hvalid, hvalue⟩ := (parser_agrees s d).mp hparse
      exact Datetime.parse_complete s (datetimeMillis d) hvalid hvalue

end Datetime.RuleRegistryProof
