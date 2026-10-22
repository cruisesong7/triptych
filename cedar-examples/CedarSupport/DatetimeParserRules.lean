import CedarSupport.Datetime
import Triptych.Automation.ExternalParser

/-!
# Cedar Datetime parser rules

Reusable successful-path summary for Cedar's `Std.Time`-backed Datetime parser. The expensive
`Parsec` inversion is proved once in cedar-lean; format proofs consume this registered component
normal form instead of importing or replaying those internals.
-/

open Cedar.Spec.Ext

namespace CedarSupport.DatetimeParserRules

/-- Cedar's Datetime parser succeeds exactly on well-formed canonical components with the
    returned epoch-millisecond value. -/
@[triptych_parser, triptych_parser_search =]
theorem parse_eq_some_iff_components {s : String} {d : Datetime} :
    Datetime.parse s = some d ↔
      ∃ components : Cedar.Thm.Datetime.DatetimeComponents,
        components.syntaxWf ∧
        components.constraintsWf ∧
        s = components.asString ∧
        components.toMillis = d.val.toInt := by
  constructor
  · intro hparse
    obtain ⟨components, ⟨hsyntax, hconstraints, hs⟩, hvalue⟩ :=
      Cedar.Thm.Datetime.parse_sound s d hparse
    exact ⟨components, hsyntax, hconstraints, hs, hvalue.symm⟩
  · rintro ⟨components, hsyntax, hconstraints, hs, hvalue⟩
    apply Cedar.Thm.Datetime.parse_complete s d
    exact ⟨components, ⟨hsyntax, hconstraints, hs⟩, hvalue.symm⟩

/-- Cedar rejects exactly strings outside its parser-independent Datetime grammar. -/
@[triptych_parser, triptych_parser_search =]
theorem parse_eq_none_iff_not_wf (s : String) :
    Datetime.parse s = none ↔ ¬Cedar.Thm.Datetime.IsWfDatetime s :=
  Cedar.Thm.Datetime.parse_eq_none_iff s

end CedarSupport.DatetimeParserRules
