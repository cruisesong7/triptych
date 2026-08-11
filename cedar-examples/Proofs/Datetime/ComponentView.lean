import Proofs.Datetime.DecodedComponents
import CedarSupport.Datetime

/-! Agreement between Datetime's generated view and parser-independent components. -/

open Triptych
open CedarExamples.Datetime

namespace Datetime.GrammarView

theorem surfaceDate {d : Cedar.Thm.Datetime.DateComponents}
    (h : d.syntaxWf) : Datetime.IsWf.Date d.asString := by
  rcases d with ⟨year, month, day⟩
  rcases h with ⟨hy, hm, hd⟩
  refine ⟨year, month, day, ⟨⟨rfl, ?_⟩, ?_⟩, ?_⟩
  · exact (fixedDigits_iff 4 (by omega) year).mpr hy
  · exact (fixedDigits_iff 2 (by omega) month).mpr hm
  · exact (fixedDigits_iff 2 (by omega) day).mpr hd

theorem surfaceTime {t : Cedar.Thm.Datetime.TimeComponents}
    (h : t.syntaxWf) : Datetime.IsWf.Time t.asString := by
  rcases t with ⟨hours, minutes, seconds⟩
  rcases h with ⟨hh, hm, hs⟩
  refine ⟨hours, minutes, seconds, ⟨⟨rfl, ?_⟩, ?_⟩, ?_⟩
  · exact (fixedDigits_iff 2 (by omega) hours).mpr hh
  · exact (fixedDigits_iff 2 (by omega) minutes).mpr hm
  · exact (fixedDigits_iff 2 (by omega) seconds).mpr hs

theorem surfaceOffset {o : Cedar.Thm.Datetime.OffsetComponents}
    (h : o.syntaxWf) : Datetime.IsWf.Offset o.asString := by
  rcases o with ⟨negative, hours, minutes⟩
  rcases h with ⟨hh, hm⟩
  have hh' : Datetime.IsWf.hh hours :=
    (fixedDigits_iff 2 (by omega) hours).mpr hh
  have hm' : Datetime.IsWf.mm minutes :=
    (fixedDigits_iff 2 (by omega) minutes).mpr hm
  cases negative
  · exact Or.inl ⟨hours, minutes, ⟨rfl, hh'⟩, hm'⟩
  · exact Or.inr ⟨hours, minutes, ⟨rfl, hh'⟩, hm'⟩

theorem surfaceSyntax_of_components
    {components : Cedar.Thm.Datetime.DatetimeComponents}
    (h : components.syntaxWf) :
    Datetime.IsWf.Datetime components.asString := by
  rcases components with ⟨date, time⟩
  cases time with
  | none =>
      exact Or.inl (Or.inl (Or.inl (Or.inl (by
        simpa [Cedar.Thm.Datetime.DatetimeComponents.asString] using
          surfaceDate h.1))))
  | some timePart =>
      rcases timePart with ⟨time, millis, zone⟩
      have hdate : Datetime.IsWf.Date date.asString := surfaceDate h.1
      have htime : Datetime.IsWf.Time time.asString := surfaceTime h.2.1
      cases millis with
      | none =>
          cases zone with
          | utc =>
              apply Or.inl
              apply Or.inl
              apply Or.inl
              apply Or.inr
              refine ⟨date.asString, time.asString, ?_⟩
              exact ⟨⟨by
                simp [Cedar.Thm.Datetime.DatetimeComponents.asString,
                  Cedar.Thm.Datetime.TimePart.asString,
                  Cedar.Thm.Datetime.Zone.asString, String.append_assoc], hdate⟩, htime⟩
          | offset offset =>
              apply Or.inl
              apply Or.inr
              refine ⟨date.asString, time.asString, offset.asString, ?_⟩
              exact ⟨⟨⟨by
                simp [Cedar.Thm.Datetime.DatetimeComponents.asString,
                  Cedar.Thm.Datetime.TimePart.asString,
                  Cedar.Thm.Datetime.Zone.asString, String.append_assoc], hdate⟩, htime⟩,
                surfaceOffset h.2.2.2⟩
      | some millis =>
          have hmillis : Datetime.IsWf.SSS millis :=
            (fixedDigits_iff 3 (by omega) millis).mpr h.2.2.1
          cases zone with
          | utc =>
              apply Or.inl
              apply Or.inl
              apply Or.inr
              refine ⟨date.asString, time.asString, millis, ?_⟩
              exact ⟨⟨⟨by
                simp [Cedar.Thm.Datetime.DatetimeComponents.asString,
                  Cedar.Thm.Datetime.TimePart.asString,
                  Cedar.Thm.Datetime.Zone.asString, String.append_assoc], hdate⟩,
                htime⟩, hmillis⟩
          | offset offset =>
              apply Or.inr
              refine ⟨date.asString, time.asString, millis, offset.asString, ?_⟩
              exact ⟨⟨⟨⟨by
                simp [Cedar.Thm.Datetime.DatetimeComponents.asString,
                  Cedar.Thm.Datetime.TimePart.asString,
                  Cedar.Thm.Datetime.Zone.asString, String.append_assoc], hdate⟩, htime⟩,
                hmillis⟩, surfaceOffset h.2.2.2⟩

theorem components_eq_of_asString
    {c c' : Cedar.Thm.Datetime.DatetimeComponents}
    (hc : c.syntaxWf) (hc' : c'.syntaxWf)
    (h : c.asString = c'.asString) :
    c = c' := by
  have hp := CedarSupport.Datetime.parseComponents_asString hc
  have hp' := CedarSupport.Datetime.parseComponents_asString hc'
  rw [h, hp'] at hp
  exact (Option.some.inj hp).symm

theorem isValid_iff_cedarWf (s : String) :
    Datetime.IsValid s ↔ Cedar.Thm.Datetime.IsWfDatetime s := by
  constructor
  · intro hvalid
    obtain ⟨v, hview, hvvalid⟩ := (Datetime.IsValid_view s).mp hvalid
    obtain ⟨c, hc, hvstr, hsyn⟩ := components_of_decodeView hview
    refine ⟨c, hsyn, (view_valid_iff_constraintsWf hc hsyn).mp hvvalid, ?_⟩
    calc
      s = v.input := (Datetime.decodeView_input hview).symm
      _ = c.asString := hvstr
  · rintro ⟨c, hsyn, hconstraints, hs⟩
    have hsurface : Datetime.IsWf.Datetime s := by
      rw [hs]
      exact surfaceSyntax_of_components hsyn
    have hgrammar : Triptych.IsWf Datetime.grammar s :=
      (Datetime.IsWfGrammar_equiv s).mpr hsurface
    have hsome : (decode Datetime.grammar s).isSome = true :=
      (decodeSome_iff_IsWf Datetime.grammar (by decide) s).mpr hgrammar
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
    let v := Datetime.View.ofMap s m
    have hview : Datetime.decodeView s = some v := by
      simp [Datetime.decodeView, v, hm]
    obtain ⟨c', hc', hvstr, hsyn'⟩ := components_of_decodeView hview
    have hcstr : c'.asString = c.asString := by
      calc
        c'.asString = v.input := hvstr.symm
        _ = s := Datetime.decodeView_input hview
        _ = c.asString := hs
    have hcc : c' = c := components_eq_of_asString hsyn' hsyn hcstr
    subst c'
    apply (Datetime.IsValid_view s).mpr
    exact ⟨v, hview, (view_valid_iff_constraintsWf hc' hsyn).mpr hconstraints⟩

theorem computeValue_eq_cedar (s : String) (hwf : Cedar.Thm.Datetime.IsWfDatetime s) :
    Datetime.computeValue s = Cedar.Thm.Datetime.computeValue s := by
  obtain ⟨c, hsyn, hconstraints, hs⟩ := hwf
  have hvalid : Datetime.IsValid s :=
    (isValid_iff_cedarWf s).mpr ⟨c, hsyn, hconstraints, hs⟩
  obtain ⟨v, hview, _⟩ := (Datetime.IsValid_view s).mp hvalid
  obtain ⟨c', hc', hvstr, hsyn'⟩ := components_of_decodeView hview
  have hcstr : c'.asString = c.asString := by
    calc
      c'.asString = v.input := hvstr.symm
      _ = s := Datetime.decodeView_input hview
      _ = c.asString := hs
  have hcc : c' = c := components_eq_of_asString hsyn' hsyn hcstr
  subst c'
  rw [Datetime.computeValue_view, hview, hs]
  unfold Cedar.Thm.Datetime.computeValue
  rw [CedarSupport.Datetime.parseComponents_asString hsyn]
  simp only [Option.map_some]
  exact congrArg some (view_denotation_eq_toMillis hc' hsyn)

end Datetime.GrammarView
