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

private theorem append_eq_append_of_length {a b c d : String}
    (h : a ++ b = c ++ d) (hlen : a.length = c.length) :
    a = c ∧ b = d := by
  have hl := congrArg String.toList h
  simp only [String.toList_append] at hl
  have hlen' : a.toList.length = c.toList.length := by
    exact String.length_toList.trans (hlen.trans String.length_toList.symm)
  exact (List.append_inj hl hlen').imp String.toList_injective String.toList_injective

private theorem date_asString_injective
    {d d' : Cedar.Thm.Datetime.DateComponents}
    (hd : d.syntaxWf) (hd' : d'.syntaxWf)
    (h : d.asString = d'.asString) :
    d = d' := by
  rcases d with ⟨year, month, day⟩
  rcases d' with ⟨year', month', day'⟩
  rcases hd with ⟨hy, hm, hday⟩
  rcases hd' with ⟨hy', hm', hday'⟩
  simp only [Cedar.Thm.Datetime.DateComponents.asString, String.append_assoc] at h
  obtain ⟨hyear, htail⟩ :=
    append_eq_append_of_length h (hy.2.trans hy'.2.symm)
  subst year'
  have htail := (String.append_right_inj "-").mp htail
  obtain ⟨hmonth, hdayEq⟩ :=
    append_eq_append_of_length htail (hm.2.trans hm'.2.symm)
  subst month'
  have hdayEq := (String.append_right_inj "-").mp hdayEq
  exact congrArg (Cedar.Thm.Datetime.DateComponents.mk year month) hdayEq

private theorem time_asString_injective
    {t t' : Cedar.Thm.Datetime.TimeComponents}
    (ht : t.syntaxWf) (ht' : t'.syntaxWf)
    (h : t.asString = t'.asString) :
    t = t' := by
  rcases t with ⟨hours, minutes, seconds⟩
  rcases t' with ⟨hours', minutes', seconds'⟩
  rcases ht with ⟨hh, hm, hs⟩
  rcases ht' with ⟨hh', hm', hs'⟩
  simp only [Cedar.Thm.Datetime.TimeComponents.asString, String.append_assoc] at h
  obtain ⟨hhours, htail⟩ :=
    append_eq_append_of_length h (hh.2.trans hh'.2.symm)
  subst hours'
  have htail := (String.append_right_inj ":").mp htail
  obtain ⟨hminutes, hseconds⟩ :=
    append_eq_append_of_length htail (hm.2.trans hm'.2.symm)
  subst minutes'
  have hseconds := (String.append_right_inj ":").mp hseconds
  exact congrArg (Cedar.Thm.Datetime.TimeComponents.mk hours minutes) hseconds

private theorem offset_asString_injective
    {o o' : Cedar.Thm.Datetime.OffsetComponents}
    (ho : o.syntaxWf) (ho' : o'.syntaxWf)
    (h : o.asString = o'.asString) :
    o = o' := by
  rcases o with ⟨negative, hours, minutes⟩
  rcases o' with ⟨negative', hours', minutes'⟩
  rcases ho with ⟨hh, hm⟩
  rcases ho' with ⟨hh', hm'⟩
  cases negative <;> cases negative'
  · simp [Cedar.Thm.Datetime.OffsetComponents.asString, String.append_assoc] at h
    obtain ⟨rfl, rfl⟩ :=
      append_eq_append_of_length h (hh.2.trans hh'.2.symm)
    rfl
  · simp [Cedar.Thm.Datetime.OffsetComponents.asString, String.append_assoc] at h
    have hsign := (append_eq_append_of_length h (by decide)).1
    contradiction
  · simp [Cedar.Thm.Datetime.OffsetComponents.asString, String.append_assoc] at h
    have hsign := (append_eq_append_of_length h (by decide)).1
    contradiction
  · simp [Cedar.Thm.Datetime.OffsetComponents.asString, String.append_assoc] at h
    obtain ⟨rfl, rfl⟩ :=
      append_eq_append_of_length h (hh.2.trans hh'.2.symm)
    rfl

private theorem offset_asString_length
    (o : Cedar.Thm.Datetime.OffsetComponents) (ho : o.syntaxWf) :
    o.asString.length = 5 := by
  rcases o with ⟨negative, hours, minutes⟩
  rcases ho with ⟨hh, hm⟩
  have hplus : "+".length = 1 := by native_decide
  have hminus : "-".length = 1 := by native_decide
  cases negative <;>
    simp [Cedar.Thm.Datetime.OffsetComponents.asString, hh.2, hm.2, hplus, hminus]

private theorem offset_asString_ne_millisUtc
    (o : Cedar.Thm.Datetime.OffsetComponents) (millis : String) :
    o.asString ≠ "." ++ millis ++ "Z" := by
  intro h
  rcases o with ⟨negative, hours, minutes⟩
  cases negative
  · have hfirst :=
      (append_eq_append_of_length
        (by simpa [Cedar.Thm.Datetime.OffsetComponents.asString,
          String.append_assoc] using h) (by decide)).1
    contradiction
  · have hfirst :=
      (append_eq_append_of_length
        (by simpa [Cedar.Thm.Datetime.OffsetComponents.asString,
          String.append_assoc] using h) (by decide)).1
    contradiction

private def millisString : Option String → String
  | none => ""
  | some millis => "." ++ millis

private def timeTailString (millis : Option String) (zone : Cedar.Thm.Datetime.Zone) :
    String :=
  millisString millis ++ zone.asString

private def millisWidth : Option String → Nat
  | none => 0
  | some _ => 4

private def zoneWidth : Cedar.Thm.Datetime.Zone → Nat
  | .utc => 1
  | .offset _ => 5

private theorem timeTail_length
    (millis : Option String) (zone : Cedar.Thm.Datetime.Zone)
    (hmillis : Cedar.Thm.Datetime.IsWfOptionalMillis millis)
    (hzone : zone.syntaxWf) :
    (timeTailString millis zone).length = millisWidth millis + zoneWidth zone := by
  have hdot : ".".length = 1 := by native_decide
  have hZ : "Z".length = 1 := by native_decide
  cases millis with
  | none =>
      cases zone with
      | utc =>
          simp [timeTailString, millisString, millisWidth, zoneWidth,
            Cedar.Thm.Datetime.Zone.asString, hZ]
      | offset offset =>
          simp [timeTailString, millisString, millisWidth, zoneWidth,
            Cedar.Thm.Datetime.Zone.asString,
            offset_asString_length offset hzone]
  | some millis =>
      change String.IsFixedDigits 3 millis at hmillis
      cases zone with
      | utc =>
          simp [timeTailString, millisString, millisWidth, zoneWidth,
            Cedar.Thm.Datetime.Zone.asString, hdot, hZ, hmillis.2]
      | offset offset =>
          simp [timeTailString, millisString, millisWidth, zoneWidth,
            Cedar.Thm.Datetime.Zone.asString, hdot, hmillis.2,
            offset_asString_length offset hzone]

private theorem timeTail_injective
    {millis millis' : Option String}
    {zone zone' : Cedar.Thm.Datetime.Zone}
    (hmillis : Cedar.Thm.Datetime.IsWfOptionalMillis millis)
    (hmillis' : Cedar.Thm.Datetime.IsWfOptionalMillis millis')
    (hzone : zone.syntaxWf) (hzone' : zone'.syntaxWf)
    (h : timeTailString millis zone = timeTailString millis' zone') :
    millis = millis' ∧ zone = zone' := by
  cases millis with
  | none =>
      cases zone with
      | utc =>
          cases millis' with
          | none =>
              cases zone' with
              | utc => exact ⟨rfl, rfl⟩
              | offset offset =>
                  have hlen := congrArg String.length h
                  rw [timeTail_length none .utc hmillis hzone,
                    timeTail_length none (.offset offset) hmillis' hzone'] at hlen
                  simp [millisWidth, zoneWidth] at hlen
          | some millis' =>
              cases zone' with
              | utc =>
                  have hlen := congrArg String.length h
                  rw [timeTail_length none .utc hmillis hzone,
                    timeTail_length (some millis') .utc hmillis' hzone'] at hlen
                  simp [millisWidth, zoneWidth] at hlen
              | offset offset =>
                  have hlen := congrArg String.length h
                  rw [timeTail_length none .utc hmillis hzone,
                    timeTail_length (some millis') (.offset offset) hmillis' hzone'] at hlen
                  simp [millisWidth, zoneWidth] at hlen
      | offset offset =>
          cases millis' with
          | none =>
              cases zone' with
              | utc =>
                  have hlen := congrArg String.length h
                  rw [timeTail_length none (.offset offset) hmillis hzone,
                    timeTail_length none .utc hmillis' hzone'] at hlen
                  simp [millisWidth, zoneWidth] at hlen
              | offset offset' =>
                  exact ⟨rfl, congrArg Cedar.Thm.Datetime.Zone.offset
                    (offset_asString_injective hzone hzone' h)⟩
          | some millis' =>
              cases zone' with
              | utc =>
                  exact absurd (by
                    simpa [timeTailString, millisString,
                      Cedar.Thm.Datetime.Zone.asString] using h)
                    (offset_asString_ne_millisUtc offset millis')
              | offset offset' =>
                  have hlen := congrArg String.length h
                  rw [timeTail_length none (.offset offset) hmillis hzone,
                    timeTail_length (some millis') (.offset offset') hmillis' hzone'] at hlen
                  simp [millisWidth, zoneWidth] at hlen
  | some millis =>
      cases zone with
      | utc =>
          cases millis' with
          | none =>
              cases zone' with
              | utc =>
                  have hlen := congrArg String.length h
                  rw [timeTail_length (some millis) .utc hmillis hzone,
                    timeTail_length none .utc hmillis' hzone'] at hlen
                  simp [millisWidth, zoneWidth] at hlen
              | offset offset' =>
                  exact absurd (by
                    simpa [timeTailString, millisString,
                      Cedar.Thm.Datetime.Zone.asString] using h.symm)
                    (offset_asString_ne_millisUtc offset' millis)
          | some millis' =>
              cases zone' with
              | utc =>
                  have h' := (String.append_right_inj ".").mp
                    (by simpa [timeTailString, millisString,
                      Cedar.Thm.Datetime.Zone.asString, String.append_assoc] using h)
                  have hm : millis = millis' := h'
                  subst millis'
                  exact ⟨rfl, rfl⟩
              | offset offset' =>
                  have hlen := congrArg String.length h
                  rw [timeTail_length (some millis) .utc hmillis hzone,
                    timeTail_length (some millis') (.offset offset') hmillis' hzone'] at hlen
                  simp [millisWidth, zoneWidth] at hlen
      | offset offset =>
          cases millis' with
          | none =>
              cases zone' with
              | utc =>
                  have hlen := congrArg String.length h
                  rw [timeTail_length (some millis) (.offset offset) hmillis hzone,
                    timeTail_length none .utc hmillis' hzone'] at hlen
                  simp [millisWidth, zoneWidth] at hlen
              | offset offset' =>
                  have hlen := congrArg String.length h
                  rw [timeTail_length (some millis) (.offset offset) hmillis hzone,
                    timeTail_length none (.offset offset') hmillis' hzone'] at hlen
                  simp [millisWidth, zoneWidth] at hlen
          | some millis' =>
              cases zone' with
              | utc =>
                  have hlen := congrArg String.length h
                  rw [timeTail_length (some millis) (.offset offset) hmillis hzone,
                    timeTail_length (some millis') .utc hmillis' hzone'] at hlen
                  simp [millisWidth, zoneWidth] at hlen
              | offset offset' =>
                  have h' := (String.append_right_inj ".").mp
                    (by simpa [timeTailString, millisString,
                      Cedar.Thm.Datetime.Zone.asString, String.append_assoc] using h)
                  obtain ⟨hm, ho⟩ :=
                    append_eq_append_of_length h' (hmillis.2.trans hmillis'.2.symm)
                  subst millis'
                  exact ⟨rfl, congrArg Cedar.Thm.Datetime.Zone.offset
                    (offset_asString_injective hzone hzone' ho)⟩

private theorem time_asString_length
    (time : Cedar.Thm.Datetime.TimeComponents) (htime : time.syntaxWf) :
    time.asString.length = 8 := by
  rcases time with ⟨hours, minutes, seconds⟩
  rcases htime with ⟨hh, hm, hs⟩
  have hcolon : ":".length = 1 := by native_decide
  simp [Cedar.Thm.Datetime.TimeComponents.asString, hh.2, hm.2, hs.2, hcolon]

private theorem date_asString_length
    (date : Cedar.Thm.Datetime.DateComponents) (hdate : date.syntaxWf) :
    date.asString.length = 10 := by
  rcases date with ⟨year, month, day⟩
  rcases hdate with ⟨hy, hm, hd⟩
  have hdash : "-".length = 1 := by native_decide
  simp [Cedar.Thm.Datetime.DateComponents.asString, hy.2, hm.2, hd.2, hdash]

private theorem timePart_asString_ne_empty (tp : Cedar.Thm.Datetime.TimePart) :
    tp.asString ≠ "" := by
  intro h
  have hlist := congrArg String.toList h
  simp [Cedar.Thm.Datetime.TimePart.asString, String.toList_append] at hlist

private theorem timePart_asString_injective
    {tp tp' : Cedar.Thm.Datetime.TimePart}
    (htp : tp.syntaxWf) (htp' : tp'.syntaxWf)
    (h : tp.asString = tp'.asString) :
    tp = tp' := by
  rcases tp with ⟨time, millis, zone⟩
  rcases tp' with ⟨time', millis', zone'⟩
  rcases htp with ⟨htime, hmillis, hzone⟩
  rcases htp' with ⟨htime', hmillis', hzone'⟩
  change Cedar.Thm.Datetime.IsWfOptionalMillis millis at hmillis
  change Cedar.Thm.Datetime.IsWfOptionalMillis millis' at hmillis'
  change zone.syntaxWf at hzone
  change zone'.syntaxWf at hzone'
  simp only [Cedar.Thm.Datetime.TimePart.asString, String.append_assoc] at h
  have h := (String.append_right_inj "T").mp h
  obtain ⟨htimeString, htail⟩ :=
    append_eq_append_of_length h
      ((time_asString_length time htime).trans
        (time_asString_length time' htime').symm)
  have htimeEq : time = time' :=
    time_asString_injective htime htime' htimeString
  subst time'
  change timeTailString millis zone = timeTailString millis' zone' at htail
  obtain ⟨hmillisEq, hzoneEq⟩ :=
    timeTail_injective (millis := millis) (millis' := millis')
      (zone := zone) (zone' := zone') hmillis hmillis' hzone hzone' htail
  cases hmillisEq
  cases hzoneEq
  rfl

theorem components_eq_of_asString
    {c c' : Cedar.Thm.Datetime.DatetimeComponents}
    (hc : c.syntaxWf) (hc' : c'.syntaxWf)
    (h : c.asString = c'.asString) :
    c = c' := by
  rcases c with ⟨date, time⟩
  rcases c' with ⟨date', time'⟩
  simp only [Cedar.Thm.Datetime.DatetimeComponents.syntaxWf] at hc hc'
  simp only [Cedar.Thm.Datetime.DatetimeComponents.asString, String.append_assoc] at h
  obtain ⟨hdateString, htimeString⟩ :=
    append_eq_append_of_length h
      ((date_asString_length date hc.1).trans
        (date_asString_length date' hc'.1).symm)
  have hdate : date = date' :=
    date_asString_injective hc.1 hc'.1 hdateString
  subst date'
  cases time with
  | none =>
      cases time' with
      | none => rfl
      | some timePart' =>
          exfalso
          exact timePart_asString_ne_empty timePart' htimeString.symm
  | some timePart =>
      cases time' with
      | none =>
          exfalso
          exact timePart_asString_ne_empty timePart htimeString
      | some timePart' =>
          have htimePart : timePart = timePart' :=
            timePart_asString_injective hc.2 hc'.2 htimeString
          subst timePart'
          rfl

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

theorem computeValue_eq_of_isDatetimeValue
    {s : String} {result : Int}
    (hvalue : Cedar.Thm.Datetime.IsDatetimeValue s result) :
    Datetime.computeValue s = some result := by
  obtain ⟨c, ⟨hsyn, hconstraints, hs⟩, hv⟩ := hvalue
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
  rw [Datetime.computeValue_view, hview]
  simp only [Option.map_some]
  rw [hv]
  exact congrArg some (view_denotation_eq_toMillis hc' hsyn)

end Datetime.GrammarView
