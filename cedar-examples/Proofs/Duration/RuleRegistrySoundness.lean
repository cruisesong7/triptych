import Proofs.Duration.RuleRegistryProof

/-!
# End-to-end Duration soundness from executable rules

The external parser is related directly to Triptych's generated grammar, constraints, and
denotation. No Cedar Duration parser soundness or completeness theorem is imported.
-/

open Cedar.Spec.Ext
open Cedar.Spec.Ext.Datetime
open CedarExamples.Duration
open Triptych

namespace Duration.RuleRegistrySoundness

open Duration.RuleRegistryProof

private theorem duration?_eq_some_iff (i : Int) (duration : Duration) :
    Cedar.Spec.Ext.Datetime.duration? i = some duration ↔
      i = durationMillis duration := by
  rcases duration with ⟨duration⟩
  unfold Cedar.Spec.Ext.Datetime.duration? durationMillis
    Cedar.Spec.Ext.Datetime.Duration.toMilliseconds
  constructor
  · intro h
    cases hvalue : Int64.ofInt? i with
    | none => simp [hvalue] at h
    | some result =>
        rw [hvalue] at h
        have hresult : result = duration := by
          simpa using Option.some.inj h
        subst result
        exact (Int64.ofInt?_some_toInt hvalue).symm
  · intro h
    rw [h]
    rw [Int64.ofInt?_toInt]
    rfl

private theorem valid_parts {s : String} (hvalid : Duration.IsValid s) :
    ∃ sgn components,
      decode Duration.grammar s =
          some
            ([("Sign", sgn), ("Components", components.asString)] ++
              Duration.GrammarView.componentsCaptures components) ∧
      (sgn = "-" ∨ sgn = "") ∧
      s = sgn ++ components.asString ∧
      Duration.GrammarView.ComponentsWf components ∧
      components.nonempty ∧
      (-9223372036854775808 : Int) ≤
          Duration.GrammarView.formatValue sgn components ∧
        Duration.GrammarView.formatValue sgn components ≤
          (9223372036854775807 : Int) := by
  obtain ⟨sgn, components, hdecode, hsign, hs, hwf⟩ :=
    Duration.GrammarView.decode_parts_of_surface_wf hvalid.1.1
  have hnonempty :
      components.nonempty := by
    apply (Duration.GrammarView.components_nonempty_iff components).mp
    exact
      (Duration.GrammarView.wf_constraints_of_decode s sgn components hdecode).mp
        hvalid.1.2
  have hbounds :=
    (Duration.GrammarView.constraints_of_decode s sgn components hdecode).mp
      hvalid.2
  exact ⟨sgn, components, hdecode, hsign, hs, hwf, hnonempty, hbounds⟩

/-- Cedar's executable Duration parser returns exactly Triptych-valid denotations. -/
theorem parser_agrees (s : String) (duration : Duration) :
    Cedar.Spec.Ext.Datetime.Duration.parse s = some duration ↔
      _root_.Duration.IsValid s ∧
        _root_.Duration.computeValue s = some (durationMillis duration) := by
  constructor
  · intro hparse
    obtain ⟨sgn, components, hsign, hs, hwf, hnonempty, hresult⟩ :=
      parts_of_parse_eq_some hparse
    have hsurface : _root_.Duration.IsWf.Duration s :=
      ⟨sgn, components.asString,
        ⟨hs, hsign⟩, Duration.GrammarView.components_to_surface components hwf⟩
    obtain ⟨decodedSign, decoded, hdecode, hdecodedSign, hdecodedS, hdecodedWf⟩ :=
      Duration.GrammarView.decode_parts_of_surface_wf hsurface
    obtain ⟨hsignEq, hcomponentsEq⟩ :=
      rendered_parts_unique hsign hdecodedSign hs hdecodedS hwf hdecodedWf
    subst decodedSign
    subst decoded
    have hvalueEq :
        Duration.GrammarView.formatValue sgn components =
          durationMillis duration :=
      (duration?_eq_some_iff _ _).mp hresult
    have hbounds :
        (-9223372036854775808 : Int) ≤
            Duration.GrammarView.formatValue sgn components ∧
          Duration.GrammarView.formatValue sgn components ≤
            (9223372036854775807 : Int) := by
      rw [hvalueEq]
      unfold durationMillis Cedar.Spec.Ext.Datetime.Duration.toMilliseconds
      constructor
      · have hmin : Int64.«MIN» = (-9223372036854775808 : Int) := by
          decide
        rw [← hmin]
        exact Int64.le_toInt duration.val
      · have hmax : Int64.«MAX» = (9223372036854775807 : Int) := by
          decide
        rw [← hmax]
        have := Int64.toInt_lt duration.val
        omega
    have hwfConstraints : _root_.Duration.SatisfiesWfConstraints s :=
      (Duration.GrammarView.wf_constraints_of_decode s sgn components hdecode).mpr
        ((Duration.GrammarView.components_nonempty_iff components).mpr hnonempty)
    have hconstraints : _root_.Duration.SatisfiesConstraints s :=
      (Duration.GrammarView.constraints_of_decode s sgn components hdecode).mpr
        hbounds
    refine ⟨⟨⟨hsurface, hwfConstraints⟩, hconstraints⟩, ?_⟩
    rw [Duration.GrammarView.format_compute_of_decode s sgn components hdecode]
    exact congrArg some hvalueEq
  · rintro ⟨hvalid, hcompute⟩
    obtain ⟨sgn, components, hdecode, hsign, hs, hwf, hnonempty, hbounds⟩ :=
      valid_parts hvalid
    have hformat :
        _root_.Duration.computeValue s =
          some (Duration.GrammarView.formatValue sgn components) :=
      Duration.GrammarView.format_compute_of_decode s sgn components hdecode
    rw [hcompute] at hformat
    have hvalueEq :
        Duration.GrammarView.formatValue sgn components =
          durationMillis duration :=
      (Option.some.inj hformat).symm
    rw [parse_of_parts s sgn components hsign hs hwf hnonempty hbounds]
    exact (duration?_eq_some_iff _ _).mpr hvalueEq

theorem parser_rejects_iff (s : String) :
    Cedar.Spec.Ext.Datetime.Duration.parse s = none ↔
      ¬_root_.Duration.IsValid s := by
  constructor
  · intro hnone hvalid
    obtain ⟨sgn, components, hdecode, hsign, hs, hwf, hnonempty, hbounds⟩ :=
      valid_parts hvalid
    have hcompute :=
      Duration.GrammarView.format_compute_of_decode s sgn components hdecode
    have hparse :=
      parse_of_parts s sgn components hsign hs hwf hnonempty hbounds
    have hsome :
        Cedar.Spec.Ext.Datetime.duration?
            (Duration.GrammarView.formatValue sgn components) ≠
          none := by
      unfold Cedar.Spec.Ext.Datetime.duration?
      have hofInt :
          Int64.ofInt? (Duration.GrammarView.formatValue sgn components) =
            some (Int64.ofInt
              (Duration.GrammarView.formatValue sgn components)) := by
        apply Int64.ofInt?_some_iff.mp
        simpa only [Int64.«MIN», Int64.«MAX»] using hbounds
      rw [hofInt]
      simp
    rw [hnone] at hparse
    exact hsome hparse.symm
  · intro hinvalid
    cases hparse : Cedar.Spec.Ext.Datetime.Duration.parse s with
    | none => rfl
    | some duration =>
        exact (hinvalid ((parser_agrees s duration).mp hparse).1).elim

end Duration.RuleRegistrySoundness
