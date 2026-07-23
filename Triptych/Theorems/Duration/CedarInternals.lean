module

public import Cedar.Thm.Ext.Duration.Grammar

import all Cedar.Thm.Ext.Duration.Lemmas

/-!
# Cedar Duration compatibility boundary

Cedar keeps its extraction-chain lemmas private. This module uses `import all` once to
republish the component-level value theorem needed by the Triptych bridge.
-/

namespace Triptych.Theorems.Duration.CedarInternals

open Cedar.Spec.Ext
open Cedar.Spec.Ext.Datetime
open Cedar.Thm.Duration

public def quantityNat : Option String → Nat
  | none => 0
  | some digits => (toNat?' digits).getD 0

private def ChunkBoundary (s : String) : Prop :=
  s = "" ∨ ∃ c cs, s.toList.reverse = c :: cs ∧ c.isDigit = false

private theorem empty_boundary : ChunkBoundary "" :=
  Or.inl rfl

private theorem append_chunk_boundary (pfx : String) (digits : Option String)
    (suffix : String) (hboundary : ChunkBoundary pfx)
    (hwf : IsWfOptionalQuantity digits)
    (hsuffix : suffix = "d" ∨ suffix = "h" ∨ suffix = "m" ∨
      suffix = "s" ∨ suffix = "ms") :
    ChunkBoundary (pfx ++ durationChunk digits suffix) := by
  cases digits with
  | none =>
      simpa [durationChunk] using hboundary
  | some value =>
      exact Or.inr
        (Cedar.Thm.Duration.pfx_append_chunk_reverse_non_digit pfx value suffix hwf hsuffix)

private theorem extract_self_value_zero (s suffix : String) (n : Nat)
    (hsuffix : suffix ≠ "")
    (h : extractTrailingQuantity s suffix = some (n, s)) :
    n = 0 := by
  unfold extractTrailingQuantity at h
  by_cases hends : s.endsWith suffix
  · simp only [hends, if_true] at h
    cases hnat :
        toNat?' (String.ofList
          ((s.dropEnd suffix.length).toString.toList.reverse.takeWhile
            Char.isDigit |>.reverse)) with
    | none =>
        rw [hnat] at h
        contradiction
    | some value =>
        rw [hnat] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        have hlist := congrArg String.toList h.2
        simp at hlist
        have htakeLen := congrArg List.length hlist
        simp at htakeLen
        have hsuffixPos : 0 < suffix.length := by
          rw [Nat.pos_iff_ne_zero, ne_eq, String.length_eq_zero_iff]
          exact hsuffix
        have hsNe : s ≠ "" := by
          intro hs
          subst s
          simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice,
            hsuffix] at hends
        have hsListNe : s.toList ≠ [] := by
          intro hsList
          apply hsNe
          apply String.ext
          simpa using hsList
        have hsListPos : 0 < s.toList.length :=
          List.length_pos_iff.mpr hsListNe
        omega
  · simp [hends] at h
    exact h.symm

private theorem exact_extract_of_exists (input pfx suffix : String)
    (digits : Option String) (hwf : IsWfOptionalQuantity digits)
    (hinput : input = pfx ++ durationChunk digits suffix)
    (hboundary : ChunkBoundary pfx) (hsuffix : suffix ≠ "")
    (hexists : ∃ n, extractTrailingQuantity input suffix = some (n, pfx)) :
    extractTrailingQuantity input suffix = some (quantityNat digits, pfx) := by
  cases digits with
  | none =>
      obtain ⟨n, hn⟩ := hexists
      have hzero : n = 0 := by
        apply extract_self_value_zero input suffix n hsuffix
        simpa [hinput, durationChunk] using hn
      simpa [quantityNat, hzero] using hn
  | some digits =>
      have hdigits : _root_.IsDigits digits := hwf
      obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hdigits.toNat?'_isSome
      have hstep :=
        Cedar.Thm.Duration.extract_step_chain_some pfx digits suffix n hdigits hnat hboundary
      simpa [hinput, durationChunk, quantityNat, hnat, String.append_assoc] using hstep

public theorem computeBodyValue_components (components : Components)
    (hwf : components.quantitiesWf) :
    computeBodyValue components.asString =
      some
        ((quantityNat components.days : Int) * MILLISECONDS_PER_DAY +
          (quantityNat components.hours : Int) * MILLISECONDS_PER_HOUR +
          (quantityNat components.minutes : Int) * MILLISECONDS_PER_MINUTE +
          (quantityNat components.seconds : Int) * MILLISECONDS_PER_SECOND +
          (quantityNat components.milliseconds : Int)) := by
  rcases components with ⟨days, hours, minutes, seconds, milliseconds⟩
  simp only [Components.quantitiesWf, IsWfOptionalQuantity] at hwf
  rcases hwf with ⟨hwfDays, hwfHours, hwfMinutes, hwfSeconds, hwfMillis⟩
  let daysChunk := durationChunk days "d"
  let hoursChunk := durationChunk hours "h"
  let minutesChunk := durationChunk minutes "m"
  let secondsChunk := durationChunk seconds "s"
  have boundaryDays : ChunkBoundary daysChunk := by
    simpa [daysChunk] using
      append_chunk_boundary "" days "d" empty_boundary hwfDays (Or.inl rfl)
  have boundaryHours : ChunkBoundary (daysChunk ++ hoursChunk) := by
    simpa [hoursChunk] using
      append_chunk_boundary daysChunk hours "h" boundaryDays hwfHours
        (Or.inr (Or.inl rfl))
  have boundaryMinutes :
      ChunkBoundary (daysChunk ++ hoursChunk ++ minutesChunk) := by
    simpa [minutesChunk] using
      append_chunk_boundary (daysChunk ++ hoursChunk) minutes "m" boundaryHours hwfMinutes
        (Or.inr (Or.inr (Or.inl rfl)))
  have boundarySeconds :
      ChunkBoundary (daysChunk ++ hoursChunk ++ minutesChunk ++ secondsChunk) := by
    simpa [secondsChunk] using
      append_chunk_boundary (daysChunk ++ hoursChunk ++ minutesChunk) seconds "s"
        boundaryMinutes hwfSeconds (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have eMillis :
      extractTrailingQuantity
          (Components.asString ⟨days, hours, minutes, seconds, milliseconds⟩) "ms" =
        some (quantityNat milliseconds,
          daysChunk ++ hoursChunk ++ minutesChunk ++ secondsChunk) := by
    apply exact_extract_of_exists _ _ _ milliseconds hwfMillis
    · simp [Components.asString, daysChunk, hoursChunk, minutesChunk, secondsChunk,
        String.append_assoc]
    · exact boundarySeconds
    · decide
    · simpa [daysChunk, hoursChunk, minutesChunk, secondsChunk, String.append_assoc] using
        Cedar.Thm.Duration.extract_ms_step days hours minutes seconds milliseconds
          hwfSeconds hwfMillis
  have eSeconds :
      extractTrailingQuantity
          (daysChunk ++ hoursChunk ++ minutesChunk ++ secondsChunk) "s" =
        some (quantityNat seconds, daysChunk ++ hoursChunk ++ minutesChunk) := by
    apply exact_extract_of_exists _ _ _ seconds hwfSeconds
    · simp [daysChunk, hoursChunk, minutesChunk, secondsChunk, String.append_assoc]
    · exact boundaryMinutes
    · decide
    · simpa [daysChunk, hoursChunk, minutesChunk, secondsChunk, String.append_assoc] using
        Cedar.Thm.Duration.extract_s_step days hours minutes seconds
          hwfDays hwfHours hwfSeconds
  have eMinutes :
      extractTrailingQuantity (daysChunk ++ hoursChunk ++ minutesChunk) "m" =
        some (quantityNat minutes, daysChunk ++ hoursChunk) := by
    apply exact_extract_of_exists _ _ _ minutes hwfMinutes
    · simp [daysChunk, hoursChunk, minutesChunk, String.append_assoc]
    · exact boundaryHours
    · decide
    · simpa [daysChunk, hoursChunk, minutesChunk, String.append_assoc] using
        Cedar.Thm.Duration.extract_m_step days hours minutes hwfDays hwfHours hwfMinutes
  have eHours :
      extractTrailingQuantity (daysChunk ++ hoursChunk) "h" =
        some (quantityNat hours, daysChunk) := by
    apply exact_extract_of_exists _ _ _ hours hwfHours
    · simp [daysChunk, hoursChunk]
    · exact boundaryDays
    · decide
    · simpa [daysChunk, hoursChunk] using
        Cedar.Thm.Duration.extract_h_step days hours hwfDays hwfHours
  have eDays :
      extractTrailingQuantity daysChunk "d" = some (quantityNat days, "") := by
    apply exact_extract_of_exists _ _ _ days hwfDays
    · simp [daysChunk]
    · exact empty_boundary
    · decide
    · simpa [daysChunk] using Cedar.Thm.Duration.extract_d_step days hwfDays
  exact Cedar.Thm.Duration.computeBodyValue_of_extracts
    (Components.asString ⟨days, hours, minutes, seconds, milliseconds⟩)
    (daysChunk ++ hoursChunk ++ minutesChunk ++ secondsChunk)
    (daysChunk ++ hoursChunk ++ minutesChunk) (daysChunk ++ hoursChunk) daysChunk
    (quantityNat milliseconds) (quantityNat seconds) (quantityNat minutes)
    (quantityNat hours) (quantityNat days) eMillis eSeconds eMinutes eHours eDays

public theorem isWfBody_front_ne_dash (body : String) (h : IsWfBody body) :
    body.front ≠ '-' :=
  Cedar.Thm.Duration.duration_body_front_ne_dash body h

public theorem computeValue_neg_body (body : String) :
    computeValue ("-" ++ body) = computeSignedBodyValue true body := by
  unfold computeValue
  rw [Cedar.Thm.Duration.isNegativeDuration_neg_body]

public theorem computeValue_pos_body (body : String) (hfront : body.front ≠ '-') :
    computeValue body = computeSignedBodyValue false body := by
  unfold computeValue
  rw [Cedar.Thm.Duration.isNegativeDuration_canonical_body body hfront]

end Triptych.Theorems.Duration.CedarInternals
