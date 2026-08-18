import Outputs.IPv4.parser
import CedarSupport.IPAddrInternals
import CedarSupport.ParserRules
import Triptych.Automation.ExternalParser

/-!
# IPv4 external-parser proof via the Triptych rule registry

This proof intentionally does not import `Cedar.Thm.Ext.IPAddr` or `IPv4.CedarBridge`.
It starts from Cedar's executable parser definitions and independently proved generic string
facts, then registers successful-path summaries for composition by `triptych_sound`.
-/

open Cedar.Spec.Ext
open Cedar.Spec.Ext.IPAddr
open CedarSupport.IPAddrInternals
open CedarSupport.String
open CedarSupport.StringInternals
open CedarSupport.ParserRules
open Triptych

namespace IPv4.RuleRegistryProof

/-- Parser-independent meaning of one IPv4 decimal octet. -/
def OctetValid (s : String) : Prop :=
  IsDigitsBetween 1 3 s ∧
    (s.startsWith "0" → s = "0") ∧ readNat s ≤ 255

/-- Cedar's octet parser implements `OctetValid` and returns the denoted byte. -/
@[triptych_parser, triptych_parser_search =]
theorem parseNumV4_eq_some_iff {s : String} {a : BitVec 8} :
    parseNumV4 s = some a ↔
      OctetValid s ∧ a = BitVec.ofNat 8 (readNat s) := by
  unfold OctetValid
  triptych_sound [parseNumV4]
  constructor
  · rintro ⟨hlen, hmax, hcanonical, hdigits, hbound, ha⟩
    refine ⟨⟨hdigits.1, by omega, hmax⟩, hcanonical, hbound, ?_⟩
    simpa using ha.symm
  · rintro ⟨⟨hdigits, hmin, hmax⟩, hcanonical, hbound, rfl⟩
    exact ⟨by omega, hmax, hcanonical, ⟨hdigits, hmin⟩, hbound, rfl⟩

def renderAddr (o₁ o₂ o₃ o₄ : String) : String :=
  o₁ ++ "." ++ o₂ ++ "." ++ o₃ ++ "." ++ o₄

def addrValue (o₁ o₂ o₃ o₄ : String) : IPv4Addr :=
  IPv4Addr.mk
    (BitVec.ofNat 8 (readNat o₁))
    (BitVec.ofNat 8 (readNat o₂))
    (BitVec.ofNat 8 (readNat o₃))
    (BitVec.ofNat 8 (readNat o₄))

private theorem noDotOfDigitsBetween {lo hi : Nat} {s : String}
    (h : IsDigitsBetween lo hi s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = '.')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq
  subst c
  have hdigit := h.1 '.' hc
  simp [TokClass.mem] at hdigit

/-- Successful dotted-quad parsing exposes exactly four valid octets and their denotation. -/
@[triptych_parser, triptych_parser_search =]
theorem parseSegsV4_eq_some_iff {s : String} {addr : IPv4Addr} :
    parseSegsV4 s = some addr ↔
      ∃ o₁ o₂ o₃ o₄,
        s = renderAddr o₁ o₂ o₃ o₄ ∧
        OctetValid o₁ ∧ OctetValid o₂ ∧ OctetValid o₃ ∧ OctetValid o₄ ∧
        addr = addrValue o₁ o₂ o₃ o₄ := by
  constructor
  · intro h
    unfold parseSegsV4 at h
    generalize hsplits : s.splitToList (· = '.') = parts at h
    rcases parts with _ | ⟨o₁, parts⟩
    · simp at h
    rcases parts with _ | ⟨o₂, parts⟩
    · simp at h
    rcases parts with _ | ⟨o₃, parts⟩
    · simp at h
    rcases parts with _ | ⟨o₄, parts⟩
    · simp at h
    rcases parts with _ | ⟨extra, parts⟩
    · triptych_sound at h
      refine ⟨o₁, o₂, o₃, o₄, ?_, h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
      · have hs := Triptych.eq_intercalate_of_splitToList_eq '.' hsplits
        repeat rw [String.intercalate_cons_cons] at hs
        rw [String.intercalate_singleton] at hs
        simpa [renderAddr, String.intercalate, String.append_assoc] using hs
      · simpa [addrValue] using h.2.2.2.2.symm
    · simp at h
  · rintro ⟨o₁, o₂, o₃, o₄, rfl, h₁, h₂, h₃, h₄, rfl⟩
    unfold parseSegsV4
    have hsplit :
        (renderAddr o₁ o₂ o₃ o₄).splitToList (· = '.') = [o₁, o₂, o₃, o₄] := by
      simpa [renderAddr, String.append_assoc] using
        (splitToListEq4 o₁ o₂ o₃ o₄ (fun x : Char => decide (x = '.')) '.'
          (by simp) (noDotOfDigitsBetween h₁.1) (noDotOfDigitsBetween h₂.1)
          (noDotOfDigitsBetween h₃.1) (noDotOfDigitsBetween h₄.1))
    rw [hsplit]
    triptych_sound
    exact ⟨h₁, h₂, h₃, h₄, by simp [addrValue]⟩

def OptionalPrefixValid : Option String → Prop
  | none => True
  | some pre => PrefixValid 2 32 pre

def renderNet (o₁ o₂ o₃ o₄ : String) (pre : Option String) : String :=
  renderAddr o₁ o₂ o₃ o₄ ++
    match pre with
    | none => ""
    | some p => "/" ++ p

def cidrValue (o₁ o₂ o₃ o₄ : String) (pre : Option String) : CIDR V4_WIDTH :=
  {
    addr := addrValue o₁ o₂ o₃ o₄
    pre :=
      match pre with
      | none => ADDR_SIZE V4_WIDTH
      | some p => Fin.ofNat (ADDR_SIZE V4_WIDTH + 1) (readNat p)
  }

def netValue (o₁ o₂ o₃ o₄ : String) (pre : Option String) : IPNet :=
  .V4 (cidrValue o₁ o₂ o₃ o₄ pre)

private theorem noSlashOfDigitsBetween {lo hi : Nat} {s : String}
    (h : IsDigitsBetween lo hi s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = '/')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq
  subst c
  have hdigit := h.1 '/' hc
  simp [TokClass.mem] at hdigit

private theorem noSlashAppend {s₁ s₂ : String}
    (h₁ : ∀ c ∈ s₁.toList, (fun x : Char => decide (x = '/')) c = false)
    (h₂ : ∀ c ∈ s₂.toList, (fun x : Char => decide (x = '/')) c = false) :
    ∀ c ∈ (s₁ ++ s₂).toList, (fun x : Char => decide (x = '/')) c = false := by
  intro c hc
  rw [String.toList_append] at hc
  rcases List.mem_append.mp hc with h | h
  · exact h₁ c h
  · exact h₂ c h

private theorem noSlashDot :
    ∀ c ∈ ".".toList, (fun x : Char => decide (x = '/')) c = false := by
  simp

private theorem noSlashOfAddr {o₁ o₂ o₃ o₄ : String}
    (h₁ : OctetValid o₁) (h₂ : OctetValid o₂)
    (h₃ : OctetValid o₃) (h₄ : OctetValid o₄) :
    ∀ c ∈ (renderAddr o₁ o₂ o₃ o₄).toList,
      (fun x : Char => decide (x = '/')) c = false := by
  simpa [renderAddr, String.append_assoc] using
    noSlashAppend (noSlashOfDigitsBetween h₁.1)
      (noSlashAppend noSlashDot
        (noSlashAppend (noSlashOfDigitsBetween h₂.1)
          (noSlashAppend noSlashDot
            (noSlashAppend (noSlashOfDigitsBetween h₃.1)
              (noSlashAppend noSlashDot (noSlashOfDigitsBetween h₄.1))))))

/-- Successful IPv4/CIDR parsing exposes its complete proof-facing component view. -/
@[triptych_parser, triptych_parser_search =]
theorem parseIPv4Net_eq_some_iff {s : String} {net : IPNet} :
    parseIPv4Net s = some net ↔
      ∃ o₁ o₂ o₃ o₄ pre,
        s = renderNet o₁ o₂ o₃ o₄ pre ∧
        OctetValid o₁ ∧ OctetValid o₂ ∧ OctetValid o₃ ∧ OctetValid o₄ ∧
        OptionalPrefixValid pre ∧ net = netValue o₁ o₂ o₃ o₄ pre := by
  constructor
  · intro h
    unfold parseIPv4Net at h
    generalize hsplits : s.splitToList (· = '/') = parts at h
    rcases parts with _ | ⟨addr, rest⟩
    · simp at h
    rcases rest with _ | ⟨pre, rest⟩
    · triptych_sound at h
      obtain ⟨a, ⟨o₁, o₂, o₃, o₄, haddr, h₁, h₂, h₃, h₄, ha⟩, hnet⟩ := h
      subst a
      have hs := Triptych.eq_intercalate_of_splitToList_eq '/' hsplits
      rw [String.intercalate_singleton] at hs
      refine ⟨o₁, o₂, o₃, o₄, none, ?_, h₁, h₂, h₃, h₄, trivial, ?_⟩
      · simpa [renderNet] using hs.trans haddr
      · simpa [netValue, cidrValue] using hnet.symm
    rcases rest with _ | ⟨extra, rest⟩
    · triptych_sound at h
      obtain ⟨hp, parsedPrefix, hprefix, parsedAddr,
        ⟨o₁, o₂, o₃, o₄, haddr, h₁, h₂, h₃, h₄, ha⟩, hnet⟩ := h
      simp only [Option.pure_def, Option.some.injEq] at hprefix
      subst parsedPrefix
      subst parsedAddr
      have hs := Triptych.eq_intercalate_of_splitToList_eq '/' hsplits
      rw [String.intercalate_cons_cons, String.intercalate_singleton] at hs
      refine ⟨o₁, o₂, o₃, o₄, some pre, ?_, h₁, h₂, h₃, h₄, hp, ?_⟩
      · simpa [renderNet, haddr, String.append_assoc] using hs
      · simpa [netValue, cidrValue, Fin.val_ofNat] using hnet.symm
    · simp at h
  · rintro ⟨o₁, o₂, o₃, o₄, pre, rfl, h₁, h₂, h₃, h₄, hp, rfl⟩
    unfold parseIPv4Net
    cases pre with
    | none =>
        have hsplit :
            (renderNet o₁ o₂ o₃ o₄ none).splitToList (· = '/') =
              [renderAddr o₁ o₂ o₃ o₄] := by
          simpa [renderNet] using
            (splitToListNoSep (renderAddr o₁ o₂ o₃ o₄)
              (fun x : Char => decide (x = '/')) (noSlashOfAddr h₁ h₂ h₃ h₄))
        rw [hsplit]
        triptych_sound
        refine ⟨addrValue o₁ o₂ o₃ o₄, ?_, ?_⟩
        · exact ⟨o₁, o₂, o₃, o₄, rfl, h₁, h₂, h₃, h₄, rfl⟩
        · simp [netValue, cidrValue]
    | some pre =>
        have hsplit :
            (renderNet o₁ o₂ o₃ o₄ (some pre)).splitToList (· = '/') =
              [renderAddr o₁ o₂ o₃ o₄, pre] := by
          simpa [renderNet, String.append_assoc] using
            (splitToListEq (renderAddr o₁ o₂ o₃ o₄) pre
              (fun x : Char => decide (x = '/')) '/' (by simp)
              (noSlashOfAddr h₁ h₂ h₃ h₄) (noSlashOfDigitsBetween hp.1))
        rw [hsplit]
        triptych_sound
        refine ⟨hp, _, rfl, addrValue o₁ o₂ o₃ o₄, ?_, ?_⟩
        · exact ⟨o₁, o₂, o₃, o₄, rfl, h₁, h₂, h₃, h₄, rfl⟩
        · simp [netValue, cidrValue, Fin.val_ofNat]

theorem parseIPv6Net_isV6 {s : String} {net : IPNet}
    (h : parseIPv6Net s = some net) :
    ∃ cidr, net = IPNet.V6 cidr := by
  unfold parseIPv6Net at h
  generalize hsplits : s.splitToList (· = '/') = parts at h
  rcases parts with _ | ⟨addr, rest⟩
  · simp at h
  rcases rest with _ | ⟨pre, rest⟩
  · triptych_sound at h
    obtain ⟨a, _, hnet⟩ := h
    exact ⟨_, hnet.symm⟩
  rcases rest with _ | ⟨extra, rest⟩
  · triptych_sound at h
    obtain ⟨_, parsedPrefix, hprefix, parsedAddr, _, hnet⟩ := h
    simp only [Option.pure_def, Option.some.injEq] at hprefix
    subst parsedPrefix
    exact ⟨_, hnet.symm⟩
  · simp at h

/-- Cedar's top-level parser returns an IPv4 payload exactly when its IPv4 branch does. -/
theorem ipv4Only_eq_some_iff_parseIPv4Net {s : String} {cidr : CIDR V4_WIDTH} :
    CedarExamples.IPv4.ipv4Only s = some cidr ↔
      parseIPv4Net s = some (.V4 cidr) := by
  unfold CedarExamples.IPv4.ipv4Only
  rw [ip_eq_parse]
  unfold CedarSupport.IPAddrInternals.parse
  cases h4 : parseIPv4Net s with
  | none =>
      simp only [Option.isSome_none, if_false, reduceCtorEq]
      cases h6 : parseIPv6Net s with
      | none => simp
      | some net =>
          obtain ⟨cidr6, rfl⟩ := parseIPv6Net_isV6 h6
          simp
  | some net =>
      obtain ⟨o₁, o₂, o₃, o₄, pre, _, _, _, _, _, _, hnet⟩ :=
        parseIPv4Net_eq_some_iff.mp h4
      subst net
      simp [netValue, cidrValue]

/-- Complete successful-result specification for Cedar's external IPv4 parser. -/
theorem ipv4Only_eq_some_iff {s : String} {cidr : CIDR V4_WIDTH} :
    CedarExamples.IPv4.ipv4Only s = some cidr ↔
      ∃ o₁ o₂ o₃ o₄ pre,
        s = renderNet o₁ o₂ o₃ o₄ pre ∧
        OctetValid o₁ ∧ OctetValid o₂ ∧ OctetValid o₃ ∧ OctetValid o₄ ∧
        OptionalPrefixValid pre ∧ cidr = cidrValue o₁ o₂ o₃ o₄ pre := by
  rw [ipv4Only_eq_some_iff_parseIPv4Net]
  constructor
  · intro h
    obtain ⟨o₁, o₂, o₃, o₄, pre, hs, h₁, h₂, h₃, h₄, hp, hnet⟩ :=
      parseIPv4Net_eq_some_iff.mp h
    exact ⟨o₁, o₂, o₃, o₄, pre, hs, h₁, h₂, h₃, h₄, hp,
      by simpa [netValue] using hnet⟩
  · rintro ⟨o₁, o₂, o₃, o₄, pre, hs, h₁, h₂, h₃, h₄, hp, hcidr⟩
    apply parseIPv4Net_eq_some_iff.mpr
    exact ⟨o₁, o₂, o₃, o₄, pre, hs, h₁, h₂, h₃, h₄, hp,
      by simpa [netValue] using congrArg IPNet.V4 hcidr⟩

theorem cidrValue_eq_toIPv4Net {o₁ o₂ o₃ o₄ : String} {pre : Option String}
    (hp : OptionalPrefixValid pre) :
    cidrValue o₁ o₂ o₃ o₄ pre =
      CedarExamples.IPv4.toIPv4Net o₁ o₂ o₃ o₄ (pre.getD "") := by
  cases pre with
  | none => rfl
  | some pre =>
      unfold OptionalPrefixValid PrefixValid at hp
      have hbound : readNat pre < 33 := by
        omega
      have hne : pre ≠ "" := by
        intro heq
        subst pre
        have hlen := hp.1.2.1
        simp at hlen
      unfold cidrValue CedarExamples.IPv4.toIPv4Net addrValue
      simp [hne, Fin.val_ofNat]
      change ((readNat pre % 33 : Nat) : IPv4Prefix) = (readNat pre : IPv4Prefix)
      rw [Nat.mod_eq_of_lt hbound]

end IPv4.RuleRegistryProof
