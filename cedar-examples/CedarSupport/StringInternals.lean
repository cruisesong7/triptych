module

public import Cedar.Thm.Data.String
public import Cedar.Spec.Ext.IPAddr
public import Triptych.Theorems.String

import all Cedar.Thm.Data.String
import all Cedar.Spec.Ext.IPAddr
import all Batteries.Data.String.Lemmas

/-! Modern-module wrappers for Cedar's private string lemmas. -/

namespace CedarSupport.StringInternals

private theorem extractGo₂Append (a tail : List Char) (i : String.Pos.Raw) :
    String.Pos.Raw.extract.go₂ (a ++ tail) i
      ((String.ofList a).rawEndPos.offsetBy i) = a := by
  induction a generalizing i with
  | nil =>
      rw [List.nil_append]
      cases tail with
      | nil => rfl
      | cons c cs =>
          change
            (if i = i then [] else c :: String.Pos.Raw.extract.go₂ cs (i + c) i) = []
          simp
  | cons c cs ih =>
      rw [List.cons_append]
      have hne : i ≠ (String.ofList (c :: cs)).rawEndPos.offsetBy i := by
        intro h
        have h' := congrArg String.Pos.Raw.byteIdx h
        simp only [String.Pos.Raw.byteIdx_offsetBy, String.byteIdx_rawEndPos,
          String.utf8ByteSize_ofList, String.utf8Len_cons] at h'
        have hc := Char.utf8Size_pos c
        omega
      change
        (if i = (String.ofList (c :: cs)).rawEndPos.offsetBy i then []
         else c :: String.Pos.Raw.extract.go₂ (cs ++ tail) (i + c)
           ((String.ofList (c :: cs)).rawEndPos.offsetBy i)) = c :: cs
      rw [if_neg hne]
      have hend :
          (String.ofList (c :: cs)).rawEndPos.offsetBy i =
            (String.ofList cs).rawEndPos.offsetBy (i + c) := by
        apply String.Pos.Raw.ext
        simp only [String.Pos.Raw.byteIdx_offsetBy, String.byteIdx_rawEndPos,
          String.utf8ByteSize_ofList, String.utf8Len_cons,
          String.Pos.Raw.byteIdx_add_char]
        omega
      rw [hend, ih]

private theorem extractGo₁Append (a b tail : List Char) (i : String.Pos.Raw) :
    String.Pos.Raw.extract.go₁ (a ++ b ++ tail) i
      ((String.ofList a).rawEndPos.offsetBy i)
      ((String.ofList (a ++ b)).rawEndPos.offsetBy i) = b := by
  induction a generalizing i with
  | nil =>
      rw [List.nil_append]
      cases b with
      | nil =>
          cases tail with
          | nil => rfl
          | cons c cs =>
              change
                (if i = i then String.Pos.Raw.extract.go₂ (c :: cs) i i
                 else String.Pos.Raw.extract.go₁ cs (i + c) i i) = []
              rw [if_pos rfl]
              change (if i = i then [] else c :: _) = []
              simp
      | cons c cs =>
          change
            (if i = i then String.Pos.Raw.extract.go₂ ((c :: cs) ++ tail) i
              ((String.ofList (c :: cs)).rawEndPos.offsetBy i)
             else _) = c :: cs
          rw [if_pos rfl]
          exact extractGo₂Append (c :: cs) tail i
  | cons c cs ih =>
      rw [List.cons_append]
      have hne : i ≠ (String.ofList (c :: cs)).rawEndPos.offsetBy i := by
        intro h
        have h' := congrArg String.Pos.Raw.byteIdx h
        simp only [String.Pos.Raw.byteIdx_offsetBy, String.byteIdx_rawEndPos,
          String.utf8ByteSize_ofList, String.utf8Len_cons] at h'
        have hc := Char.utf8Size_pos c
        omega
      change
        (if i = (String.ofList (c :: cs)).rawEndPos.offsetBy i then _
         else String.Pos.Raw.extract.go₁ (cs ++ b ++ tail) (i + c)
           ((String.ofList (c :: cs)).rawEndPos.offsetBy i)
           ((String.ofList ((c :: cs) ++ b)).rawEndPos.offsetBy i)) = b
      rw [if_neg hne]
      have hb :
          (String.ofList (c :: cs)).rawEndPos.offsetBy i =
            (String.ofList cs).rawEndPos.offsetBy (i + c) := by
        apply String.Pos.Raw.ext
        simp only [String.Pos.Raw.byteIdx_offsetBy, String.byteIdx_rawEndPos,
          String.utf8ByteSize_ofList, String.utf8Len_cons,
          String.Pos.Raw.byteIdx_add_char]
        omega
      have he :
          (String.ofList ((c :: cs) ++ b)).rawEndPos.offsetBy i =
            (String.ofList (cs ++ b)).rawEndPos.offsetBy (i + c) := by
        apply String.Pos.Raw.ext
        simp only [String.Pos.Raw.byteIdx_offsetBy, String.byteIdx_rawEndPos,
          String.utf8ByteSize_ofList, String.utf8Len_cons,
          String.Pos.Raw.byteIdx_add_char, String.utf8Len_append]
        omega
      rw [hb, he, ih]

private theorem rawExtractAppend (a b c : String) :
    String.Pos.Raw.extract (a ++ b ++ c) a.rawEndPos (a ++ b).rawEndPos = b := by
  rw [show a = String.ofList a.toList by simp,
    show b = String.ofList b.toList by simp,
    show c = String.ofList c.toList by simp]
  simp only [← String.ofList_append, String.Pos.Raw.extract, String.toList_ofList]
  split <;> rename_i h
  · have hb : String.utf8Len b.toList = 0 := by
      simp only [String.byteIdx_rawEndPos, String.utf8ByteSize_ofList,
        String.utf8Len_append] at h
      omega
    cases hbList : b.toList with
    | nil => simp
    | cons c cs =>
        have hc := Char.utf8Size_pos c
        simp only [hbList, String.utf8Len_cons] at hb
        omega
  · congr 1
    simpa only [String.Pos.Raw.offsetBy_zero] using
      extractGo₁Append a.toList b.toList c.toList 0

private theorem utf8GetAuxAppend (a rest : List Char) (c : Char) (i : String.Pos.Raw) :
    String.Pos.Raw.utf8GetAux (a ++ c :: rest) i
      ((String.ofList a).rawEndPos.offsetBy i) = c := by
  induction a generalizing i with
  | nil =>
      change (if i = i then c else _) = c
      simp
  | cons x xs ih =>
      rw [List.cons_append]
      have hne : i ≠ (String.ofList (x :: xs)).rawEndPos.offsetBy i := by
        intro h
        have h' := congrArg String.Pos.Raw.byteIdx h
        simp only [String.Pos.Raw.byteIdx_offsetBy, String.byteIdx_rawEndPos,
          String.utf8ByteSize_ofList, String.utf8Len_cons] at h'
        have hx := Char.utf8Size_pos x
        omega
      change
        (if i = (String.ofList (x :: xs)).rawEndPos.offsetBy i then x
         else String.Pos.Raw.utf8GetAux (xs ++ c :: rest) (i + x)
           ((String.ofList (x :: xs)).rawEndPos.offsetBy i)) = c
      rw [if_neg hne]
      have hp :
          (String.ofList (x :: xs)).rawEndPos.offsetBy i =
            (String.ofList xs).rawEndPos.offsetBy (i + x) := by
        apply String.Pos.Raw.ext
        simp only [String.Pos.Raw.byteIdx_offsetBy, String.byteIdx_rawEndPos,
          String.utf8ByteSize_ofList, String.utf8Len_cons,
          String.Pos.Raw.byteIdx_add_char]
        omega
      rw [hp, ih]

private theorem rawGetAppend (a : String) (c : Char) (rest : List Char) :
    String.Pos.Raw.get (a ++ String.ofList (c :: rest)) a.rawEndPos = c := by
  rw [show a = String.ofList a.toList by simp]
  simp only [← String.ofList_append, String.Pos.Raw.get, String.toList_ofList]
  simpa using utf8GetAuxAppend a.toList rest c 0

private theorem rawNextAppend (a : String) (c : Char) (rest : List Char) :
    String.Pos.Raw.next (a ++ String.ofList (c :: rest)) a.rawEndPos =
      (a ++ String.singleton c).rawEndPos := by
  unfold String.Pos.Raw.next
  rw [rawGetAppend]
  apply String.Pos.Raw.ext
  simp only [String.Pos.Raw.byteIdx_add_char, String.byteIdx_rawEndPos,
    String.utf8ByteSize_append, String.utf8ByteSize_singleton]

private theorem rawAtEndAppend (a : String) (rest : List Char) :
    String.Pos.Raw.atEnd (a ++ String.ofList rest) a.rawEndPos = rest.isEmpty := by
  cases rest with
  | nil => simp [String.Pos.Raw.atEnd]
  | cons c cs =>
      simp only [String.Pos.Raw.atEnd, String.byteIdx_rawEndPos,
        String.utf8ByteSize_append, String.utf8ByteSize_ofList,
        String.utf8Len_cons, List.isEmpty_cons, decide_eq_false_iff_not]
      have hc := Char.utf8Size_pos c
      omega

private theorem stringEqOfListConsOfNe {s : String} (h : s ≠ "") :
    ∃ c cs, s = String.ofList (c :: cs) := by
  cases hs : s.toList with
  | nil =>
      exfalso
      apply h
      apply String.toList_inj.mp
      simpa using hs
  | cons c cs =>
      exact ⟨c, cs, by
        apply String.toList_inj.mp
        simpa using hs⟩

private theorem intercalateAppendSingleton (sep x : String) (xs : List String) :
    String.intercalate sep (xs ++ [x]) =
      match xs with
      | [] => x
      | _ => String.intercalate sep xs ++ sep ++ x := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
      cases ys with
      | nil =>
          simp only [List.nil_append, List.cons_append]
          rw [String.intercalate_cons_cons, String.intercalate_singleton,
            String.intercalate_singleton]
      | cons z zs =>
          simp only [List.cons_append]
          rw [String.intercalate_cons_cons, String.intercalate_cons_cons]
          have ih' :
              String.intercalate sep (z :: (zs ++ [x])) =
                String.intercalate sep (z :: zs) ++ sep ++ x := by
            simpa only [List.cons_append] using ih
          rw [ih']
          simp only [String.append_assoc]

private theorem intercalateAppendSingletonOfNe (sep x : String) (xs : List String)
    (h : xs ≠ []) :
    String.intercalate sep (xs ++ [x]) =
      String.intercalate sep xs ++ sep ++ x := by
  cases xs with
  | nil => contradiction
  | cons y ys => simpa using intercalateAppendSingleton sep x (y :: ys)

private def accumulated (sep : String) : List String → String
  | [] => ""
  | part :: r => accumulated sep r ++ part ++ sep

private theorem intercalateReverseCons (sep part : String) (r : List String) :
    String.intercalate sep (part :: r).reverse = accumulated sep r ++ part := by
  induction r generalizing part with
  | nil => simp [accumulated]
  | cons x xs ih =>
      rw [List.reverse_cons]
      rw [List.reverse_cons]
      rw [intercalateAppendSingletonOfNe sep part (xs.reverse ++ [x]) (by simp)]
      simp only [accumulated]
      have hx := ih x
      rw [List.reverse_cons] at hx
      rw [hx]

private theorem rawEndUnoffset (a b : String) :
    (a ++ b).rawEndPos.unoffsetBy b.rawEndPos = a.rawEndPos := by
  apply String.Pos.Raw.ext
  simp only [String.Pos.Raw.byteIdx_unoffsetBy, String.byteIdx_rawEndPos,
    String.utf8ByteSize_append]
  omega

private def SplitOnState (s sep : String) (b i j : String.Pos.Raw)
    (r : List String) : Prop :=
  ∃ current matched rest sepRest,
    s = accumulated sep r ++ current ++ matched ++ rest ∧
    sep = matched ++ sepRest ∧
    b = (accumulated sep r).rawEndPos ∧
    i = (accumulated sep r ++ current ++ matched).rawEndPos ∧
    j = matched.rawEndPos ∧
    sepRest ≠ ""

private theorem splitOnAuxIntercalate (s sep : String)
    (b i j : String.Pos.Raw) (r : List String) :
    SplitOnState s sep b i j r →
      String.intercalate sep (String.splitOnAux s sep b i j r) = s := by
  refine String.splitOnAux.induct s sep
    (motive := fun b i j r =>
      SplitOnState s sep b i j r →
        String.intercalate sep (String.splitOnAux s sep b i j r) = s)
    ?_ ?_ ?_ ?_ b i j r
  · intro b i j r hend hstate
    obtain ⟨current, matched, rest, sepRest, hs, hsep, hb, hi, hj, hsepRest⟩ :=
      hstate
    subst b
    subst i
    subst j
    subst s
    have hrestList : rest.toList.isEmpty = true := by
      rw [← rawAtEndAppend (accumulated sep r ++ current ++ matched) rest.toList]
      simpa only [String.ofList_toList, String.append_assoc] using hend
    have hrest : rest = "" := by
      apply String.toList_inj.mp
      simpa using List.isEmpty_iff.mp hrestList
    subst rest
    rw [String.splitOnAux.eq_1, if_pos hend]
    rw [intercalateReverseCons]
    have hextract :
        String.Pos.Raw.extract (accumulated sep r ++ current ++ matched ++ "")
          (accumulated sep r).rawEndPos
          (accumulated sep r ++ current ++ matched).rawEndPos =
            current ++ matched := by
      simpa only [String.append_assoc] using
        rawExtractAppend (accumulated sep r) (current ++ matched) ""
    rw [hextract]
    simp only [String.append_assoc, String.append_empty]
  · intro b i j r hnotEnd hget iNext jNext hendSep ih hstate
    rw [String.splitOnAux.eq_1, if_neg hnotEnd, if_pos hget, if_pos hendSep]
    obtain ⟨current, matched, rest, sepRest, hs, hsep, hb, hi, hj, hsepRest⟩ :=
      hstate
    change String.Pos.Raw.atEnd sep (String.Pos.Raw.next sep j) = true at hendSep
    change
      (SplitOnState s sep (String.Pos.Raw.next s i) (String.Pos.Raw.next s i) 0
          (String.Pos.Raw.extract s b
            ((String.Pos.Raw.next s i).unoffsetBy (String.Pos.Raw.next sep j)) :: r) →
        String.intercalate sep
            (String.splitOnAux s sep (String.Pos.Raw.next s i)
              (String.Pos.Raw.next s i) 0
              (String.Pos.Raw.extract s b
                ((String.Pos.Raw.next s i).unoffsetBy (String.Pos.Raw.next sep j)) :: r)) =
          s) at ih
    rw [hs, hi] at hnotEnd
    rw [hs, hi, hj] at hget
    rw [hj] at hendSep
    rw [hs, hb, hi, hj] at ih
    have hrest : rest ≠ "" := by
      intro h
      subst rest
      apply hnotEnd
      simpa only [String.toList_empty, String.ofList_nil, String.append_empty,
        List.isEmpty_nil] using
        rawAtEndAppend (accumulated sep r ++ current ++ matched) []
    obtain ⟨c, restChars, rfl⟩ := stringEqOfListConsOfNe hrest
    obtain ⟨d, sepChars, rfl⟩ := stringEqOfListConsOfNe hsepRest
    have hcd : c = d := by
      have hget' := hget
      rw [rawGetAppend (accumulated sep r ++ current ++ matched) c restChars] at hget'
      rw [hsep, rawGetAppend matched d sepChars] at hget'
      exact beq_iff_eq.mp hget'
    subst d
    have hsepChars : sepChars = [] := by
      apply List.isEmpty_iff.mp
      rw [← rawAtEndAppend (matched ++ String.singleton c) sepChars]
      have hendSep' := hendSep
      rw [hsep, rawNextAppend matched c sepChars] at hendSep'
      simpa only [String.ofList_cons, String.ofList_nil, String.append_empty,
        String.append_assoc] using hendSep'
    subst sepChars
    have hsep' : sep = matched ++ String.singleton c := by
      simpa only [String.ofList_cons, String.ofList_nil, String.append_empty] using hsep
    have hiNext :
        String.Pos.Raw.next
            (accumulated sep r ++ current ++ matched ++ String.ofList (c :: restChars))
            (accumulated sep r ++ current ++ matched).rawEndPos =
          (accumulated sep r ++ current ++ matched ++ String.singleton c).rawEndPos := by
      exact rawNextAppend (accumulated sep r ++ current ++ matched) c restChars
    have hjNext :
        String.Pos.Raw.next sep matched.rawEndPos = sep.rawEndPos := by
      rw [hsep', String.singleton_eq_ofList]
      exact rawNextAppend matched c []
    have hjoined :
        accumulated sep r ++ current ++ matched ++ String.singleton c =
          (accumulated sep r ++ current) ++ sep := by
      rw [hsep']
      simp only [String.append_assoc]
    have hstart :
        ((accumulated sep r ++ current ++ matched ++ String.singleton c).rawEndPos
          ).unoffsetBy sep.rawEndPos =
            (accumulated sep r ++ current).rawEndPos := by
      rw [hjoined]
      exact rawEndUnoffset (accumulated sep r ++ current) sep
    have hinput :
        accumulated sep r ++ current ++ matched ++ String.ofList (c :: restChars) =
          accumulated sep r ++ current ++ sep ++ String.ofList restChars := by
      rw [hsep']
      simp only [String.ofList_cons, String.append_assoc]
    have hextract :
        String.Pos.Raw.extract
            (accumulated sep r ++ current ++ matched ++ String.ofList (c :: restChars))
            (accumulated sep r).rawEndPos
            ((String.Pos.Raw.next
                (accumulated sep r ++ current ++ matched ++ String.ofList (c :: restChars))
                (accumulated sep r ++ current ++ matched).rawEndPos).unoffsetBy
              (String.Pos.Raw.next sep matched.rawEndPos)) =
          current := by
      rw [hiNext, hjNext, hstart]
      rw [hinput]
      simpa only [String.append_assoc] using
        rawExtractAppend (accumulated sep r) current
          (sep ++ String.ofList restChars)
    have hnext :
        String.Pos.Raw.next
            (accumulated sep r ++ current ++ matched ++ String.ofList (c :: restChars))
            (accumulated sep r ++ current ++ matched).rawEndPos =
          (accumulated sep (current :: r)).rawEndPos := by
      rw [hiNext, hjoined]
      rfl
    rw [hextract] at ih
    rw [hs, hb, hi, hj, hextract]
    apply ih
    refine ⟨"", "", String.ofList restChars, sep, ?_, by simp, ?_, ?_, by simp, ?_⟩
    · simpa only [accumulated, String.append_empty] using hinput
    · simpa only [String.append_empty] using hnext
    · simpa only [String.append_empty] using hnext
    · intro h
      rw [hsep'] at h
      have hlen := congrArg String.length h
      simp at hlen
  · intro b i j r hnotEnd hget iNext jNext hnotEndSep ih hstate
    rw [String.splitOnAux.eq_1, if_neg hnotEnd, if_pos hget, if_neg hnotEndSep]
    obtain ⟨current, matched, rest, sepRest, hs, hsep, hb, hi, hj, hsepRest⟩ :=
      hstate
    change
      ¬String.Pos.Raw.atEnd sep (String.Pos.Raw.next sep j) = true at hnotEndSep
    change
      (SplitOnState s sep b (String.Pos.Raw.next s i) (String.Pos.Raw.next sep j) r →
        String.intercalate sep
            (String.splitOnAux s sep b (String.Pos.Raw.next s i)
              (String.Pos.Raw.next sep j) r) =
          s) at ih
    rw [hs, hi] at hnotEnd
    rw [hs, hi, hj] at hget
    rw [hj] at hnotEndSep
    rw [hs, hb, hi, hj] at ih
    have hrest : rest ≠ "" := by
      intro h
      subst rest
      apply hnotEnd
      simpa only [String.toList_empty, String.ofList_nil, String.append_empty,
        List.isEmpty_nil] using
        rawAtEndAppend (accumulated sep r ++ current ++ matched) []
    obtain ⟨c, restChars, rfl⟩ := stringEqOfListConsOfNe hrest
    obtain ⟨d, sepChars, rfl⟩ := stringEqOfListConsOfNe hsepRest
    have hcd : c = d := by
      have hget' := hget
      rw [rawGetAppend (accumulated sep r ++ current ++ matched) c restChars] at hget'
      rw [hsep, rawGetAppend matched d sepChars] at hget'
      exact beq_iff_eq.mp hget'
    subst d
    have hsepChars : String.ofList sepChars ≠ "" := by
      intro h
      have hchars : sepChars = [] := by
        have := congrArg String.toList h
        simpa using this
      subst sepChars
      apply hnotEndSep
      rw [hsep, rawNextAppend matched c []]
      simpa only [String.ofList_cons, String.ofList_nil, String.append_empty,
        List.isEmpty_nil] using
        rawAtEndAppend (matched ++ String.singleton c) []
    have hinput :
        accumulated sep r ++ current ++ matched ++ String.ofList (c :: restChars) =
          accumulated sep r ++ current ++ (matched ++ String.singleton c) ++
            String.ofList restChars := by
      simp only [String.ofList_cons, String.append_assoc]
    have hseparator :
        sep = (matched ++ String.singleton c) ++ String.ofList sepChars := by
      simpa only [String.ofList_cons, String.append_assoc] using hsep
    have hiNext :
        String.Pos.Raw.next
            (accumulated sep r ++ current ++ matched ++ String.ofList (c :: restChars))
            (accumulated sep r ++ current ++ matched).rawEndPos =
          (accumulated sep r ++ current ++ (matched ++ String.singleton c)).rawEndPos := by
      simpa only [String.append_assoc] using
        rawNextAppend (accumulated sep r ++ current ++ matched) c restChars
    have hjNext :
        String.Pos.Raw.next sep matched.rawEndPos =
          (matched ++ String.singleton c).rawEndPos := by
      rw [hsep]
      exact rawNextAppend matched c sepChars
    rw [hs, hb, hi, hj]
    apply ih
    exact ⟨current, matched ++ String.singleton c, String.ofList restChars,
      String.ofList sepChars, hinput, hseparator, rfl, hiNext, hjNext, hsepChars⟩
  · intro b i j r hnotEnd hget ih hstate
    rw [String.splitOnAux.eq_1, if_neg hnotEnd, if_neg hget]
    obtain ⟨current, matched, rest, sepRest, hs, hsep, hb, hi, hj, hsepRest⟩ :=
      hstate
    change
      (SplitOnState s sep b (String.Pos.Raw.next s (i.unoffsetBy j)) 0 r →
        String.intercalate sep
            (String.splitOnAux s sep b (String.Pos.Raw.next s (i.unoffsetBy j)) 0 r) =
          s) at ih
    rw [hs, hi] at hnotEnd
    rw [hs, hb, hi, hj] at ih
    have hrest : rest ≠ "" := by
      intro h
      subst rest
      apply hnotEnd
      simpa only [String.toList_empty, String.ofList_nil, String.append_empty,
        List.isEmpty_nil] using
        rawAtEndAppend (accumulated sep r ++ current ++ matched) []
    have hsuffix : matched ++ rest ≠ "" := by
      intro h
      have hlen := congrArg String.length h
      have hrestLen : 0 < rest.length := by
        by_contra hzero
        apply hrest
        exact String.length_eq_zero_iff.mp (by omega)
      simp only [String.length_append, String.length_empty] at hlen
      omega
    obtain ⟨c, suffixChars, hsuffixEq⟩ := stringEqOfListConsOfNe hsuffix
    have hstart :
        (accumulated sep r ++ current ++ matched).rawEndPos.unoffsetBy
            matched.rawEndPos =
          (accumulated sep r ++ current).rawEndPos := by
      exact rawEndUnoffset (accumulated sep r ++ current) matched
    have hinput :
        accumulated sep r ++ current ++ matched ++ rest =
          accumulated sep r ++ (current ++ String.singleton c) ++
            String.ofList suffixChars := by
      rw [show accumulated sep r ++ current ++ matched ++ rest =
          accumulated sep r ++ current ++ (matched ++ rest) by
        simp only [String.append_assoc]]
      rw [hsuffixEq]
      simp only [String.ofList_cons, String.append_assoc]
    have hnext :
        String.Pos.Raw.next
            (accumulated sep r ++ current ++ matched ++ rest)
            ((accumulated sep r ++ current ++ matched).rawEndPos.unoffsetBy
              matched.rawEndPos) =
          (accumulated sep r ++ (current ++ String.singleton c)).rawEndPos := by
      rw [hstart, hinput]
      have hshape :
          accumulated sep r ++ (current ++ String.singleton c) ++
              String.ofList suffixChars =
            (accumulated sep r ++ current) ++ String.ofList (c :: suffixChars) := by
        simp only [String.ofList_cons, String.append_assoc]
      rw [hshape]
      simpa only [String.append_assoc] using
        rawNextAppend (accumulated sep r ++ current) c suffixChars
    have hsepNe : sep ≠ "" := by
      intro h
      have hlen := congrArg String.length hsep
      rw [h] at hlen
      simp only [String.length_empty, String.length_append] at hlen
      apply hsepRest
      exact String.length_eq_zero_iff.mp (by omega)
    rw [hs, hb, hi, hj]
    apply ih
    exact ⟨current ++ String.singleton c, "", String.ofList suffixChars, sep,
      by simpa only [String.append_empty] using hinput, by simp, rfl,
      by simpa only [String.append_empty] using hnext, by simp, hsepNe⟩

/-- A proof-oriented reference implementation of splitting a character list on `"::"`. -/
public def legacySplitDoubleColonAux : List Char → List Char → List String
  | current, ':' :: ':' :: rest =>
      String.ofList current :: legacySplitDoubleColonAux [] rest
  | current, c :: rest =>
      legacySplitDoubleColonAux (current ++ [c]) rest
  | current, [] =>
      [String.ofList current]

/-- A colon-free prefix can be accumulated without changing subsequent `"::"` matches. -/
public theorem splitDoubleColonAux_consume_noColon
    (current chars rest : List Char)
    (h : ∀ c ∈ chars, c ≠ ':') :
    legacySplitDoubleColonAux current (chars ++ rest) =
      legacySplitDoubleColonAux (current ++ chars) rest := by
  induction chars generalizing current with
  | nil => simp
  | cons c cs ih =>
      have hc : c ≠ ':' := h c (by simp)
      have hnonmatch :
          ∀ suffix, c = ':' → cs ++ rest = ':' :: suffix → False := by
        intro suffix heq _
        exact hc heq
      rw [List.cons_append,
        legacySplitDoubleColonAux.eq_2 current c (cs ++ rest) hnonmatch]
      simpa only [List.append_assoc, List.singleton_append] using
        ih (current ++ [c]) (fun d hd => h d (by simp [hd]))

private theorem splitOnAuxDoubleColon (pre : String) (current remaining : List Char)
    (r : List String) :
    String.splitOnAux (pre ++ String.ofList (current ++ remaining)) "::"
        pre.rawEndPos (pre ++ String.ofList current).rawEndPos 0 r =
      r.reverse ++ legacySplitDoubleColonAux current remaining := by
  induction current, remaining using legacySplitDoubleColonAux.induct generalizing pre r with
  | case1 current rest ih =>
      have hs₁ :
          pre ++ String.ofList (current ++ ':' :: ':' :: rest) =
            (pre ++ String.ofList current) ++ String.ofList (':' :: ':' :: rest) := by
        simp only [← String.ofList_append, String.append_assoc]
      have hs₂ :
          pre ++ String.ofList (current ++ ':' :: ':' :: rest) =
            (pre ++ String.ofList (current ++ [':'])) ++ String.ofList (':' :: rest) := by
        simp only [← String.ofList_append, String.append_assoc, List.append_assoc,
          List.cons_append, List.nil_append]
      have hsTail :
          pre ++ String.ofList (current ++ ':' :: ':' :: rest) =
            ((pre ++ String.ofList current) ++ "::") ++ String.ofList rest := by
        change
          pre ++ String.ofList (current ++ ':' :: ':' :: rest) =
            ((pre ++ String.ofList current) ++ String.ofList [':', ':']) ++
              String.ofList rest
        simp only [← String.ofList_append, String.append_assoc, List.append_assoc,
          List.cons_append, List.nil_append]
      have hend₁ :
          ¬String.Pos.Raw.atEnd (pre ++ String.ofList (current ++ ':' :: ':' :: rest))
              (pre ++ String.ofList current).rawEndPos = true := by
        rw [hs₁, rawAtEndAppend]
        simp
      have hget₁ :
          (String.Pos.Raw.get (pre ++ String.ofList (current ++ ':' :: ':' :: rest))
                (pre ++ String.ofList current).rawEndPos ==
              String.Pos.Raw.get "::" 0) = true := by
        rw [hs₁, rawGetAppend]
        change (':' == ':') = true
        simp
      have hi₁ :
          String.Pos.Raw.next (pre ++ String.ofList (current ++ ':' :: ':' :: rest))
              (pre ++ String.ofList current).rawEndPos =
            (pre ++ String.ofList (current ++ [':'])).rawEndPos := by
        rw [hs₁, rawNextAppend]
        apply String.Pos.Raw.ext
        simp [String.byteIdx_rawEndPos, String.utf8ByteSize_append,
          String.utf8ByteSize_ofList]
        omega
      have hj₁ :
          String.Pos.Raw.next "::" 0 = (String.singleton ':').rawEndPos := by
        simpa using rawNextAppend "" ':' [':']
      have hsepNotEnd :
          ¬String.Pos.Raw.atEnd "::" (String.Pos.Raw.next "::" 0) = true := by
        rw [hj₁, show "::" = String.singleton ':' ++ String.ofList [':'] by rfl,
          rawAtEndAppend]
        simp
      rw [String.splitOnAux.eq_1, if_neg hend₁, if_pos hget₁, if_neg hsepNotEnd,
        hi₁, hj₁]
      have hend₂ :
          ¬String.Pos.Raw.atEnd (pre ++ String.ofList (current ++ ':' :: ':' :: rest))
              (pre ++ String.ofList (current ++ [':'])).rawEndPos = true := by
        rw [hs₂, rawAtEndAppend]
        simp
      have hget₂ :
          (String.Pos.Raw.get (pre ++ String.ofList (current ++ ':' :: ':' :: rest))
                (pre ++ String.ofList (current ++ [':'])).rawEndPos ==
              String.Pos.Raw.get "::" (String.singleton ':').rawEndPos) = true := by
        rw [hs₂, rawGetAppend,
          show "::" = String.singleton ':' ++ String.ofList (':' :: []) by rfl,
          rawGetAppend]
        simp
      have hi₂ :
          String.Pos.Raw.next (pre ++ String.ofList (current ++ ':' :: ':' :: rest))
              (pre ++ String.ofList (current ++ [':'])).rawEndPos =
            ((pre ++ String.ofList current) ++ "::").rawEndPos := by
        rw [hs₂, rawNextAppend]
        congr 1
        change
          (pre ++ String.ofList (current ++ [':'])) ++ String.ofList [':'] =
            (pre ++ String.ofList current) ++ String.ofList [':', ':']
        simp only [← String.ofList_append, String.append_assoc, List.append_assoc,
          List.cons_append, List.nil_append]
      have hj₂ :
          String.Pos.Raw.next "::" (String.singleton ':').rawEndPos =
            "::".rawEndPos := by
        simpa using rawNextAppend (String.singleton ':') ':' []
      have hsepEnd : String.Pos.Raw.atEnd "::" "::".rawEndPos = true := by
        simp [String.Pos.Raw.atEnd]
      have hstart :
          ((pre ++ String.ofList current) ++ "::").rawEndPos.unoffsetBy "::".rawEndPos =
            (pre ++ String.ofList current).rawEndPos :=
        rawEndUnoffset (pre ++ String.ofList current) "::"
      have hextract :
          String.Pos.Raw.extract (pre ++ String.ofList (current ++ ':' :: ':' :: rest))
              pre.rawEndPos (pre ++ String.ofList current).rawEndPos =
            String.ofList current := by
        rw [hs₁]
        simpa using
          rawExtractAppend pre (String.ofList current) (String.ofList (':' :: ':' :: rest))
      rw [String.splitOnAux.eq_1, if_neg hend₂, if_pos hget₂, hi₂, hj₂,
        if_pos hsepEnd, hstart, hextract]
      rw [hsTail]
      have hrec :=
        ih ((pre ++ String.ofList current) ++ "::") (String.ofList current :: r)
      simp only [List.nil_append, String.ofList_nil, String.append_empty] at hrec
      rw [hrec]
      simp [legacySplitDoubleColonAux, List.reverse_cons, List.append_assoc]
  | case2 current c rest hnomatch ih =>
      by_cases hc : c = ':'
      · subst c
        cases rest with
        | nil =>
            have hinput :
                pre ++ String.ofList (current ++ [':']) =
                  (pre ++ String.ofList current) ++ String.ofList (':' :: []) := by
              simp [String.append_assoc]
            have hend :
                ¬String.Pos.Raw.atEnd (pre ++ String.ofList (current ++ [':']))
                    (pre ++ String.ofList current).rawEndPos = true := by
              rw [hinput, rawAtEndAppend]
              simp
            have hget :
                (String.Pos.Raw.get (pre ++ String.ofList (current ++ [':']))
                      (pre ++ String.ofList current).rawEndPos ==
                    String.Pos.Raw.get "::" 0) = true := by
              rw [hinput, rawGetAppend]
              change (':' == ':') = true
              simp
            have hiNext :
                String.Pos.Raw.next (pre ++ String.ofList (current ++ [':']))
                    (pre ++ String.ofList current).rawEndPos =
                  (pre ++ String.ofList (current ++ [':'])).rawEndPos := by
              rw [hinput, rawNextAppend]
              apply String.Pos.Raw.ext
              simp [String.byteIdx_rawEndPos, String.utf8ByteSize_append,
                String.utf8ByteSize_ofList]
            have hjNext :
                String.Pos.Raw.next "::" 0 = (String.singleton ':').rawEndPos := by
              simpa using rawNextAppend "" ':' [':']
            have hsepNotEnd :
                ¬String.Pos.Raw.atEnd "::" (String.Pos.Raw.next "::" 0) = true := by
              rw [hjNext,
                show "::" = String.singleton ':' ++ String.ofList [':'] by rfl,
                rawAtEndAppend]
              simp
            rw [String.splitOnAux.eq_1, if_neg hend, if_pos hget,
              if_neg hsepNotEnd, hiNext]
            have hfinalEnd :
                String.Pos.Raw.atEnd (pre ++ String.ofList (current ++ [':']))
                    (pre ++ String.ofList (current ++ [':'])).rawEndPos = true := by
              simp [String.Pos.Raw.atEnd]
            rw [String.splitOnAux.eq_1, if_pos hfinalEnd]
            have hextract :
                String.Pos.Raw.extract (pre ++ String.ofList (current ++ [':']))
                    pre.rawEndPos
                    (pre ++ String.ofList (current ++ [':'])).rawEndPos =
                  String.ofList (current ++ [':']) := by
              simpa using rawExtractAppend pre (String.ofList (current ++ [':'])) ""
            rw [hextract, List.reverse_cons]
            simp [legacySplitDoubleColonAux]
        | cons d tail =>
            by_cases hd : d = ':'
            · subst d
              exact (hnomatch tail rfl rfl).elim
            · have hs₁ :
                  pre ++ String.ofList (current ++ ':' :: d :: tail) =
                    (pre ++ String.ofList current) ++ String.ofList (':' :: d :: tail) := by
                simp only [← String.ofList_append, String.append_assoc]
              have hs₂ :
                  pre ++ String.ofList (current ++ ':' :: d :: tail) =
                    (pre ++ String.ofList (current ++ [':'])) ++
                      String.ofList (d :: tail) := by
                simp only [← String.ofList_append, String.append_assoc, List.append_assoc,
                  List.cons_append, List.nil_append]
              have hend₁ :
                  ¬String.Pos.Raw.atEnd (pre ++ String.ofList (current ++ ':' :: d :: tail))
                      (pre ++ String.ofList current).rawEndPos = true := by
                rw [hs₁, rawAtEndAppend]
                simp
              have hget₁ :
                  (String.Pos.Raw.get (pre ++ String.ofList (current ++ ':' :: d :: tail))
                        (pre ++ String.ofList current).rawEndPos ==
                      String.Pos.Raw.get "::" 0) = true := by
                rw [hs₁, rawGetAppend]
                change (':' == ':') = true
                simp
              have hi₁ :
                  String.Pos.Raw.next (pre ++ String.ofList (current ++ ':' :: d :: tail))
                      (pre ++ String.ofList current).rawEndPos =
                    (pre ++ String.ofList (current ++ [':'])).rawEndPos := by
                rw [hs₁, rawNextAppend]
                apply String.Pos.Raw.ext
                simp [String.byteIdx_rawEndPos, String.utf8ByteSize_append,
                  String.utf8ByteSize_ofList]
                omega
              have hj₁ :
                  String.Pos.Raw.next "::" 0 = (String.singleton ':').rawEndPos := by
                simpa using rawNextAppend "" ':' [':']
              have hsepNotEnd :
                  ¬String.Pos.Raw.atEnd "::" (String.Pos.Raw.next "::" 0) = true := by
                rw [hj₁, show "::" = String.singleton ':' ++ String.ofList [':'] by rfl,
                  rawAtEndAppend]
                simp
              rw [String.splitOnAux.eq_1, if_neg hend₁, if_pos hget₁,
                if_neg hsepNotEnd, hi₁, hj₁]
              have hend₂ :
                  ¬String.Pos.Raw.atEnd (pre ++ String.ofList (current ++ ':' :: d :: tail))
                      (pre ++ String.ofList (current ++ [':'])).rawEndPos = true := by
                rw [hs₂, rawAtEndAppend]
                simp
              have hget₂ :
                  ¬(String.Pos.Raw.get
                        (pre ++ String.ofList (current ++ ':' :: d :: tail))
                        (pre ++ String.ofList (current ++ [':'])).rawEndPos ==
                      String.Pos.Raw.get "::" (String.singleton ':').rawEndPos) = true := by
                rw [hs₂, rawGetAppend,
                  show "::" = String.singleton ':' ++ String.ofList (':' :: []) by rfl,
                  rawGetAppend]
                change ¬(d == ':') = true
                simpa using hd
              have hafter :
                  pre ++ String.ofList (current ++ [':']) =
                    (pre ++ String.ofList current) ++ String.singleton ':' := by
                simp only [String.singleton_eq_ofList, ← String.ofList_append,
                  String.append_assoc]
              have hstart :
                  (pre ++ String.ofList (current ++ [':'])).rawEndPos.unoffsetBy
                        (String.singleton ':').rawEndPos =
                    (pre ++ String.ofList current).rawEndPos := by
                rw [hafter, rawEndUnoffset]
              rw [String.splitOnAux.eq_1, if_neg hend₂, if_neg hget₂, hstart, hi₁]
              simpa [legacySplitDoubleColonAux, hd, List.append_assoc] using ih pre r
      · have hinput :
            pre ++ String.ofList (current ++ c :: rest) =
              (pre ++ String.ofList current) ++ String.ofList (c :: rest) := by
          simp only [← String.ofList_append, String.append_assoc]
        have hend :
            ¬String.Pos.Raw.atEnd (pre ++ String.ofList (current ++ c :: rest))
                (pre ++ String.ofList current).rawEndPos = true := by
          rw [hinput, rawAtEndAppend]
          simp
        have hget :
            ¬(String.Pos.Raw.get (pre ++ String.ofList (current ++ c :: rest))
                (pre ++ String.ofList current).rawEndPos ==
              String.Pos.Raw.get "::" 0) = true := by
          rw [hinput, rawGetAppend]
          change ¬(c == ':') = true
          simpa using hc
        have hnext :
            String.Pos.Raw.next (pre ++ String.ofList (current ++ c :: rest))
                (pre ++ String.ofList current).rawEndPos =
              (pre ++ String.ofList (current ++ [c])).rawEndPos := by
          rw [hinput, rawNextAppend]
          apply String.Pos.Raw.ext
          simp [String.byteIdx_rawEndPos, String.utf8ByteSize_append,
            String.utf8ByteSize_ofList]
          omega
        rw [String.splitOnAux.eq_1, if_neg hend, if_neg hget,
          String.Pos.Raw.unoffsetBy_zero, hnext]
        simpa [legacySplitDoubleColonAux, hc, List.append_assoc] using ih pre r
  | case3 current =>
      have hend :
          String.Pos.Raw.atEnd (pre ++ String.ofList (current ++ []))
              (pre ++ String.ofList current).rawEndPos = true := by
        simp [String.Pos.Raw.atEnd]
      rw [String.splitOnAux.eq_1, if_pos hend]
      have hextract :
          String.Pos.Raw.extract (pre ++ String.ofList (current ++ []))
              pre.rawEndPos (pre ++ String.ofList current).rawEndPos =
            String.ofList current := by
        simpa using rawExtractAppend pre (String.ofList current) ""
      rw [hextract, List.reverse_cons]
      simp [legacySplitDoubleColonAux]

/-- Legacy `String.splitOn "::"` agrees with the simple list reference implementation. -/
public theorem splitOnDoubleColon_eq (s : String) :
    s.splitOn "::" = legacySplitDoubleColonAux [] s.toList := by
  simpa [String.splitOn] using splitOnAuxDoubleColon "" [] s.toList []

/-- The proof-oriented reference splitter agrees with Cedar's public implementation. -/
public theorem splitDoubleColonAux_eq_cedar (current remaining : List Char) :
    legacySplitDoubleColonAux current remaining =
      Cedar.Spec.Ext.IPAddr.splitDoubleColonAux current remaining := by
  induction current, remaining using legacySplitDoubleColonAux.induct with
  | case1 current rest ih =>
      rw [legacySplitDoubleColonAux.eq_1,
        Cedar.Spec.Ext.IPAddr.splitDoubleColonAux.eq_1, ih]
  | case2 current c rest hnomatch ih =>
      rw [legacySplitDoubleColonAux.eq_2 current c rest hnomatch,
        Cedar.Spec.Ext.IPAddr.splitDoubleColonAux.eq_2 current c rest hnomatch, ih]
  | case3 current =>
      rw [legacySplitDoubleColonAux.eq_3, Cedar.Spec.Ext.IPAddr.splitDoubleColonAux.eq_3]

/-- Legacy `String.splitOn "::"` agrees with Cedar's public splitter. -/
public theorem splitOnDoubleColon_eq_cedar (s : String) :
    s.splitOn "::" = Cedar.Spec.Ext.IPAddr.splitDoubleColon s := by
  rw [splitOnDoubleColon_eq]
  exact splitDoubleColonAux_eq_cedar [] s.toList

/-- Legacy `String.splitOn` is reconstructed by intercalating its nonempty separator. -/
public theorem intercalateSplitOn (s sep : String) (hsep : sep ≠ "") :
    String.intercalate sep (s.splitOn sep) = s := by
  unfold String.splitOn
  simp only [beq_iff_eq, hsep, if_false]
  apply splitOnAuxIntercalate
  exact ⟨"", "", s, sep, by simp [accumulated], by simp, by simp [accumulated],
    by simp [accumulated], by simp, hsep⟩

/-- An observed legacy split determines the original string. -/
public theorem eqIntercalateOfSplitOnEq {s sep : String} {parts : List String}
    (hsep : sep ≠ "") (h : s.splitOn sep = parts) :
    s = String.intercalate sep parts := by
  rw [← h]
  exact (intercalateSplitOn s sep hsep).symm

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
