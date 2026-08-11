import Cedar.Spec.Ext.IPAddr

namespace CedarSupport.IPAddrInternals

open Cedar.Spec.Ext
open Cedar.Spec.Ext.IPAddr

def parsePrefixNat (str : String) (digits : Nat) (size : Nat) : Option (Fin (size + 1)) :=
  let nchars := str.length
  if 0 < nchars && nchars ≤ digits && (str.startsWith "0" → str = "0")
  then do
    let n ← toNat?' str
    if n ≤ size then .some (Fin.ofNat (size + 1) n) else .none
  else .none

def parseNumV4 (str : String) : Option (BitVec 8) :=
  let nchars := str.length
  if 0 < nchars && nchars ≤ 3 && (str.startsWith "0" → str = "0")
  then do
    let n ← toNat?' str
    if n ≤ 0xff then .some n else .none
  else .none

def parseSegsV4 (str : String) : Option IPv4Addr :=
  match str.splitToList (· = '.') with
  | [s₀, s₁, s₂, s₃] => do
    let a₀ ← parseNumV4 s₀
    let a₁ ← parseNumV4 s₁
    let a₂ ← parseNumV4 s₂
    let a₃ ← parseNumV4 s₃
    .some (IPv4Addr.mk a₀ a₁ a₂ a₃)
  | _ => .none

def parseIPv4Net (str : String) : Option IPNet :=
  match str.splitToList (· = '/') with
  | strV4 :: rest => do
    let pre ←
      match rest with
      | [] => .some (ADDR_SIZE V4_WIDTH)
      | [strPre] => parsePrefixNat strPre 2 (ADDR_SIZE V4_WIDTH)
      | _ => .none
    let v4 ← parseSegsV4 strV4
    .some (IPNet.V4 { addr := v4, pre := pre })
  | _ => .none

def isHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def toHexNat (c : Char) : Nat :=
  if c.isDigit
  then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f'
  then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F'
  then c.toNat - 'A'.toNat + 10
  else c.toNat

def parseNumV6 (str : String) : Option (BitVec 16) :=
  let nchars := str.length
  if 0 < nchars && nchars ≤ 4 && str.all isHexDigit
  then
    let n := str.foldl (fun n c => n * 16 + toHexNat c) 0
    if n ≤ 0xffff then .some n else .none
  else .none

def parseNumSegsV6 (str : String) : Option (List (BitVec 16)) :=
  if str.isEmpty
  then .some []
  else (str.splitToList (· = ':')).mapM parseNumV6

def parseSegsV6 (str : String) : Option IPv6Addr := do
  let segs ←
    match Cedar.Spec.Ext.IPAddr.splitDoubleColon str with
    | [s₁] => parseNumSegsV6 s₁
    | [s₁, s₂] => do
      let ns₁ ← parseNumSegsV6 s₁
      let ns₂ ← parseNumSegsV6 s₂
      let nsegs := ns₁.length + ns₂.length
      if nsegs < 8
      then .some (ns₁ ++ (List.replicate (8 - nsegs) 0) ++ ns₂)
      else .none
    | _ => .none
  match segs with
  | [a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇] =>
    .some (IPv6Addr.mk a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇)
  | _ => .none

def parseIPv6Net (str : String) : Option IPNet :=
  match str.splitToList (· = '/') with
  | strV6 :: rest => do
    let pre ←
      match rest with
      | [] => .some (ADDR_SIZE V6_WIDTH)
      | [strPre] => parsePrefixNat strPre 3 (ADDR_SIZE V6_WIDTH)
      | _ => .none
    let v6 ← parseSegsV6 strV6
    .some (IPNet.V6 { addr := v6, pre := pre })
  | _ => .none

def parse (str : String) : Option IPNet :=
  let v4 := parseIPv4Net str
  if v4.isSome then v4 else parseIPv6Net str

theorem ip_eq_parse (str : String) : Cedar.Spec.Ext.IPAddr.ip str = parse str := by
  rfl

end CedarSupport.IPAddrInternals
