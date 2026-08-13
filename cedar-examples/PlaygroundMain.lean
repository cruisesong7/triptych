import Outputs.Decimal.parser
import Outputs.Duration.parser
import Outputs.Datetime.parser
import Outputs.IPv4.parser
import Outputs.IPv6.parser

open Lean

namespace CedarExamples.Playground

structure Field where
  name : String
  text : String
  present : Bool := true
  deriving ToJson

structure Response where
  format : String
  input : String
  wellFormed : Bool
  semanticConstraints : Option Bool
  valid : Bool
  generatedResult : Option String
  cedarResult : Option String
  agree : Bool
  fields : Array Field
  deriving ToJson

def scalar (name text : String) : Field :=
  { name, text }

def optional (name : String) : Option String → Field
  | some text => { name, text }
  | none => { name, text := "", present := false }

def repeated (name : String) (items : List String) : Field :=
  { name, text := String.intercalate ", " items, present := !items.isEmpty }

def decimalFields (s : String) : Array Field :=
  match CedarExamples.Decimal.Decimal.decodeView s with
  | none => #[]
  | some view =>
      #[scalar "Sign" view.sign, scalar "Natural" view.natural, scalar "Fraction" view.fraction]

def durationFields (s : String) : Array Field :=
  match CedarExamples.Duration.Duration.decodeView s with
  | none => #[]
  | some view =>
      #[scalar "Sign" view.sign,
        optional "Days" view.dDays,
        optional "Hours" view.dHours,
        optional "Minutes" view.dMinutes,
        optional "Seconds" view.dSeconds,
        optional "Millis" view.dMillis]

def datetimeFields (s : String) : Array Field :=
  match CedarExamples.Datetime.Datetime.decodeView s with
  | none => #[]
  | some view =>
      #[scalar "YYYY" view.yyyy,
        scalar "MM" view.mm,
        scalar "DD" view.dd,
        optional "Time.hh" view.time_hh,
        optional "Time.mm" view.time_mm,
        optional "Seconds" view.ss,
        optional "Millis" view.sss,
        optional "Offset.hh" view.offset_hh,
        optional "Offset.mm" view.offset_mm,
        optional "Offset" view.offset]

def ipv4Fields (s : String) : Array Field :=
  match CedarExamples.IPv4.IPv4.decodeView s with
  | none => #[]
  | some view =>
      #[scalar "Oct1" view.oct1,
        scalar "Oct2" view.oct2,
        scalar "Oct3" view.oct3,
        scalar "Oct4" view.oct4,
        optional "Prefix" view.prefix]

def ipv6Fields (s : String) : Array Field :=
  match CedarExamples.IPv6.IPv6.decodeView s with
  | none => #[]
  | some view =>
      #[repeated "Full groups" view.h16All,
        repeated "Left groups" view.h16lAll,
        repeated "Right groups" view.h16rAll,
        optional "Prefix" view.prefix]

def decimalResponse (s : String) : Response :=
  let generated := (CedarExamples.Decimal.Decimal.parse s).map toString
  let cedar := (CedarExamples.Decimal.Decimal.checkedExtParse s).map toString
  {
    format := "Decimal"
    input := s
    wellFormed := decide (CedarExamples.Decimal.Decimal.IsWf s)
    semanticConstraints := some (decide (CedarExamples.Decimal.Decimal.SatisfiesConstraints s))
    valid := decide (CedarExamples.Decimal.Decimal.IsValid s)
    generatedResult := generated
    cedarResult := cedar
    agree := generated == cedar
    fields := decimalFields s
  }

def durationResponse (s : String) : Response :=
  let generated := (CedarExamples.Duration.Duration.parse s).map toString
  let cedar := (CedarExamples.Duration.Duration.checkedExtParse s).map toString
  {
    format := "Duration"
    input := s
    wellFormed := decide (CedarExamples.Duration.Duration.IsWf s)
    semanticConstraints := some (decide (CedarExamples.Duration.Duration.SatisfiesConstraints s))
    valid := decide (CedarExamples.Duration.Duration.IsValid s)
    generatedResult := generated
    cedarResult := cedar
    agree := generated == cedar
    fields := durationFields s
  }

def datetimeResponse (s : String) : Response :=
  let generated := (CedarExamples.Datetime.Datetime.parse s).map toString
  let cedar :=
    (CedarExamples.Datetime.Datetime.checkedExtParse s).map fun datetime =>
      toString datetime.val.toInt
  {
    format := "Datetime"
    input := s
    wellFormed := decide (CedarExamples.Datetime.Datetime.IsWf s)
    semanticConstraints := none
    valid := decide (CedarExamples.Datetime.Datetime.IsValid s)
    generatedResult := generated
    cedarResult := cedar
    agree := generated == cedar
    fields := datetimeFields s
  }

def ipv4Response (s : String) : Response :=
  let generated :=
    (CedarExamples.IPv4.IPv4.parse s).map CedarExamples.IPv4.ipNetToStr
  let cedar :=
    (CedarExamples.IPv4.IPv4.checkedExtParse s).map CedarExamples.IPv4.ipNetToStr
  {
    format := "IPv4"
    input := s
    wellFormed := decide (CedarExamples.IPv4.IPv4.IsWf s)
    semanticConstraints := none
    valid := decide (CedarExamples.IPv4.IPv4.IsValid s)
    generatedResult := generated
    cedarResult := cedar
    agree := generated == cedar
    fields := ipv4Fields s
  }

def ipv6Response (s : String) : Response :=
  let generated :=
    (CedarExamples.IPv6.IPv6.parse s).map CedarExamples.IPv6.ipNetToStr
  let cedar :=
    (CedarExamples.IPv6.IPv6.checkedExtParse s).map CedarExamples.IPv6.ipNetToStr
  {
    format := "IPv6"
    input := s
    wellFormed := decide (CedarExamples.IPv6.IPv6.IsWf s)
    semanticConstraints := none
    valid := decide (CedarExamples.IPv6.IPv6.IsValid s)
    generatedResult := generated
    cedarResult := cedar
    agree := generated == cedar
    fields := ipv6Fields s
  }

def parse (format input : String) : Except String Response :=
  match format.toLower with
  | "decimal" => .ok (decimalResponse input)
  | "duration" => .ok (durationResponse input)
  | "datetime" => .ok (datetimeResponse input)
  | "ipv4" => .ok (ipv4Response input)
  | "ipv6" => .ok (ipv6Response input)
  | _ => .error s!"Unknown format '{format}'"

def errorJson (message : String) : Json :=
  Json.mkObj [("error", message)]

def run (args : List String) : IO UInt32 := do
  match args with
  | format :: inputParts =>
      let input := String.intercalate " " inputParts
      match parse format input with
      | .ok response =>
          IO.println (toJson response).compress
          return 0
      | .error message =>
          IO.eprintln (errorJson message).compress
          return 2
  | _ =>
      IO.eprintln (errorJson "Usage: playground <format> <input>").compress
      return 2

end CedarExamples.Playground

def main (args : List String) := CedarExamples.Playground.run args
