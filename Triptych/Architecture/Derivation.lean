import Triptych.Architecture.Decode

/-!
# Structural derivation helpers

Pure operations shared by generated derivation trees and their proof layer.
-/

namespace Triptych

/-- Captures added around the inner captures of a referenced production. -/
def referenceCaptures (qual name text : String) : CaptureMap :=
  if qual.isEmpty then
    [(name, text)]
  else
    [(name, text), (qual ++ "." ++ name, text)]

/-- Render an optional derivation. -/
def renderOptional (render : α → String) : Option α → String
  | none => ""
  | some x => render x

/-- Captures contributed by an optional derivation. -/
def capturesOptional (captures : α → CaptureMap) : Option α → CaptureMap
  | none => []
  | some x => captures x

/-- Validity of an optional derivation. -/
def OptionalValid (valid : α → Prop) : Option α → Prop
  | none => True
  | some x => valid x

instance {α : Type u} (valid : α → Prop) [DecidablePred valid] (entry : Option α) :
    Decidable (OptionalValid valid entry) := by
  cases entry <;> simp only [OptionalValid] <;> infer_instance

/-- Render a separated repetition. -/
def renderSeparated (sep : String) (render : α → String) (values : List α) : String :=
  String.intercalate sep (values.map render)

/-- Exact captures of a separated repetition, including its count capture. -/
def capturesSeparated (base : String) (captures : α → CaptureMap)
    (values : List α) : CaptureMap :=
  (base ++ "#count", toString values.length) :: values.flatMap captures

/-- Structural validity of a separated repetition. The nonempty clause reflects the decoder's
    `item (sep item)*` shape; generated grammars additionally guarantee `1 ≤ lo`. -/
def RepetitionValid (lo : Nat) (hi : Option Nat) (valid : α → Prop)
    (values : List α) : Prop :=
  values ≠ [] ∧
    lo ≤ values.length ∧
    (∀ upper, hi = some upper → values.length ≤ upper) ∧
    ∀ x ∈ values, valid x

instance {α : Type u} (valid : α → Prop) [DecidablePred valid]
    (lo : Nat) (hi : Option Nat) (values : List α) :
    Decidable (RepetitionValid lo hi valid values) := by
  unfold RepetitionValid
  infer_instance

end Triptych
