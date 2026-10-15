import Outputs.BitRows.parser

/-!
# Multiple dependent-field checks
-/

namespace BitRowsExample

#guard BitRows.parse "3:101/a0F" =
  some { width := 3, first := "101", second := "a0F" }
#guard BitRows.parse "0:/" =
  some { width := 0, first := "", second := "" }
#guard BitRows.parse "3:10/a0F" = none
#guard BitRows.parse "3:101/a0" = none
#guard BitRows.parse "3:10x/a0F" = none

example (first second width : String) :
    BitRows.WfConstraints first width second ↔
      first.length = rowWidth width ∧ second.length = rowWidth width :=
  Iff.rfl

example (input : String) :
    BitRows.parse input = none ↔ ¬BitRows.IsValid input :=
  BitRows.parse_reject input

end BitRowsExample
