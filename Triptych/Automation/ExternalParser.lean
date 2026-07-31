/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Lean.Elab.Tactic
import Triptych.Automation.Registry

/-!
# Static external-parser proof automation

This module supplies the backend-neutral successful-path rules. The rules turn a hypothesis such
as `parser s = some a` into the witnesses, branch facts, and guards that made the result possible.
Parser-library backends extend the same `triptych_parser` registry with rules for their primitives.

`triptych_sound [parser, helper] at h` unfolds the named definitions and applies exactly the
registered rules to `h`. Unsupported parser operations remain visible in the resulting hypothesis,
which makes the next missing backend rule explicit.
-/

namespace Triptych.Automation

/-- Successful inversion of a conditional returning an optional value. -/
@[triptych_parser]
theorem ite_option_eq_some_iff {α : Type} (p : Prop) [Decidable p]
    (thenBranch elseBranch : Option α) (a : α) :
    (if p then thenBranch else elseBranch) = some a ↔
      (p ∧ thenBranch = some a) ∨ (¬p ∧ elseBranch = some a) := by
  by_cases hp : p <;> simp [hp]

attribute [triptych_parser]
  Option.bind_eq_bind
  Option.bind_eq_some_iff
  Option.map_eq_map
  Option.map_eq_some_iff
  Option.filter_eq_some_iff
  Option.guard_eq_some_iff
  Option.orElse_eq_orElse
  Option.orElse_eq_or
  Option.or_eq_some_iff
  Option.isSome_iff_exists
  Option.some.injEq
  Bool.and_eq_true
  Bool.or_eq_true
  Bool.not_eq_true
  decide_eq_true_eq
  reduceCtorEq
  false_and
  and_false
  false_or
  or_false
  true_and
  and_true
  and_assoc
  exists_and_left
  exists_eq_left
  exists_eq_left'
  exists_eq_right
  exists_eq_right'

end Triptych.Automation

open Lean Parser Tactic

/--
Invert the successful path of an `Option`-valued parser using rules registered with
`@[triptych_parser]`. Definitions named in brackets are unfolded before the registered rules run.
-/
syntax (name := triptychSound)
  "triptych_sound" (" [" simpLemma,* "]")? (location)? : tactic

macro_rules
  | `(tactic| triptych_sound) =>
      `(tactic| simp only [triptych_parser])
  | `(tactic| triptych_sound $loc) =>
      `(tactic| simp only [triptych_parser] $loc)
  | `(tactic| triptych_sound [$rules,*]) =>
      `(tactic| simp only [$rules,*, triptych_parser])
  | `(tactic| triptych_sound [$rules,*] $loc) =>
      `(tactic| simp only [$rules,*, triptych_parser] $loc)
