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

import Triptych.Automation.ExternalParser

/-!
# External-parser registry tests

This module models a parser backend that imports Triptych, proves one rule for its own primitive,
and registers it. The final theorem checks that `triptych_sound` composes that downstream rule with
the backend-neutral `Option` rules.
-/

namespace Triptych.Automation.Tests

private def guardedIncrement (source : Option Nat) : Option Nat := do
  let n ← source
  if n < 10 then some (n + 1) else none

private theorem guardedIncrement_success {source : Option Nat} {result : Nat}
    (h : guardedIncrement source = some result) :
    ∃ n, source = some n ∧ n < 10 ∧ n + 1 = result := by
  triptych_sound [guardedIncrement] at h
  exact h

private def leftBiased (x y : Option Nat) : Option Nat :=
  x <|> y

private theorem leftBiased_success {x y : Option Nat} {result : Nat}
    (h : leftBiased x y = some result) :
    x = some result ∨ (x = none ∧ y = some result) := by
  triptych_sound [leftBiased] at h
  exact h

private def filteredMap (source : Option Nat) : Option Nat :=
  (source.filter fun n => n < 10).map (· + 1)

private theorem filteredMap_success {source : Option Nat} {result : Nat}
    (h : filteredMap source = some result) :
    ∃ n, source = some n ∧ n < 10 ∧ n + 1 = result := by
  triptych_sound [filteredMap] at h
  exact h

private def guarded (n : Nat) : Option Nat :=
  Option.guard (fun n => n < 10) n

private theorem guarded_success {n result : Nat} (h : guarded n = some result) :
    n = result ∧ n < 10 := by
  triptych_sound [guarded] at h
  exact h

private def positive (n : Nat) : Option Nat :=
  if 0 < n then some n else none

@[triptych_parser]
private theorem positive_eq_some_iff (n result : Nat) :
    positive n = some result ↔ 0 < n ∧ n = result := by
  unfold positive
  by_cases h : 0 < n <;> simp [h]

private def backendParser (source : Option Nat) : Option Nat := do
  let n ← source
  let n ← positive n
  some (n + 1)

private theorem backendParser_success {source : Option Nat} {result : Nat}
    (h : backendParser source = some result) :
    ∃ n, source = some n ∧ 0 < n ∧ n + 1 = result := by
  triptych_sound [backendParser] at h
  exact h

private structure EncodeView where
  source : String
  denotation : Nat

private def encodePrinter (n : Nat) : String := toString n

private def encodeParser (s : String) : Option Nat :=
  s.toNat?

private def encodeValid (_ : EncodeView) : Prop :=
  True

private def encodeDecodeView (s : String) : Option EncodeView :=
  (encodeParser s).map fun n => ⟨s, n⟩

private theorem encodePrinter_roundtrip (n : Nat) :
    encodeParser (encodePrinter n) = some n := by
  simp [encodeParser, encodePrinter]

private theorem encodeParser_agrees (s : String) (n : Nat) :
    encodeParser s = some n ↔
      (encodeParser s).isSome ∧ encodeParser s = some n := by
  constructor
  · intro h
    simp [h]
  · exact And.right

private theorem encodeAccepted_view (s : String) :
    (encodeParser s).isSome ↔
      ∃ view, encodeDecodeView s = some view ∧ encodeValid view := by
  unfold encodeDecodeView encodeValid
  cases encodeParser s <;> simp

private theorem encodeValue_view (s : String) :
    encodeParser s = (encodeDecodeView s).map EncodeView.denotation := by
  unfold encodeDecodeView
  cases encodeParser s <;> rfl

private theorem triptychEncode_identity (n : Nat) :
    ∃ view,
      encodeDecodeView (encodePrinter n) = some view ∧
      encodeValid view ∧
      view.denotation = n := by
  triptych_encode [encodePrinter_roundtrip, encodeParser_agrees, encodeAccepted_view,
    encodeValue_view]

private theorem encodePrinter_accepted (n : Nat) :
    (encodeParser (encodePrinter n)).isSome := by
  simp [encodePrinter_roundtrip]

-- ANCHOR: triptychEncodeDirectUse
private theorem triptychEncodeDirect_identity (n : Nat) :
    ∃ view,
      encodeDecodeView (encodePrinter n) = some view ∧
      encodeValid view ∧
      view.denotation = n := by
  triptych_encode_direct [encodePrinter_accepted n, encodePrinter_roundtrip n,
    encodeAccepted_view, encodeValue_view]
-- ANCHOR_END: triptychEncodeDirectUse

private structure EncodeTree where
  result : Nat

private def EncodeTree.render (tree : EncodeTree) : String :=
  encodePrinter tree.result

private def EncodeTree.Valid (_ : EncodeTree) : Prop :=
  True

private def EncodeTree.toView (tree : EncodeTree) : EncodeView :=
  ⟨tree.render, tree.result⟩

private theorem EncodeTree.decodeView_render (tree : EncodeTree)
    (_ : tree.Valid) :
    encodeDecodeView tree.render = some tree.toView := by
  simp [encodeDecodeView, encodeParser, EncodeTree.render, encodePrinter, EncodeTree.toView]

private theorem encodeDerivation :
    EncodeDerivationStmt EncodeTree.render EncodeTree.Valid EncodeTree.toView
      encodeValid EncodeView.denotation encodePrinter := by
  intro n
  exact ⟨⟨n⟩, True.intro, rfl, True.intro, rfl⟩

private def encodeToDerivation (n : Nat) : EncodeTree :=
  ⟨n⟩

private def encodeDerivationPrinter :
    DerivationPrinter EncodeTree.render EncodeTree.Valid EncodeTree.toView
      encodeValid EncodeView.denotation where
  toDerivation := encodeToDerivation
  structural _ := True.intro
  valid _ := True.intro
  rightInverse _ := rfl

private theorem encodeDerivationFromToDerivation :
    EncodeDerivationStmt EncodeTree.render EncodeTree.Valid EncodeTree.toView
      encodeValid EncodeView.denotation
      encodeDerivationPrinter.toString :=
  encodeDerivationPrinter.encodeDerivation

-- ANCHOR: triptychEncodeDerivationUse
private theorem triptychEncodeDerivation_identity (n : Nat) :
    ∃ view,
      encodeDecodeView (encodePrinter n) = some view ∧
      encodeValid view ∧
      view.denotation = n := by
  triptych_encode_derivation [EncodeTree.decodeView_render, encodeDerivation]
-- ANCHOR_END: triptychEncodeDerivationUse

private def encodeOfSpec (n : Nat) : Nat := n

private def encodeToSpec (n : Nat) : Nat := n

private theorem encodeConversion {n : Nat} :
    encodeOfSpec (encodeToSpec n) = n := by
  rfl

private theorem encodeParser_agrees_converted (s : String) (n : Nat) :
    encodeParser s = some n ↔
      (encodeParser s).isSome ∧ encodeParser s = some (encodeToSpec n) := by
  simpa [encodeToSpec] using encodeParser_agrees s n

private theorem triptychEncode_converted (n : Nat) :
    ∃ view,
      encodeDecodeView (encodePrinter n) = some view ∧
      encodeValid view ∧
      encodeOfSpec view.denotation = n := by
  triptych_encode [encodePrinter_roundtrip, encodeParser_agrees_converted,
    encodeAccepted_view, encodeValue_view, encodeConversion]

private theorem triptychEncodeDirect_converted (n : Nat) :
    ∃ view,
      encodeDecodeView (encodePrinter n) = some view ∧
      encodeValid view ∧
      encodeOfSpec view.denotation = n := by
  triptych_encode_direct [encodePrinter_accepted n,
    show encodeParser (encodePrinter n) = some (encodeToSpec n) by
      simpa [encodeToSpec] using encodePrinter_roundtrip n,
    encodeAccepted_view, encodeValue_view, encodeConversion]

end Triptych.Automation.Tests
