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

import Triptych.Architecture.Classify

/-!
# Verus runtime grammar model

This module defines the complete generic grammar representation used when a format is outside the
specialized `ScanPlan` fragment.

`RuntimeGrammar` covers every symbol form handled by Triptych's Lean scanner:

* arbitrary literals and Lean-style quoted string literals;
* all token classes and length specifications;
* production references, alternatives, and optional items;
* separated repetition, including nested repetition items.

References and nested repetition items are resolved to numeric indices. The generated fallback
module contains this data plus a thin call to the verified complete scanner. Specialized formats
do not serialize this model at runtime.
-/

namespace Triptych.Backend.Verus

/-- One flattened runtime symbol. References point into `RuntimeGrammar.productions`; repetition
    items point into `RuntimeGrammar.symbols`. -/
inductive RuntimeSymbol where
  | literal (text : String)
  | stringLiteral
  | reference (production : Nat)
  | terminal (token : TokClass) (length : LenSpec)
  | repetition (separator : String) (item : Nat) (lower : Nat) (upper : Option Nat)
  deriving Repr, Inhabited, DecidableEq

/-- A symbol occurrence in a production sequence. -/
structure RuntimeItem where
  symbol : Nat
  optional : Bool
  deriving Repr, Inhabited, DecidableEq

/-- One source-ordered production alternative. -/
abbrev RuntimeAlternative := List RuntimeItem

/-- One named production after references have been resolved. -/
structure RuntimeProduction where
  name : String
  alternatives : List RuntimeAlternative
  deriving Repr, Inhabited, DecidableEq

/-- Complete input to the generic verified Rust scanner. -/
structure RuntimeGrammar where
  start : Nat
  symbols : List RuntimeSymbol
  productions : List RuntimeProduction
  deriving Repr, Inhabited, DecidableEq

/-- One source alternative after flattening its item list. The range points into
    `FlatGrammar.items`; no parser-control nodes are introduced. -/
structure FlatAlternative where
  firstItem : Nat
  itemCount : Nat
  deriving Repr, Inhabited, DecidableEq

/-- One source production after flattening its alternatives. The range points into
    `FlatGrammar.alternatives`. -/
structure FlatProduction where
  name : String
  firstAlternative : Nat
  alternativeCount : Nat
  deriving Repr, Inhabited, DecidableEq

/-- Source-faithful representation emitted to Verus. It retains the grammar's symbols, items,
    alternatives, and productions instead of introducing a bytecode or parser-control language. -/
structure FlatGrammar where
  start : Nat
  symbols : List RuntimeSymbol
  items : List RuntimeItem
  alternatives : List FlatAlternative
  productions : List FlatProduction
  deriving Repr, Inhabited, DecidableEq

private def duplicate? [BEq α] (values : List α) : Bool :=
  values.eraseDups.length != values.length

private def indexOf? (needle : String) : List String → Option Nat
  | [] => none
  | value :: rest =>
      if value == needle then some 0 else (indexOf? needle rest).map (· + 1)

private abbrev CompileM := StateT (List RuntimeSymbol) (Except String)

private def appendSymbol (symbol : RuntimeSymbol) : CompileM Nat := do
  let symbols ← get
  set (symbols ++ [symbol])
  pure symbols.length

private partial def compileSymbol (productionNames : List String) : Sym → CompileM Nat
  | .lit literal =>
      appendSymbol (.literal literal)
  | .str =>
      appendSymbol .stringLiteral
  | .ref name =>
      match indexOf? name productionNames with
      | some index => appendSymbol (.reference index)
      | none => throw s!"Verus runtime: unresolved production reference `{name}`"
  | .term token length =>
      appendSymbol (.terminal token length)
  | .rep separator item lower upper => do
      let itemIndex ← compileSymbol productionNames item
      appendSymbol (.repetition separator itemIndex lower upper)

private def compileItem (productionNames : List String) (item : SymItem) :
    CompileM RuntimeItem := do
  pure { symbol := ← compileSymbol productionNames item.sym, optional := item.optional }

private def compileAlternative (productionNames : List String) (alternative : Triptych.Seq) :
    CompileM RuntimeAlternative :=
  alternative.mapM (compileItem productionNames)

private def compileProduction (productionNames : List String) (production : Production) :
    CompileM RuntimeProduction := do
  pure
    { name := production.name
      alternatives := ← production.alts.mapM (compileAlternative productionNames) }

/-- The grammar-side acceptance condition for the generic verified Rust runtime. Unlike the
    current readable-spec translator, it does not require static uniqueness and does not exclude
    quoted strings or separated repetition. -/
def runtimeGrammarSupported (grammar : Grammar) : Bool :=
  let names := grammar.prods.map (·.name)
  !duplicate? names &&
    (indexOf? grammar.start names).isSome &&
    grammar.refsResolve &&
    grammar.cycle?.isNone &&
    grammar.repOk

/-- Resolve a Triptych grammar into the flattened representation consumed by the generic runtime.
    This is fail-closed and accepts the same grammar forms as the Lean scanner. -/
def compileRuntimeGrammar (grammar : Grammar) : Except String RuntimeGrammar := do
  let productionNames := grammar.prods.map (·.name)
  if duplicate? productionNames then
    throw "Verus runtime: production names must be unique"
  let start ← match indexOf? grammar.start productionNames with
    | some index => pure index
    | none => throw s!"Verus runtime: start production `{grammar.start}` is missing"
  if !grammar.refsResolve then
    throw "Verus runtime: every production reference must resolve"
  if let some cycle := grammar.cycle? then
    throw s!"Verus runtime: recursive grammars are unsupported: \
      {String.intercalate " -> " cycle}"
  if !grammar.repOk then
    throw "Verus runtime: separated repetition requires a nonempty separator and lower bound 1"
  let (productions, symbols) ←
    (grammar.prods.mapM (compileProduction productionNames)).run []
  pure { start, symbols, productions }

/-- Flatten only list storage; preserve the original grammar hierarchy and source order. -/
def RuntimeGrammar.flatten (grammar : RuntimeGrammar) : FlatGrammar := Id.run do
  let mut items : List RuntimeItem := []
  let mut alternatives : List FlatAlternative := []
  let mut productions : List FlatProduction := []
  for production in grammar.productions do
    let firstAlternative := alternatives.length
    for alternative in production.alternatives do
      let firstItem := items.length
      items := items ++ alternative
      alternatives := alternatives ++
        [{ firstItem, itemCount := alternative.length }]
    productions := productions ++
      [{ name := production.name
         firstAlternative
         alternativeCount := production.alternatives.length }]
  pure
    { start := grammar.start
      symbols := grammar.symbols
      items
      alternatives
      productions }

/-- Compile a Triptych grammar into the source-faithful representation intended for the direct
    Verus scanner. -/
def compileFlatGrammar (grammar : Grammar) : Except String FlatGrammar :=
  RuntimeGrammar.flatten <$> compileRuntimeGrammar grammar

end Triptych.Backend.Verus
