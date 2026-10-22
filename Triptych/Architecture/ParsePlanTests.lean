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

import Triptych.Theorems.ParsePlan
import Triptych.Theorems.SearchMachine

namespace Triptych.ParsePlanTests

private def item (symbol : Sym) (optional := false) : SymItem :=
  { sym := symbol, optional }

private def decimalGrammar : Grammar :=
  { start := "Decimal"
    prods :=
      [ { name := "Decimal"
          alts := [[item (.ref "Sign"), item (.ref "Natural"), item (.lit "."),
            item (.ref "Fraction")]] },
        { name := "Sign", alts := [[item (.lit "-") true]] },
        { name := "Natural", alts := [[item (.term .digit .atLeastOne)]] },
        { name := "Fraction", alts := [[item (.term .digit (.between 1 4))]] } ] }

private def ambiguousGrammar : Grammar :=
  { start := "Root"
    prods :=
      [ { name := "Root", alts := [[item (.ref "Left"), item (.ref "Right")]] },
        { name := "Left", alts := [[item (.term .digit .atLeastOne)]] },
        { name := "Right", alts := [[item (.term .digit .atLeastOne)]] } ] }

private def repetitionGrammar : Grammar :=
  { start := "Root"
    prods :=
      [ { name := "Root"
          alts := [[item (.rep "," (.ref "Item") 1 (some 3))]] },
        { name := "Item", alts := [[item (.term .digit (.exactly 1))]] } ] }

private def sharedPrefixGrammar : Grammar :=
  { start := "Root"
    prods :=
      [ { name := "Root"
          alts :=
            [[item (.ref "Prefix"), item (.lit "x")],
             [item (.ref "Prefix"), item (.lit "y")]] },
        { name := "Prefix", alts := [[item (.term .digit (.exactly 2))]] } ] }

private def sharedTokenPrefixGrammar : Grammar :=
  { start := "Root"
    prods :=
      [{ name := "Root"
         alts :=
           [[item (.term .digit (.exactly 2)), item (.lit "x")],
            [item (.term .digit (.exactly 2)), item (.lit "y")]] }] }

private def recursiveGrammar : Grammar :=
  { start := "Root"
    prods :=
      [{ name := "Root", alts := [[item (.ref "Root")]] }] }

private def administrativeFailureArms : SearchCode → Nat
  | .accept | .fail => 0
  | .literal _ next | .stringLiteral next | .tokenRun _ _ next =>
      administrativeFailureArms next
  | .capture _ body next =>
      administrativeFailureArms body + administrativeFailureArms next
  | .choice first .fail =>
      administrativeFailureArms first + 1
  | .choice first second =>
      administrativeFailureArms first + administrativeFailureArms second
  | .repetition _ item _ _ _ next =>
      administrativeFailureArms item + administrativeFailureArms next

private def captureCount (key : String) : SearchCode → Nat
  | .accept | .fail => 0
  | .literal _ next | .stringLiteral next | .tokenRun _ _ next =>
      captureCount key next
  | .capture keys body next =>
      (if keys.contains key then 1 else 0) +
        captureCount key body + captureCount key next
  | .choice first second =>
      captureCount key first + captureCount key second
  | .repetition _ item _ _ _ next =>
      captureCount key item + captureCount key next

private def tokenRunCount : SearchCode → Nat
  | .accept | .fail => 0
  | .literal _ next | .stringLiteral next =>
      tokenRunCount next
  | .tokenRun _ _ next =>
      1 + tokenRunCount next
  | .capture _ body next | .repetition _ body _ _ _ next =>
      tokenRunCount body + tokenRunCount next
  | .choice first second =>
      tokenRunCount first + tokenRunCount second

private def machineTokenRunCount : SearchMachineCode → Nat
  | .accept | .fail => 0
  | .literal _ next | .stringLiteral next | .save next | .capture _ next =>
      machineTokenRunCount next
  | .tokenRun _ _ next | .greedyTokenRun _ _ next =>
      1 + machineTokenRunCount next
  | .choice first second =>
      machineTokenRunCount first + machineTokenRunCount second
  | .repetition _ item _ _ _ next =>
      machineTokenRunCount item + machineTokenRunCount next

#guard (compileParsePlan decimalGrammar).usesCursor
#guard !(compileParsePlan ambiguousGrammar).usesCursor
#guard (compileParsePlan ambiguousGrammar).usesSearch
#guard !(compileParsePlan recursiveGrammar).usesSearch

#guard
  match compileParsePlan ambiguousGrammar with
  | .search _ => true
  | .scanner _ => false
  | .cursor _ => false

#guard
  match compileParsePlan recursiveGrammar with
  | .scanner reason => reason.contains "recursive grammars are unsupported"
  | .search _ => false
  | .cursor _ => false

private def samples :=
  ["-12.34", "12.3", "0.0000", "-0.1", "", "-", "12", "12.", "12.34567", "x.1"]

#guard
  samples.all fun source =>
    (compileParsePlan decimalGrammar).decode decimalGrammar source ==
      scan decimalGrammar source

#guard
  ["12", "1234", "", "x"].all fun source =>
    (compileParsePlan ambiguousGrammar).decode ambiguousGrammar source ==
      scan ambiguousGrammar source

#guard
  match compileSearchPlan ambiguousGrammar with
  | .error _ => false
  | .ok searchPlan =>
      let program := lowerSearchPlan searchPlan
      ["12", "1234", "", "x"].all fun source =>
        program.decode source == searchPlan.decode source

#guard
  match compileSearchPlan ambiguousGrammar with
  | .error _ => false
  | .ok searchPlan =>
      let raw := lowerSearchPlanRaw searchPlan
      let reduced := lowerSearchPlan searchPlan
      administrativeFailureArms raw.code > 0 &&
        administrativeFailureArms reduced.code == 0

#guard
  match compileSearchPlan sharedPrefixGrammar with
  | .error _ => false
  | .ok searchPlan =>
      let raw := lowerSearchPlanRaw searchPlan
      let reduced := lowerSearchPlan searchPlan
      captureCount "Prefix" raw.code == 2 &&
        captureCount "Prefix" reduced.code == 1 &&
        ["12x", "12y", "1x", "12z"].all fun source =>
          reduced.decode source == raw.decode source

#guard
  match compileSearchPlan sharedTokenPrefixGrammar with
  | .error _ => false
  | .ok searchPlan =>
      let raw := lowerSearchPlanRaw searchPlan
      let reduced := lowerSearchPlan searchPlan
      let machine := lowerSearchProgram reduced
      tokenRunCount raw.code == 2 &&
        tokenRunCount reduced.code == 1 &&
        reduced.code.nodeCount < raw.code.nodeCount &&
        machineTokenRunCount machine.code == 1 &&
        ["12x", "12y", "1x", "12z"].all fun source =>
          machine.decode source == raw.decode source

#guard
  match compileSearchPlan ambiguousGrammar with
  | .error _ => false
  | .ok searchPlan =>
      let program := lowerSearchPlan searchPlan
      let machine := lowerSearchProgram program
      ["12", "1234", "", "x"].all fun source =>
        machine.decode source == program.decode source

#guard
  match compileSearchPlan repetitionGrammar with
  | .error _ => false
  | .ok searchPlan =>
      let program := lowerSearchPlan searchPlan
      let machine := lowerSearchProgram program
      ["1", "1,2", "1,2,3", "", "1,", "1,2,3,4", "a"].all fun source =>
        machine.decode source == program.decode source

example (source : String) :
    (compileParsePlan decimalGrammar).decode decimalGrammar source =
      scan decimalGrammar source :=
  ParsePlan.compile_decode_eq_scan decimalGrammar source

example (searchPlan : SearchPlan) (source : String) :
    (lowerSearchPlan searchPlan).decode source = searchPlan.decode source :=
  SearchProgram.lowerSearchPlan_decode searchPlan source

example (code : SearchCode) :
    code.reduce.nodeCount ≤ code.nodeCount :=
  SearchCode.nodeCount_reduce_le code

example (program : SearchProgram) (source : String) :
    (lowerSearchProgram program).decode source = program.decode source :=
  SearchMachine.lowerSearchProgram_decode program source

example : ParsePlan.CertifiedFor decimalGrammar (compileParsePlan decimalGrammar) :=
  ParsePlan.compile_certifiedFor decimalGrammar

end Triptych.ParsePlanTests
