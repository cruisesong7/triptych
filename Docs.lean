/-
Triptych documentation — root of the manual (book genre).

From cedar-examples/:
Build:   lake build docs
Render:  lake exe docs --output ../_site
-/
import VersoManual
import Docs.Intro
import Docs.Walkthrough
import Docs.Automation
import Docs.Obligations
import Docs.Scope
import Docs.Execution
import Docs.Conformance

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "Triptych" =>

%%%
authors := ["Triptych"]
shortTitle := "Triptych"
%%%

Triptych is a Lean 4 *grammar-to-parser compiler* for flat, non-recursive string formats.

A {lit}`triptych` block -- a grammar plus optional value, constraint, external-parser, and
printer clauses -- generates a coherent family of artifacts:

- a *readable surface specification* with typed syntax derivations,
- a specialized executable parser and typed decoded view, and
- machine-checked reconciliation, parser-contract, and printer theorems.

Compiler-generated proofs depend only on {name}`propext`, {name}`Classical.choice`, and
{name}`Quot.sound`. The shipped Cedar examples also discharge every format-specific
external-parser and printer obligation.

The chapters follow the compiler from its source DSL through executable parsing, proof
automation, deployment boundaries, and Cedar conformance evidence.

{include 0 Docs.Intro}

{include 0 Docs.Walkthrough}

{include 0 Docs.Automation}

{include 0 Docs.Obligations}

{include 0 Docs.Scope}

{include 0 Docs.Execution}

{include 0 Docs.Conformance}
