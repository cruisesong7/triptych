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
import Docs.Scope
import Docs.NextSteps
-- import Docs.Playground
import Docs.Demo

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "Triptych" =>

%%%
shortTitle := "Triptych"
%%%

![Triptych. Parser, spec, and soundness: one grammar, three panels.](triptych-logo.svg)

Triptych is a Lean 4 *grammar-to-parser compiler* for flat, non-recursive string formats.

A {lit}`triptych` block -- a grammar plus optional value, constraint, external-parser, and
printer clauses -- generates a coherent family of artifacts:

- a *readable surface specification* with typed syntax derivations,
- a *verified executable parser* and typed decoded view, and
- machine-checked reconciliation, parser-contract, and printer theorems.

Compiler-generated proofs depend only on {name}`propext`, {name}`Classical.choice`, and
{name}`Quot.sound`. The shipped Cedar examples also discharge every format-specific
external-parser and printer obligation.

The chapters follow the compiler from its source DSL through executable parsing, generated
correctness proofs, checks against Cedar's test corpus, proof automation, current scope, and
next steps.

{include 0 Docs.Intro}

{include 0 Docs.Walkthrough}

{include 0 Docs.Automation}

{include 0 Docs.Scope}

{include 0 Docs.NextSteps}

{include 0 Docs.Demo}
