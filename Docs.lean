/-
Triptych documentation — root of the manual (book genre).

Build:   lake build docs
Render:  lake exe docs --output _site
-/
import VersoManual
import Docs.Intro
import Docs.Walkthrough
import Docs.Obligations
import Docs.Scope
import Docs.Conformance

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Triptych" =>

%%%
authors := ["Triptych"]
shortTitle := "Triptych"
%%%

Triptych is a Lean 4 *grammar-to-specification compiler* for flat, non-recursive
string-format parsers.

A `format_spec` block — a grammar plus optional value and constraint clauses — generates
three artifacts that are proven to agree with each other:

- a *readable surface spec* (proof-free prose-level predicates),
- an *analyzable, executable engine* (the parser you actually run), and
- an *auto-emitted, machine-checked reconciliation proof* tying the two together.

Every generated proof depends only on `propext`, `Classical.choice`, and `Quot.sound` —
no `sorry`, no `native_decide`, no new axioms.

This book introduces the tool: why it exists, what it produces, and where its expressive
ceiling sits. The chapters build on each other, so first-time readers should start at the
beginning.

{include 0 Docs.Intro}

{include 0 Docs.Walkthrough}

{include 0 Docs.Obligations}

{include 0 Docs.Scope}

{include 0 Docs.Conformance}
