/-
Triptych documentation -- final chapter: interactive demo.
-/
import VersoManual
import Outputs.Decimal.parser
import Outputs.Duration.parser
import Outputs.Datetime.parser
import Outputs.IPv4.parser
import Outputs.IPv6.parser

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

block_extension demoMount where
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ _ => open Verso.Output.Html in
    pure {{<div data-triptych-demo></div>}}
  toTeX := some fun _ _ _ _ _ => pure .empty

open Verso Doc Elab in
@[directive]
def demo : DirectiveExpanderOf Unit
  | (), _ => ``(Block.other demoMount #[])

#doc (Manual) "Demo" =>

%%%
tag := "demo"
shortTitle := "Demo"
file := "demo"
%%%

This is a real {lit}`lean4web` editor backed by the {lit}`cedar-examples` Lake project.
Select a Cedar format, then open its grammar source, generated readable specification,
generated parser, or completed soundness proofs.

:::demo
:::

The editable web copy comments out {lit}`to "Outputs/..."`. Lean4web checks every snippet as
its virtual root module, so allowing that clause there would generate files with the wrong
caller-module import.

To generate files, edit the real grammar module locally and run
{lit}`lake env lean Inputs/Decimal.lean` from {lit}`cedar-examples`.

The active {lit}`to "Outputs/Decimal"` clause rewrites generated {lit}`spec.lean` and
{lit}`parser.lean`. It creates {lit}`soundness.lean` once and then preserves that file because it
contains user proofs.

Use *New grammar* to open a separate editor with a small signed-natural grammar. It omits the
{lit}`to` clause so it is safe to edit directly in the web Demo.
