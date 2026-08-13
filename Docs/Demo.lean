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

The Demo opens the Cedar examples in the public {lit}`lean4web` editor. Select a format, then
open its grammar source, generated readable specification, generated parser, or completed
soundness proofs.

:::demo
:::

Lean4web loads the exact source from Triptych's {lit}`main` branch. The public server does not
install Triptych's custom Lake dependencies, so this Demo is for browsing and editing source.
The repository's CI checks the files in the complete {lit}`cedar-examples` project.

To generate files, edit the real grammar module locally and run
{lit}`lake env lean Inputs/Decimal.lean` from {lit}`cedar-examples`.

The active {lit}`to "Outputs/Decimal"` clause rewrites generated {lit}`spec.lean` and
{lit}`parser.lean`. It creates {lit}`soundness.lean` once and then preserves that file because it
contains user proofs.

Use *New grammar* to open a separate editor with a small signed-natural starting point.
