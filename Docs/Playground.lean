/-
Triptych documentation -- Chapter 6: live parser result explorer.
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

block_extension playgroundMount where
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ _ => open Verso.Output.Html in
    pure {{<div data-triptych-playground></div>}}
  toTeX := some fun _ _ _ _ _ => pure .empty

open Verso Doc Elab in
@[directive]
def playground : DirectiveExpanderOf Unit
  | (), _ => ``(Block.other playgroundMount #[])

#doc (Manual) "Parser demo: inspect runtime results" =>

%%%
tag := "parser-demo"
shortTitle := "Parser demo"
file := "parser-demo"
%%%

This demo runs the generated Lean parsers for all five Cedar formats. The browser sends
the selected format and input to a small executable that imports the generated
{lit}`parser.lean` modules. JavaScript displays the response; it does not reimplement the
grammar or parser.

The result separates three useful observations:

1. *well-formed* reports whether the input follows the grammar and its field-level conditions;
2. *semantic constraints* reports the separate value constraint when the format has one; and
3. *valid* is the predicate used to gate the generated executable parser.

The two result columns run {lit}`parse` and {lit}`checkedExtParse`. The latter calls Cedar's
parser and accepts its result only when it agrees with the generated specification. The decoded
fields are the generated typed {lit}`View`, so malformed field contents can still be inspected
when the grammar shape was decoded but a condition later rejected the input.

:::playground
:::

# What is being executed

The endpoint calls the same declarations used throughout this book:

```lean
#check @CedarExamples.Decimal.Decimal.parse
#check @CedarExamples.Duration.Duration.parse
#check @CedarExamples.Datetime.Datetime.parse
#check @CedarExamples.IPv4.IPv4.parse
#check @CedarExamples.IPv6.IPv6.parse
```

The native command-line interface returns the same JSON consumed by the page:

```
lake exe playground -- decimal "-12.34"
```

The web transport is ordinary application code and is not part of the proof. The parser
soundness, completeness, rejection, view, and external-parser agreement theorems remain the
machine-checked boundary.
