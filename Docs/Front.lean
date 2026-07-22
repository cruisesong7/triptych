/-
FormatSpec documentation site — front page.
-/
import VersoBlog
open Verso Genre Blog

#doc (Page) "FormatSpec" =>

A Lean 4 *grammar-to-specification compiler* for flat, non-recursive string-format
parsers.

A `format_spec` block — a grammar plus optional value and constraint clauses — generates
three artifacts that are proven to agree with each other:

- a *readable surface spec* (proof-free prose-level predicates),
- an *analyzable/executable engine* (the parser you actually run), and
- an *auto-emitted, machine-checked reconciliation proof* tying the two together.

Every generated equivalence depends only on `propext`, `Classical.choice`, and `Quot.sound` —
no `sorry`, no `native_decide`, no new axioms.

See the [blog](/blog) for a walkthrough of how it works and what it can express.
