/-
FormatSpec documentation site — introductory post.
-/
import VersoBlog
open Verso Genre Blog

#doc (Post) "One grammar, three artifacts that can't drift" =>

%%%
authors := ["FormatSpec"]
date := {year := 2026, month := 7, day := 20}
%%%

FormatSpec takes a single `format_spec` block and emits three things: a *surface spec* you
can read, an *engine* you can run, and a *proof* that the two describe the same language.
The proof is emitted automatically and checked by the Lean kernel, so the spec and the engine
cannot silently disagree.

# The problem

Hand-written format parsers drift from their prose specifications. Someone tweaks the parser to
fix a bug; the spec in the comment above it no longer holds; nothing catches it. FormatSpec
removes the gap by *generating* both the spec and the engine from one grammar and mechanically
reconciling them.

# The gradient

The DSL is deliberately layered — a graceful-degradation gradient from fully automatic to
fully manual:

1. *Full auto-proof.* A pure grammar (concatenation, alternation, optional, counted
   terminals, separated repetition). Everything — spec, engine, equivalence, decidability, and
   a correct-by-construction parser — is generated and proven with zero manual obligations.
   *Example: Decimal.*
2. *Escape with a manual contract.* A `value'` or `constraints'` escape lets the accepted
   language be any decidable predicate and the parsed value any type, at the cost of
   discharging a small, explicit contract. *Example: Graph.*
3. *Out of scope.* Data-dependent length (e.g. graph6's 6-bit packing) falls outside the
   grammar class and is handled by a hand-written decoder.

# Anti-drift documentation

This site is built with [Verso](https://github.com/leanprover/verso), which type-checks the
Lean code it renders as part of building the site. That means the walkthrough below can pull
the *actual* generated definitions out of the FormatSpec library — if they stop compiling, the
site stops building. The documentation inherits the same anti-drift property the library was
designed to provide.

To wire a verified example in, point Verso at the package and reference a real declaration by
name. Sketch (uncomment once the target declaration path is confirmed):

```
-- {leanExampleProject fs "."}
-- {leanExampleModule fmod "." FormatSpec.Examples.Decimal.parser}
-- {leanCommand fs FormatSpec.Examples.Decimal.parse}
```

The next post will replace this sketch with the live Decimal walkthrough.
