import Lake
open Lake DSL

/-!
# Vermilion roundtrip proofs (developer tool)

This package holds the hand-maintained proofs that Vermilion's Lean translation of each generated
`spec.rs` agrees with Triptych's readable Lean specification. It is laid out like Vermilion's own
case studies: the proofs are an ordinary `lean_lib` and Vermilion is an ordinary dependency, so
`lake build` and the editor elaborate them directly.

The generated modules come from the latest `check-verus-roundtrip` run, which copies them into
`generated-src/`: `TriptychVermilionRecovered.<Format>` (Vermilion's `Specs.lean`) and
`TriptychVermilionGenerated.<Format>` (Triptych's `Recovered.*` aliases). Run the check once for a
format before opening its proofs.

Vermilion is a sibling checkout; Cedar comes through `cedar-examples` at the revision pinned there.
Vermilion must be the Triptych-compatible branch (`rust-char-support`; see
`verus-experiments/README.md`).
-/

require vermilion from "../../../vermilion"
require cedarExamples from "../../cedar-examples"

package vermilionRoundtrip where
  -- lean-smt calls cvc5 through native FFI; the language server needs the plugin at startup,
  -- exactly as in Vermilion's own lakefile.
  moreGlobalServerArgs :=
    #[s!"--plugin=.lake/packages/cvc5/.lake/build/lib/{nameToSharedLib "cvc5_cvc5"}"]

@[default_target]
lean_lib TriptychVermilionProofs where
  srcDir := "proofs"
  globs := #[.submodules `TriptychVermilionProofs]

lean_lib TriptychVermilionRecovered where
  srcDir := "generated-src"
  globs := #[.submodules `TriptychVermilionRecovered]

lean_lib TriptychVermilionGenerated where
  srcDir := "generated-src"
  globs := #[.submodules `TriptychVermilionGenerated]
