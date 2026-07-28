import Lake
open Lake DSL

require "leanprover-community" / "batteries" @ git "v4.31.0"

package triptych

@[default_target]
lean_lib Triptych where
  globs := #[
    .one `Triptych,
    .submodules `Triptych.Architecture,
    .one `Triptych.Theorems.Coherence,
    .one `Triptych.Theorems.DecodeLemmas,
    .one `Triptych.Theorems.Reconcile,
    .one `Triptych.Theorems.RelationalParser,
    .one `Triptych.Theorems.Roundtrip,
    .one `Triptych.Theorems.Unambiguity
  ]
  defaultFacets := #[LeanLib.staticFacet]

-- The Verso documentation book (chapters, verso dependency, `docs` targets) lives on the
-- `docs` branch, which tracks `main` and adds the site on top.
