import Lake
open Lake DSL

require "leanprover-community" / "batteries" @ git "v4.31.0"

-- Documentation site (Verso manual/book genre), pinned to the same toolchain (v4.31.0). Only
-- built when you explicitly target the `docs` exe / `Docs` lib, so it doesn't slow the core build.
require verso from git "https://github.com/leanprover/verso.git" @ "v4.31.0"

package triptych

@[default_target]
lean_lib Triptych where
  globs := #[
    .one `Triptych,
    .submodules `Triptych.Architecture,
    .submodules `Triptych.Automation,
    .one `Triptych.Theorems.Coherence,
    .one `Triptych.Theorems.Derivation,
    .one `Triptych.Theorems.DecodeLemmas,
    .one `Triptych.Theorems.Reconcile,
    .one `Triptych.Theorems.RelationalParser,
    .one `Triptych.Theorems.Roundtrip,
    .one `Triptych.Theorems.String,
    .one `Triptych.Theorems.Unambiguity,
    .one `Triptych.Theorems.Value
  ]
  defaultFacets := #[LeanLib.staticFacet]

-- The Verso documentation book. This `docs` branch tracks `main` and adds the site on top.
lean_lib Docs where
  globs := #[.andSubmodules `Docs]

lean_exe docs where
  root := `DocsMain
