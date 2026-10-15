import Lake
open Lake DSL

require "leanprover-community" / "batteries" @ git "v4.34.0"

package triptych

@[default_target]
lean_lib Triptych where
  globs := #[
    .one `Triptych,
    .submodules `Triptych.Reference,
    .submodules `Triptych.Architecture,
    .submodules `Triptych.Automation,
    .submodules `Triptych.Backend,
    .submodules `Triptych.Theorems
  ]
  defaultFacets := #[LeanLib.staticFacet]
