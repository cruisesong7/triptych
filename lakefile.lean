import Lake
open Lake DSL

require "leanprover-community" / "batteries" @ git "v4.34.0"

package triptych

@[default_target]
lean_lib Triptych where
  globs := #[
    .one `Triptych,
    .submodules `Triptych.Core,
    .submodules `Triptych.Reference,
    .submodules `Triptych.Runtime,
    .submodules `Triptych.Plan,
    .submodules `Triptych.Elab,
    .submodules `Triptych.Automation,
    .submodules `Triptych.Backend,
    .submodules `Triptych.Tests
  ]
  defaultFacets := #[LeanLib.staticFacet]
