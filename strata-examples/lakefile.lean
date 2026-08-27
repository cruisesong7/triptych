import Lake
open Lake DSL

require triptych from ".."
require StrataDDM from git
  "https://github.com/strata-org/Strata-DDM" @
    "247e0512ccd91c0280c1d98401bc7795b6d3a1a4"

package strataExamples

@[default_target]
lean_lib StrataExamples where
  globs := #[
    .one `StrataExamples,
    .submodules `Inputs,
    .submodules `Outputs,
    .submodules `Proofs
  ]
  defaultFacets := #[LeanLib.staticFacet]
