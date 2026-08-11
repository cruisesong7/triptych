import Lake
open Lake DSL

require triptych from ".."
require Cedar from "../../cedar-spec/cedar-lean"

package cedarExamples

@[default_target]
lean_lib CedarExamples where
  globs := #[
    .one `CedarExamples,
    .submodules `CedarSupport,
    .submodules `Outputs,
    .submodules `Inputs,
    .submodules `Proofs
  ]
  defaultFacets := #[LeanLib.staticFacet]

-- Generated parsers vs Cedar's real parsers over Cedar's own test corpus.
lean_lib ConformanceTests where
  globs := #[.one `ConformanceTests]
