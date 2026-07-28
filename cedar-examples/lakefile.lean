import Lake
open Lake DSL

require triptych from ".."
require Cedar from "../../cedar-spec/cedar-lean"

package cedarExamples

@[default_target]
lean_lib CedarExamples where
  globs := #[
    .one `CedarExamples,
    .submodules `Decimal,
    .submodules `Duration,
    .submodules `Datetime,
    .submodules `IPv4,
    .submodules `IPv6,
    .submodules `CedarSupport
  ]
  defaultFacets := #[LeanLib.staticFacet]

-- Generated parsers vs Cedar's real parsers over Cedar's own test corpus.
lean_lib ConformanceTests where
  globs := #[.one `ConformanceTests]
