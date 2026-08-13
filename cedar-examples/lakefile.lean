import Lake
open Lake DSL

require triptych from ".."
require Cedar from "../../cedar-spec/cedar-lean"
require verso from git "https://github.com/leanprover/verso.git" @ "v4.31.0"

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

-- The Verso book is an integration target: it checks the generated Cedar modules while its
-- source remains at the repository root.
lean_lib Docs where
  srcDir := ".."
  globs := #[.andSubmodules `Docs]

lean_exe docs where
  srcDir := ".."
  root := `DocsMain

lean_exe playground where
  root := `PlaygroundMain
