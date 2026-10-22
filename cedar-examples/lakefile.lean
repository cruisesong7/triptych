import Lake
open Lake DSL

require triptych from ".."
-- Cedar on Lean v4.34.0 with the extension-parser proofs (`Cedar.Thm.Ext`): the `cruise-docs`
-- branch of our cedar-spec fork. Upstream only gained those proofs after moving to v4.34.1, and
-- its `main` is on v4.35; Triptych stays on v4.34.0 until Vermilion's lean-smt dependency moves.
require Cedar from git "https://github.com/cruisesong7/cedar-spec.git" @
  "4f1f43b48496378beeb58ac17131372b02593c4a" / "cedar-lean"
require verso from git "https://github.com/leanprover/verso.git" @ "v4.34.0"

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

def docsAnchorNeeds : Array PartialBuildKey := #[
  .packageModuleFacet `cedarExamples `Inputs.Decimal `highlighted,
  .packageModuleFacet `cedarExamples `Outputs.Decimal.soundness `highlighted,
  .packageModuleFacet `triptych `Triptych.Automation.ExternalParserTests `highlighted,
  .packageModuleFacet `triptych `Triptych.Architecture.SyntaxTests `highlighted
]

-- The Verso book is an integration target: it checks the generated Cedar modules while its
-- source remains at the repository root.
lean_lib Docs where
  srcDir := ".."
  globs := #[.andSubmodules `Docs]
  needs := docsAnchorNeeds

lean_exe docs where
  srcDir := ".."
  root := `DocsMain
  needs := docsAnchorNeeds

lean_exe playground where
  root := `PlaygroundMain

lean_exe scanner_benchmark where
  root := `ScannerBenchmark
