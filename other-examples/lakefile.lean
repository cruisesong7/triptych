import Lake
open Lake DSL

require triptych from ".."

package otherExamples

@[default_target]
lean_lib OtherExamples where
  globs := #[
    .one `OtherExamples,
    .submodules `Inputs,
    .submodules `Outputs,
    .submodules `Proofs
  ]
  defaultFacets := #[LeanLib.staticFacet]

lean_exe parser_benchmark where
  root := `ParserBenchmark
