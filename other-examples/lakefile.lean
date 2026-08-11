import Lake
open Lake DSL

require triptych from ".."

package graph

@[default_target]
lean_lib Graph where
  globs := #[
    .one `Graph,
    .submodules `Graph
  ]
  defaultFacets := #[LeanLib.staticFacet]

lean_exe parser_benchmark where
  root := `ParserBenchmark
