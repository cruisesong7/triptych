import Lake
open Lake DSL

require "leanprover-community" / "batteries" @ git "v4.31.0"

package formatspec

@[default_target]
lean_lib FormatSpec where
  defaultFacets := #[LeanLib.staticFacet]
