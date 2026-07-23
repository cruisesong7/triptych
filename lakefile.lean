import Lake
open Lake DSL

require "leanprover-community" / "batteries" @ git "v4.31.0"

-- Local dependency on cedar-lean (same toolchain v4.31.0, same batteries commit): lets the
-- generated `soundness.lean` reference the REAL Cedar ext-type parsers (e.g.
-- `Cedar.Spec.Ext.Decimal.parse`) as the external parser in the contract obligations.
require Cedar from "../cedar-spec/cedar-lean"

package triptych

@[default_target]
lean_lib Triptych where
  defaultFacets := #[LeanLib.staticFacet]

-- One-time conformance tests: the GENERATED executable parsers vs Cedar's REAL parsers over
-- Cedar's OWN test corpus. Kept out of `default_target` (it's a confidence check, not part of the
-- proof story); build/run with `lake build Triptych.Examples.ConformanceTests`.
lean_lib ConformanceTests where
  globs := #[.one `Triptych.Examples.ConformanceTests]

-- The Verso documentation book (chapters, verso dependency, `docs` targets) lives on the
-- `docs` branch, which tracks `main` and adds the site on top.
