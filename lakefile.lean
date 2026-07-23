import Lake
open Lake DSL

require "leanprover-community" / "batteries" @ git "v4.31.0"

-- Local dependency on cedar-lean (same toolchain v4.31.0, same batteries commit): lets the
-- generated `soundness.lean` reference the REAL Cedar ext-type parsers (e.g.
-- `Cedar.Spec.Ext.Decimal.parse`) as the external parser in the contract obligations.
require Cedar from "../cedar-spec/cedar-lean"

-- Documentation site (Verso manual/book genre), pinned to the same toolchain (v4.31.0). Only
-- built when you explicitly target the `docs` exe / `Docs` lib, so it doesn't slow the core build.
require verso from git "https://github.com/leanprover/verso.git" @ "v4.31.0"

package triptych

@[default_target]
lean_lib Triptych where
  defaultFacets := #[LeanLib.staticFacet]

-- One-time conformance tests: the GENERATED executable parsers vs Cedar's REAL parsers over
-- Cedar's OWN test corpus. Kept out of `default_target` (it's a confidence check, not part of the
-- proof story); build/run with `lake build Triptych.Examples.ConformanceTests`.
lean_lib ConformanceTests where
  globs := #[.one `Triptych.Examples.ConformanceTests]

-- The Verso documentation book. This `docs` branch tracks `main` and adds the site on top.
lean_lib Docs where
  globs := #[.andSubmodules `Docs]

lean_exe docs where
  root := `DocsMain
