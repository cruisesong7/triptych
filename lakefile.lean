import Lake
open Lake DSL

require "leanprover-community" / "batteries" @ git "v4.31.0"

-- Local dependency on cedar-lean (same toolchain v4.31.0, same batteries commit): lets the
-- generated `soundness.lean` reference the REAL Cedar ext-type parsers (e.g.
-- `Cedar.Spec.Ext.Decimal.parse`) as the external parser in the contract obligations.
require Cedar from "../cedar-spec/cedar-lean"

package formatspec

@[default_target]
lean_lib FormatSpec where
  defaultFacets := #[LeanLib.staticFacet]
