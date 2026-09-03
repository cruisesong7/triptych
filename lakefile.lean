import Lake
open Lake DSL

require "leanprover-community" / "batteries" @ git "v4.33.0"

package triptych

@[default_target]
lean_lib Triptych where
  globs := #[
    .one `Triptych,
    .submodules `Triptych.Architecture,
    .submodules `Triptych.Automation,
    .submodules `Triptych.Backend,
    .one `Triptych.Theorems.Coherence,
    .one `Triptych.Theorems.Derivation,
    .one `Triptych.Theorems.DecodeLemmas,
    .one `Triptych.Theorems.Reconcile,
    .one `Triptych.Theorems.RelationalParser,
    .one `Triptych.Theorems.Roundtrip,
    .one `Triptych.Theorems.String,
    .one `Triptych.Theorems.Unambiguity,
    .one `Triptych.Theorems.Value
  ]
  defaultFacets := #[LeanLib.staticFacet]
