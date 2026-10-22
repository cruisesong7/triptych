# Vermilion roundtrip proofs

These proofs are a developer tool for work on Triptych's Verus backend; format authors never need
to run or maintain them. Each `<Format>.lean` file is maintained by hand. If it is missing, the roundtrip command
creates a write-once scaffold containing one public theorem per generated obligation, initially
closed by `sorry`. The checker compares every theorem with the freshly generated proposition and
rejects any theorem that depends on an axiom other than `propext`, `Classical.choice`, and
`Quot.sound` (so `sorry`, `native_decide`, and stray `axiom`s all fail).

Reusable `String ↔ Vermilion.Seq Int` lemmas live in `Utils.lean` under the
`Triptych.Vermilion.String` namespace. The generated check module pins the definition of
`encodeString` by `rfl`, so editing it fails the check instead of changing what the theorems mean.

In addition to direct function equivalences, every format receives four capture/result
obligations:

- `matching_view_normalizes`;
- `matches_view_exact`, which equates each recovered slot with its exact named
  `Triptych.component`;
- `matching_view_exists`; and
- `matches_result`, which equates valid source `computeValue` results with the recovered
  `*_matches_result` relation.

Together these prevent a translated specification from swapping same-shaped captures while still
proving only validity and denotation facts.

## Layout

`verus-experiments/vermilion-roundtrip/` is a Lake package laid out like Vermilion's own case
studies: the proofs are a `lean_lib` with `srcDir := "proofs"`, and Vermilion and `cedar-examples`
are ordinary dependencies. Each format follows Cedar's `Cedar/Thm/Ext/<Format>.lean` +
`<Format>/Lemmas.lean` layout:

```
vermilion-roundtrip/
  lakefile.lean, lake-manifest.json
  proofs/TriptychVermilionProofs/
    Utils.lean             shared String ↔ Vermilion.Seq Int lemmas
    Decimal.lean           public theorems only: the generated statements, each closed by one lemma
    Decimal/Lemmas.lean    every proof body
    Datetime.lean, Datetime/Lemmas.lean, ...
  generated-src/           written by the last check run (git-ignored)
    TriptychVermilionRecovered/<Format>.lean   Vermilion's translation of spec.rs
    TriptychVermilionGenerated/<Format>.lean   Triptych's `Recovered.*` aliases
```

`<Format>.lean` contains exactly one public theorem per generated obligation, with the generated
name and statement and a single-identifier proof:

```lean
import TriptychVermilionGenerated.Decimal
import TriptychVermilionProofs.Decimal.Lemmas

namespace Triptych.Vermilion.Proofs.Decimal

open Triptych
open Triptych.Vermilion.String
open Triptych.Vermilion.Generated.Decimal

theorem decimal_is_wf_Sign :
    ∀ source : String,
      Decimal.IsWf.Sign source ↔
        Recovered.decimal_is_wf_Sign (encodeString source) :=
  sign_equiv

-- One theorem is generated for every deterministic obligation.

end Triptych.Vermilion.Proofs.Decimal
```

Lemma modules use the same namespace. A public theorem whose proof is not just an existing helper
is proved in `Lemmas.lean` as `<theorem>_equiv` with the identical statement. Further modules may
be added under `<Format>/` (for example `Grammar.lean`); the runner copies the whole directory
and compiles it in import order before `<Format>.lean`. A freshly scaffolded format starts as a
single `<Format>.lean` with `sorry` bodies; move the proofs into `<Format>/` as they grow.

## Running and editing

The package expects a sibling Vermilion checkout: `~/Documents/vermilion` on branch
`rust-char-support` of `cruisesong7/vermilion`, which is upstream Vermilion ported to Lean v4.34
(branch `lean-v4.34`) plus the `char` support Triptych's specifications need. Cedar comes through
`cedar-examples` at the revision pinned there. Run the check from the
repository root (rustup's proxies must precede any standalone Rust on `PATH`):

```sh
PATH="/opt/homebrew/opt/rustup/bin:$PATH" lake exe triptych -- check-verus-roundtrip \
  --vermilion-root ~/Documents/vermilion cedar-examples/Inputs/Decimal.lean
```

Each run also refreshes `generated-src/` and links `.lake/packages/` to the dependency checkouts
Vermilion and `cedar-examples` already build, at the revisions pinned in `lake-manifest.json`.
After one run per format, open the proofs in the editor or run `lake build` in
`verus-experiments/vermilion-roundtrip/`.
