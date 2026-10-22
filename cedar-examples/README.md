# Triptych Cedar Examples

This optional Lake package contains the Cedar-backed formats, external-parser proofs, and parser
conformance suite. The Cedar-free Graph example lives in the sibling `other-examples` package.

The source layout separates authored inputs from compiler output and proof support:

```text
Inputs/<Format>.lean                handwritten Triptych DSL input
Outputs/<Format>/spec.lean          generated readable specification
Outputs/<Format>/parser.lean        generated verified parser
Outputs/<Format>/soundness.lean     generated proof-obligation scaffold, when needed
Proofs/<Format>/*.lean              format-specific proof automation and views
CedarSupport/*.lean                 shared Cedar backend rules and internals
```

Cedar comes from the `cruise-docs` branch of the `cruisesong7/cedar-spec` fork (the `cedar-lean`
subdirectory), pinned in `lakefile.lean` to a Lean v4.34.0 revision that has the extension-parser
proofs; Lake fetches it. To move Cedar forward, change that
revision, keep `lean-toolchain` in step with Cedar's, and run `lake update Cedar`.

From this directory:

```sh
lake build CedarExamples
lake build ConformanceTests
```

`CedarExamples` is the default target. `ConformanceTests` is separate because it evaluates
the generated parsers against Cedar's test corpus and is not part of the generic proof core.

All shipped `Outputs/*/soundness.lean` obligations are discharged. The current conformance
matrix is:

| Surface | Cases |
|---|---:|
| Decimal generated / checked external | 32/32 each |
| Duration generated / checked external | 42/42 each |
| Datetime generated / checked external | 74/74 each |
| IPv4 generated / readable spec / checked external | 89/89 each |
| IPv6 generated / readable spec / checked external | 89/89 each |

Run `lake exe scanner_benchmark` for paired scanner/reference-decoder measurements on Decimal
and IPv6. The benchmark checks equal acceptance counts and reports timing without a CI threshold.
| IPv6 printer roundtrip | 52/52 |

The build aborts on any mismatch; the current total is zero failures.
