# Triptych Cedar Examples

This optional Lake package contains the Cedar-backed formats, bridge proofs, and parser
conformance suite. The Cedar-free Graph example lives in the sibling `other-examples` package.

The checkout layout is expected to be:

```text
Documents/
  triptych/
  cedar-spec/
    cedar-lean/
```

From this directory:

```sh
lake build CedarExamples
lake build ConformanceTests
```

`CedarExamples` is the default target. `ConformanceTests` is separate because it evaluates
the generated parsers against Cedar's test corpus and is not part of the generic proof core.
