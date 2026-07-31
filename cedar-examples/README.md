# Triptych Cedar Examples

This optional Lake package contains the Cedar-backed formats, external-parser proofs, and parser
conformance suite. The Cedar-free Graph example lives in the sibling `other-examples` package.

The source layout separates authored inputs from compiler output and proof support:

```text
Grammars/<Format>.lean              handwritten Triptych DSL input
Generated/<Format>/spec.lean        generated readable specification
Generated/<Format>/parser.lean      generated verified parser
Generated/<Format>/soundness.lean   generated proof-obligation scaffold, when needed
Proofs/<Format>/*.lean              format-specific proof automation and views
CedarSupport/*.lean                 shared Cedar backend rules and internals
```

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
