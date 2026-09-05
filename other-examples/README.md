# Other Triptych Examples

This Cedar-free package contains the structured Graph example for the Triptych grammar compiler.

```sh
lake build
lake exe parser_benchmark
```

The Lean sources use the `Graph.*` module prefix. Cedar-backed examples and validation proofs
live in `../cedar-examples/`. The benchmark runs the verified scanner and archived reference
decoder on the same graph inputs, checks equal acceptance counts, and reports their relative
time. It is a smoke measurement with no fixed timing threshold.
