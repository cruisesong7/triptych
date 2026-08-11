# Other Triptych Examples

This Cedar-free package contains the structured Graph example for the Triptych grammar compiler.

```sh
lake build
lake exe parser_benchmark
```

The Lean sources use the `Graph.*` module prefix. Cedar-backed examples and validation proofs
live in `../cedar-examples/`. The benchmark is a smoke measurement with no timing threshold; it
reports elapsed time and the reference decoder's structural budgets for representative graphs.
