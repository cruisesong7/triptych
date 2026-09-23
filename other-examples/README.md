# Other Triptych Examples

This Cedar-free package follows the same source/generated/proof layout as `cedar-examples`:

- `Inputs/Graph.lean` contains the public dependent-width grammar;
- `Outputs/Graph/` contains the generated readable specification and verified parser;
- `Proofs/Graph/Examples.lean` contains executable examples and contract checks;
- `Inputs/Graph6.lean` defines the lower-level staged dependent parser;
- `Proofs/Graph6/Scanner.lean` checks its examples, agreement theorem, and search bound.

```sh
lake build
lake exe parser_benchmark
```

Cedar-backed examples and validation proofs live in `../cedar-examples/`. The benchmark compares
the staged direct parser with the generic scanner on a deterministic Decimal-shaped format. It
also runs the verified scanner and archived reference decoder on the same graph inputs. Every
pair checks equal acceptance counts; timings are smoke measurements with no fixed threshold.
