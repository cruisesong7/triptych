# Strata examples

Triptych reference grammars for non-recursive fragments of Strata's SMT-LIB syntax.

- `Inputs/SMT/SpecConstant/grammar.lean` covers the numeral, decimal, negative convenience,
  and quoted-string forms exercised by Strata's existing `SpecConstant` parser tests. Its
  generated values use `Nat`, `StrataDDM.Decimal`, and `String`.
- `Inputs/SMT/BitVector/grammar.lean` covers SMT-LIB binary and hexadecimal bit-vector literals.
- `Outputs/SMT/` contains the generated readable specifications and verified parsers.
- `Proofs/SMT/` contains checked serializers and their parser-roundtrip proofs.

The package pins Strata-DDM at the commit used for these examples and compiles it under Lean
4.33. The lexical grammar remains explicit in Triptych; a later parser bridge can prove
agreement with Strata's generated SMT parser.

```sh
lake build
```
