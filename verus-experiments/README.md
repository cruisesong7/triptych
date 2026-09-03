# Verus specification experiment

This experiment translates Triptych's elaborated grammar, value, and constraint ASTs into a
readable Verus specification and an external-parser contract scaffold. The generated Decimal
files are `cedar-ext/decimal/src/spec.rs` and `cedar-ext/decimal/src/soundness.rs`.

## Generated specification

The Verus surface deliberately follows the generated Lean specification:

| Lean specification | Verus specification |
| --- | --- |
| `Decimal.IsWf.Sign` | `decimal_is_wf_sign` |
| `Decimal.IsWf.Natural` | `decimal_is_wf_natural` |
| `Decimal.IsWf.Decimal` | `decimal_is_wf_decimal` |
| `Decimal.View` | `DecimalView` |
| `Decimal.value` | `decimal_value` |
| `Decimal.Constraints` | `decimal_constraints` |
| `Decimal.SatisfiesConstraints` | `decimal_satisfies_constraints` |
| `Decimal.IsValid` | `decimal_is_valid` |

The grammar predicate also keeps the readable component structure. For example, the Decimal root
quantifies `sign`, `natural`, and `fraction`, equates the input with their concatenation around the
decimal-point literal, and applies each production predicate.

`spec.rs` contains specification definitions only. It does not contain `decode_view`,
`compute_value`, a functional parser contract, an executable Rust parser, `proof fn`
declarations, or a proof about Cedar's production parser.

`soundness.rs` is generated separately and contains:

- `decimal_matches_result`, relating a valid typed view to its integer denotation;
- `DecimalExternalParserContract::parse_to_spec`, the specification view of an external parser
  after converting its result to Triptych's integer value;
- `extparse_sound`, `extparse_complete`, and `extparse_reject` proof obligations.

The scaffold is a Verus trait, not an admitted proof. A concrete integration must connect
`parse_to_spec` to the production parser and implement all three `proof fn` methods. Verus then
checks those implementations. Triptych creates `soundness.rs` once and leaves it untouched so
hand-written parser adapters and proofs are not overwritten.

## Cedar runtime conformance

`cedar-ext/decimal/tests/cedar_runtime.rs` invokes the production Decimal parser through Cedar's
public `Expression::new_decimal` and `eval_expression` APIs. It reuses the accepted and rejected
inputs from Cedar's own `decimal_creation` unit test. Accepted inputs are additionally compared
with their expected Decimal values using Cedar's equality operator.

The test depends on the sibling `cedar` checkout and therefore exercises its current
`cedar-policy-core/src/extensions/decimal.rs`, including the private regex-based parser. Run it
with:

```sh
cd verus-experiments/cedar-ext/decimal
cargo test --test cedar_runtime
```

This is behavioral evidence, not a Verus proof of Cedar's parser. Implementing
`DecimalExternalParserContract` remains the formal verification step.

## Translation pipeline

The `triptych` command parses the DSL once, then reuses the same semantic values for Lean and
Verus generation:

1. Grammar declarations become a first-order `Grammar` containing productions, alternatives,
   symbols, token classes, and length bounds.
2. The value clause is parsed once into a `ValExpr`, rather than elaborated separately for Lean
   and Verus.
3. Each constraint is parsed once into a `Constraint` plus its acceptance phase. The parser records
   whether the source mentioned `value` before substituting the shared value AST.
4. The Lean emitter reifies these values into the readable specification and executable engine.
5. `Verus.FormatInput` groups the grammar, value, phased constraints, and conversion names for
   the Verus translator. It is a convenience record, not a separate semantic model.
6. The Verus translator converts these source ASTs into `Triptych.Backend.Verus.Semantic`, a
   semantic deep embedding that still contains operations such as `natOf` and `intPow`.
7. `Triptych.Backend.Verus.Desugar` converts that semantic AST into
   `Triptych.Backend.Verus.Surface`,
   selects only the required helpers, and replaces every semantic operation with concrete calls
   and expressions.
8. `Triptych.Backend.Verus.PrettyPrint` emits Verus syntax from the Surface AST. It does not
   recognize a Decimal-specific shape or substitute a fixed template.
9. The soundness emitter builds a separate Surface AST containing the result relation and
   external-parser contract trait.

The grammar translation emits one predicate per production. Literals become byte sequences,
references become calls to sibling predicates, token runs become quantified byte predicates with
length bounds, and alternatives become disjunctions.

The value translation recursively maps literals, field readers, arithmetic, negation, and powers
to structured `int` expressions. Constraint translation maps string conditions, cardinality,
arithmetic comparisons, and conjunctions to structured `bool` expressions. A generated typed view
keeps the captures used by these expressions attached to one grammar match. The Verus AST has no
raw-code escape hatch.

## Trust boundary

This architecture genuinely narrows the trusted translation boundary:

- Lean and the Verus translator consume the same parsed `Grammar`, `ValExpr`, and `Constraint`
  values.
- Lean defines a denotation for the semantic Verus AST subset and proves that translating a
  `ValExpr` preserves `ValExpr.eval`, including the named-value optimization.
- Lean proves that compiling a `Constraint` preserves `Constraint.eval`. For `strEq`, this theorem
  requires the capture to be present; backend validation therefore requires that field to be a
  non-optional direct reference in every root alternative.
- Recovery theorems additionally show that supported source nodes can be reconstructed from their
  translated Verus AST.
- `denote_desugar_translateValExpr` composes translation and desugaring for every supported value
  expression. `denote_desugar_translateArithmeticConstraint` does the same for arithmetic
  constraints, including Decimal's `Int64` bound.
- `helperDeclaration_realizes` proves that every concrete helper declaration evaluates to its
  canonical byte-level meaning. Separate theorems connect `natOf`, `intOf`, and `signOf` on
  encoded strings to Triptych's audited Lean readers.
- Both AST layers are typed by constructors, making translation and pretty-printing exhaustive
  and preventing ad hoc source fragments from bypassing the pipeline.
- The generated specification and soundness contract are accepted by
  `cargo verus verify -- --no-cheating`.

This proves semantic preservation from supported Triptych value expressions and arithmetic
constraints through Surface AST helper calls. The full high-level constraint theorem also
covers string and cardinality constraints before desugaring. It does not yet prove the grammar
translation or source pretty-printer correct. The pretty-printer, Verus itself, and the generated
grammar/view translation remain trusted. Parsing the emitted source back into an independently
defined syntax, or validating it against Verus's frontend, would reduce that boundary further.

## Current boundary

The current backend supports:

- statically unique, acyclic grammars using ASCII literals, references, and
  `digit`/`hexDigit`/`bit` token runs;
- scalar captures that are direct references in the start production;
- string equality only when its capture is required in every root alternative;
- the arithmetic value AST except `count`;
- both well-formedness and semantic constraint phases.

It currently rejects `str`, separated repetition, repeated-capture counts, nested or qualified
value captures, and opaque `value'` or `constraints'` escapes. `ofSpec` and `toSpec` names are
recorded as conversion-boundary metadata; their Lean implementations are not translated into
Rust.

Verus type-checks the emitted specification and contract scaffold. Merely declaring the contract
trait does not prove an executable Rust parser against it; that requires a concrete implementation
of the trait's proof methods. The backend also does not yet prove the Verus pretty-printer correct
or make Triptych's Lean emitter itself formally verified.

## Commands

From the Triptych repository root:

```sh
./verus-experiments/setup-verus.sh
cd cedar-examples
lake build Inputs.Decimal
cd ..
./verus-experiments/verify.sh
```

The setup script pins Verus `0.2026.08.30.b432e82`, its required Rust toolchain, and the release
archive checksum.
