# Triptych Roadmap

The roadmap is ordered around practical validation and user leverage. Finish one demanding
format family end to end, then reduce how much proof work users must do. Broader static
coherence certificates are useful foundations, but they are not the current product priority.

## 1. Complete IPAddr end to end

Make the Cedar IP address family the primary integration target.

### IPv4

- discharge the two remaining printer obligations;
- discharge the three remaining external-parser obligations;
- retain exact agreement with Cedar for bare addresses, CIDR prefixes, numeric bounds, and
  canonical decimal spelling;
- remove every `sorry` from `IPv4/soundness.lean`.

### IPv6

- expand the current eight-explicit-group example to the complete IPv6 surface accepted by
  Cedar, including compressed `::` forms and network prefixes;
- produce Cedar's complete structured IP value rather than only the explicit-group address;
- add Cedar external-parser and canonical-printer clauses;
- prove the generated value agrees with Cedar across every supported syntactic form;
- add IPv6 valid, invalid, compressed, boundary, and prefix cases to conformance.

### Combined validation

- validate the family-level behavior of Cedar's `ip` parser across IPv4 and IPv6;
- cover inputs where IPv4 and IPv6 dispatch or rejection could disagree;
- keep generated and bridge theorems on the accepted standard axioms;
- run the complete IPAddr suite from the independent `cedar-examples` package.

**Exit criterion:** IPv4 and full IPv6 parse, value, reject, external-parser, printer, and
conformance obligations are complete with no `sorry`.

## 2. Make proofs substantially more automatic

Use the finished IPAddr work to identify repeated proof patterns and move them into Triptych.
Prioritize reductions in user-authored proof volume:

- generate stronger bridge lemmas for common external parser combinators;
- automate routine soundness, completeness, rejection, projection, and printer obligations;
- turn recurring decomposition arguments into reusable tactics or theorem families;
- generate useful proof hints and source-located diagnostics when automation stops;
- separate genuinely semantic obligations from bookkeeping that the compiler can discharge;
- report obligation counts and which DSL escape caused each remaining manual proof;
- add regression tests measuring handwritten proof lines for each Cedar example.

**Exit criterion:** regenerating the IPAddr examples leaves only format-specific semantic facts
for the user, with routine parser plumbing discharged automatically.

## 3. Improve compiler utility and execution quality

- derive default printers for invertible layouts where practical;
- improve diagnostics for inaccessible captures, malformed repetitions, overlapping choices,
  constraint-phase mistakes, and unsupported format features;
- add CI jobs for the Cedar-free core, `other-examples`, and the optional Cedar package;
- avoid unnecessary parse enumeration in deterministic fragments;
- state useful parser cost bounds and benchmark generated parsers on realistic inputs;
- make generated files and proof obligations easier to navigate from the source DSL.

## 4. Finish the remaining Cedar formats

After IPAddr and the automation pass:

- discharge Datetime's three external-parser obligations;
- audit Decimal and Duration after applying the new automation;
- require zero `sorry`, accepted axioms only, and complete conformance for all shipped Cedar
  examples.

## 5. Collection-aware values and constraints

Repeated captures are already available to `value'` as `List String`. Generalize the
analyzable value and constraint tiers with operations such as:

- `count X`;
- `sum X`;
- per-element predicates such as `forall X`;
- list arguments for `constraints'`;
- direct access to generated repetition counts.

## 6. Broader capture-functionality certificates

The current proved foundation remains available:

- required deterministic sequences;
- direct disjoint literal alternatives;
- unary token/literal delimiter boundaries;
- a leading optional-literal reference separated by FIRST-character exclusion;
- emitted `grammarDecodeUnique`, `grammarCaptureFunctional`, `grammarValueCoherent`, and
  `parse_iff_denotes` when certification succeeds.

Do not broaden this analysis ahead of the IPAddr and automation work unless a concrete format
or parser optimization needs it. Later extensions may include recursive FIRST-language
disjointness, general nullable sequences, repetition functionality, production-level
certificate composition, and eventually a tagged finite-state transducer checker with
counterexamples.

## 7. New examples

Only after the current Cedar work is useful and low-friction:

1. **UUIDv4**, followed by **UUIDv7**;
2. **DIMACS CNF**;
3. SemVer, cron expressions, DNS names, or HTTP Structured Fields based on the next concrete
   language feature that needs pressure-testing.

Full JSON and SQL remain out of scope until Triptych has recursive grammar and value semantics.
