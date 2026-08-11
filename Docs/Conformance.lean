/-
Triptych documentation -- Chapter 7: differential evidence and CI.
-/
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "Conformance: proof, differential evidence, and CI" =>

%%%
tag := "conformance"
shortTitle := "Conformance"
file := "conformance"
%%%

Generated reconciliation proves that Triptych's specification and executable agree with each
other. External-parser theorems prove that Cedar agrees with that specification. Differential
testing adds a third check: did the human-authored grammar capture the intended real-world
format on the project's known cases?

# The 13-suite matrix

{lit}`cedar-examples/ConformanceTests.lean` evaluates generated parsers, readable
specifications, checked external wrappers, and printer roundtrips against Cedar's own parser
corpus.

| Surface | Checks |
|---|---:|
| Decimal generated / checked external | 32 + 32 |
| Duration generated / checked external | 42 + 42 |
| Datetime generated / checked external | 74 + 74 |
| IPv4 generated / readable spec / checked external | 89 + 89 + 89 |
| IPv6 generated / readable spec / checked external | 89 + 89 + 89 |
| IPv6 generated and external printer roundtrip | 52 |

The current result is 882 of 882 checks across 13 suites, with zero failures.

For Decimal and Duration, {lit}`ofSpec` makes the generated parser return the same domain type
as Cedar, so each generated check is direct {name}`Option` equality. Datetime compares its
generated epoch-millisecond value with Cedar's parsed datetime mapped through
{lit}`datetimeMillis`.

IPv4 and IPv6 run the same mixed-family corpus. Every IPv6 string is also an IPv4 rejection
case and conversely. Their readable-spec suites separately evaluate
{lit}`decide (IPv4.IsValid s)` and {lit}`decide (IPv6.IsValid s)` against Cedar's family
acceptance.

# Prefix-length boundaries

The IP corpus covers bare addresses, CIDR prefix lengths, address bounds, canonical spelling,
compression, hextet counts, and family dispatch. Names consistently follow the semantic Cedar
API: {lit}`Prefix`, {lit}`IPv4Prefix`, and {lit}`IPv6Prefix` mean the number of leading
network bits. The text {lit}`/24` is appended to an IPv4 address syntactically, but it still
denotes a prefix length, not a suffix concept.

# Checked external behavior

Every format also compares {lit}`checkedExtParse` with the real Cedar parser. Two focused
guards feed a deliberately dishonest Decimal parser to
{lit}`Triptych.checkedExternalParse` and confirm that it rejects both a wrong value and an
invalid string without assuming any theorem about that parser.

# A bug the suite found

An early Duration grammar placed the optional minus sign inline. Recognition was correct, but
anonymous literals are not captured, so the value function computed a negative duration as
positive. The generated specification and parser agreed perfectly on that wrong transcription.

Differential testing found the value mismatch. The fix became a DSL rule:
{lit}`Sign ::= sign` gives the sign a named capture, and the elaborator rejects unsafe sign
shapes.

This is the exact complementarity:

- generated proofs cover every input, relative to the authored grammar;
- static external-parser proofs cover every input, after format semantics are established;
- differential tests exercise the actual integration on a finite, independently authored
  corpus.

# Build gates

The conformance runner uses ordinary evaluation and throws on any failure, so
{lit}`lake build ConformanceTests` is a hard gate. It uses no
{lit}`native_decide` and introduces no axiom.

The CI workflow has three independent jobs:

1. build the Cedar-free core;
2. build the Cedar-free Graph package and run {lit}`parser_benchmark`;
3. check out a pinned Cedar parser revision, build every Cedar proof module, and run all
   conformance suites.

Together, the proof checks, differential matrix, and package-separated CI keep compiler
coherence, format semantics, and real integration visible as distinct claims.
