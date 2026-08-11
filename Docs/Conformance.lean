/-
Triptych documentation — Chapter 5: conformance testing against Cedar's parsers.
-/
import VersoManual

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Conformance: testing against the real thing" =>

%%%
tag := "conformance"
shortTitle := "Conformance"
file := "conformance"
%%%

The proofs in this book relate generated artifacts to each other and — through the
obligations of chapter 3 — to external parsers. But proofs are only as good as the
statements they prove, and every statement is ultimately anchored in a human transcription:
someone read Cedar's documentation and wrote the `triptych` block. What if the
*transcription* is wrong? A grammar that faithfully generates a spec, a parser, and a
reconciliation proof for the *wrong format* passes every check the previous chapters
described.

Triptych's answer is old-fashioned and effective: run the generated parsers against the
real ones, on the real project's own test corpus.

# The setup

`Triptych/Examples/ConformanceTests.lean` runs the *generated executable parsers* —
`Decimal.parse`, `Duration.parse`, `Datetime.parse`, the actual decode-based engines from
chapter 2, not the readable `Prop`s — against Cedar's real parsers, over every string that
cedar-lean's own unit tests exercise: 32 Decimal strings, 42 Duration, and 70 Datetime,
valid and invalid cases alike.

Cedar is the oracle. For Decimal and Duration, `lift` makes the generated parser return the
*same type* as Cedar's (`Option Decimal`, `Option Duration`), so each check is a direct
equality with no hard-coded expectations:

```
check s (Decimal.parse s) (Cedar.Spec.Ext.Decimal.parse s)
```

Any divergence — in *acceptance* or in *value* — shows up. Datetime has no `lift` (Cedar
defines no canonical `ToString Datetime`, so there is no printer clause to serve), so its
generated parser returns epoch milliseconds as `Option Int` and the check compares through
the projection: `Datetime.parse s = (Cedar.…parse s).map datetimeMillis`.

Two implementation choices matter:

- *It gates the build.* The suite runs in `#eval` at elaboration time and throws on a
  nonzero failure count, so a diverging spec does not just print a warning — it fails
  `lake build`. (It lives in its own library target, out of the default build, so the core
  library stays fast.)
- *It is plain evaluation.* No `native_decide`, no axioms — the same kernel-visible
  reduction as everything else in the project. The conformance suite adds no trust
  assumptions.

# What it caught: the Duration sign bug

The suite is not hypothetical insurance; it caught a real bug during development.

An early version of the Duration grammar wrote the optional leading minus sign inline, as a
bare optional literal in the top production — the natural transcription of
`Duration ::= ['-'] Components`. The grammar was correct as a *recognizer*: negative
durations parsed fine. But the decoder records captured substrings under *production names*,
and a bare literal belongs to no named production — so the minus sign was matched and then
captured nowhere. The value function, reading captures by name, never saw it:
`"-1d"` quietly computed the same positive value as `"1d"`.

Every proof in `parser.lean` held throughout. The spec and the engine agreed perfectly —
*both* dropped the sign, because both were generated from the same (subtly wrong) grammar.
This is precisely the failure mode reconciliation proofs cannot catch: a faithful
implementation of an unfaithful transcription. The conformance run flagged it immediately, as
a value mismatch against Cedar's parser on the negative-duration test strings.

The fix became a design rule rather than a bug fix: the DSL now provides a dedicated `sign`
terminal that must be a production's sole right-hand side (`Sign ::= sign`), so a sign always
owns a named capture, and the value DSL reads it by bare production name. The elaborator
rejects the shapes that made the bug expressible. Chapter 2's aside about the sign production
is this story in its brief form.

# The moral: proofs and tests are complements

It is tempting to read verification as making tests obsolete. The Duration bug shows why
that is wrong in a precise way. The proof stack guarantees *internal* coherence: spec,
engine, and parser cannot drift from each other. The conformance suite anchors the stack
*externally*: the whole coherent tower actually describes Cedar's format, on the evidence of
Cedar's own test corpus. Each covers the other's blind spot —

- proofs quantify over *all* strings, but only relative to the transcribed grammar;
- tests check the *real* parser, but only on finitely many strings.

The obligations of chapter 3 close the loop fully — `extparse_sound` and friends turn the
finite test evidence into a universally quantified theorem — but they take real proof work
(Decimal's are done; Duration's and Datetime's remain open). The conformance suite is the
cheap, immediate check that keeps the transcription honest while that work proceeds, and a
regression net thereafter: it reruns on every build of its target.
