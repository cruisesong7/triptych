# Triptych — grammar in, Lean spec out

## The problem

Format parsers are everywhere and they sit on the trust boundary — decimals, durations,
datetimes, IP addresses, UUIDs, anything turning untrusted text into a typed value. Getting
them right is security-critical.

Getting them right means verifying them against a spec — and the spec is the catch. You
first have to write down what "correct" even means, and that spec has to faithfully mirror
the grammar. Drift slightly from the grammar and you've verified the wrong thing,
confidently. The grammar itself is usually just a few readable lines; everything downstream
is mechanical transcription into a spec you then have to trust. Closing that gap is what
motivates this.

## The idea

A small grammar DSL in Lean, built with Lean's metaprogramming, so that

> **input = the grammar. output = the formal spec.**

You write the grammar once, in notation that looks like the docs, and the tool generates the
formal spec, executable reference parser, and reconciliation proofs. We keep it to a strict
regular subclass — no recursive productions or data-dependent lengths, but with optional
symbols, token runs, and separated repetition — which is exactly what makes generation total.

```
triptych Decimal where
  grammar
    Decimal  ::= Sign Natural "." Fraction
    Sign     ::= sign
    Natural  ::= digit+
    Fraction ::= digit{1,4}
  value
    Sign * (nat Natural * 10^4 + nat Fraction * 10^(4 - len Fraction))
  constraints
    value ∈ [Int64.MIN, Int64.MAX]
```

## What's new

Parser generators (ANTLR, EverParse) hand you *code*. This hands you a *spec*, and that's
useful in three ways:

1. A spec you can verify an existing parser against — no rewrite; it's the formal target a
   hand-written parser gets checked against.
2. A spec that's readable — it reads like the grammar, so a human can check it against the
   grammar by eye and trust the transcription is faithful.
3. A generated proof that the readable spec and a runnable version are the same thing — so
   you get something both a person and a machine can check, guaranteed to agree.

It also emits a correct-by-construction reference parser, typed derivation trees, and a small
obligation surface for an independent external parser or canonical serializer.

## Where it stands

- Decimal, Duration, Datetime, IPv4, and IPv6 target Cedar's real extension parsers.
- Every shipped parser/printer scaffold obligation is discharged.
- Cedar conformance covers generated parsers, readable specs, checked external parsers, and
  printer roundtrip with zero failures.
- The Cedar-free Graph example demonstrates arbitrary structured `value'` output and an
  independent decidable `constraints'` predicate. Collection escapes can consume every repeated
  capture through `[X]`, with generated reconciliation and typed views.

## Where it could go

- Reuse common semantic components and external-parser bridge lemmas.
- Extend automatic printer synthesis beyond the proved signed-decimal patterns and add analyzable
  collection reductions beyond `count X` and list-aware escapes.
- Improve static capture-functionality coverage and deterministic execution; CI, structural
  decoder budgets, and a benchmark smoke target now provide regression evidence.
- Add UUID and DIMACS CNF examples. Recursive and data-dependent formats such as JSON, TLV, and
  protobuf remain outside the current grammar class.

## One-liner

> Write a five-line grammar, get a trustworthy formal spec for its parser — plus the proof
> that the readable version and the runnable version are the same thing.
