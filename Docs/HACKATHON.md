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
formal spec for you. We keep it to the simple class these formats actually live in — no
recursion, fixed shape — which is exactly what makes the whole thing automatable.

```
format_spec Decimal where
  grammar
    Decimal  ::= Integer "." Fraction
    Integer  ::= ["-"] digit+
    Fraction ::= digit{1,4}
  value
    int Integer * 10^4 + sign Integer * nat Fraction * 10^(4 - len Fraction)
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

## Where it could go

- Point the generated soundness/completeness obligations at a *real* parser (e.g. the
  Cedar-Lean extension parsers) and discharge them.
- Grow past the simple class into dependent / length-prefixed formats — IPv6 `::`, TLV,
  protobuf, count-prefixed arrays, SAT-style graph encodings — where a value read from the
  input decides how much to parse next.

## One-liner

> Write a five-line grammar, get a trustworthy formal spec for its parser — plus the proof
> that the readable version and the runnable version are the same thing.
