/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Triptych.Architecture.Denote

/-!
# Conservative static unambiguity analysis

`Grammar.unaryUnique` recognizes a small, useful deterministic grammar fragment:

* the start production contains exactly one required symbol;
* every production reached through a reference also contains exactly one required symbol;
* the path ends in one literal or token run.

Token runs may have any `LenSpec`, including `atLeastOne`: although they enumerate several
prefixes, at most one consumes the complete input. Fuel bounds reference traversal by the
number of productions, so cyclic and overlong paths are rejected.

`Grammar.sequenceUnique` broadens that fragment to required single-alternative sequences.
Every non-final symbol must have at most one PREFIX match: literals, exact-width token runs,
or references to recursively prefix-unique sequences. The final symbol may instead use the
weaker unary rule above, because only a full-consumption match can complete the sequence.
Thus a sequence can end in a variable-width token while retaining unique full parses. A
variable-width unary token path may also precede a required literal delimiter when the
delimiter's first character is outside the token class.

`Grammar.optionalHeadUnique` recognizes a required reference of the form `X ::= ["lit"]` at
the start of a sequence. The consuming and empty cases are exclusive when the remainder is
sequence-unique and cannot start with the literal's first character. This captures optional
signs followed by unsigned digit runs without assigning PEG-style priority to the optional.

`Grammar.literalAlternativesUnique` accepts several such sequences when each begins with a
required, nonempty literal and those literals have pairwise-distinct first characters. At most
one alternative can then match any input. This first disjointness rule is intentionally
syntactic; recursive FIRST-set analysis remains future work.

This is deliberately a sufficient check, not a complete ambiguity decision procedure.
General optionals, shared-prefix alternatives, and separated repetitions currently return
`false`. `Grammar.staticUnique` combines the supported fragments, and
`Triptych.Theorems.Unambiguity` proves that `true` implies `GrammarDecodeUnique`.
-/

namespace Triptych

/-- Check that `sym` starts a unary reference path ending in one literal or token run. -/
def Grammar.unaryUniqueFrom (g : Grammar) : Nat → Sym → Bool
  | _, .lit _ => true
  | _, .str => false
  | _, .term _ _ => true
  | _, .rep _ _ _ _ => false
  | 0, .ref _ => false
  | fuel + 1, .ref name =>
      match g.prod? name with
      | some { name := _, alts := [[{ sym := inner, optional := false }]] } =>
          g.unaryUniqueFrom fuel inner
      | _ => false

/-- Conservative grammar-level uniqueness check. A missing start production returns `true`
    because it has no parses; otherwise the start must be a unary deterministic path. -/
def Grammar.unaryUnique (g : Grammar) : Bool :=
  match g.startProd? with
  | none => true
  | some { name := _, alts := [[{ sym := inner, optional := false }]] } =>
      g.unaryUniqueFrom g.prods.length inner
  | _ => false

/-- Check that `sym` has at most one PREFIX match. Unlike `unaryUniqueFrom`, this cannot accept
    a variable-width token: several prefixes may match even though at most one consumes the
    complete input. References may expand to required, single-alternative sequences. -/
def Grammar.prefixUniqueFrom (g : Grammar) : Nat → Sym → Bool
  | _, .lit _ => true
  | _, .str => false
  | _, .term _ (.exactly _) => true
  | _, .term _ (.between lo hi) => lo == hi
  | _, .term _ .atLeastOne => false
  | _, .rep _ _ _ _ => false
  | 0, .ref _ => false
  | fuel + 1, .ref name =>
      match g.prod? name with
      | some { name := _, alts := [alt] } =>
          alt.all (fun item => !item.optional && g.prefixUniqueFrom fuel item.sym)
      | _ => false

/-- A required sequence in which every symbol has at most one prefix match. -/
def Grammar.prefixUniqueSeqFrom (g : Grammar) (fuel : Nat) (seq : Seq) : Bool :=
  seq.all (fun item => !item.optional && g.prefixUniqueFrom fuel item.sym)

/-- Check a unary reference path ending in a token whose class excludes the first character
    of `delimiter`. Two different token-prefix lengths therefore cannot both place the same
    nonempty delimiter immediately after the token. -/
def Grammar.delimiterUniqueFrom (g : Grammar) : Nat → Sym → String → Bool
  | _, .term tok _, delimiter =>
      match delimiter.toList.head? with
      | none => false
      | some c => !(decide (tok.mem c))
  | 0, .ref _, _ => false
  | fuel + 1, .ref name, delimiter =>
      match g.prod? name with
      | some { name := _, alts := [[{ sym := inner, optional := false }]] } =>
          g.delimiterUniqueFrom fuel inner delimiter
      | _ => false
  | _, _, _ => false

/-- Check unique full consumption for a required sequence. Every intermediate symbol must be
    prefix-unique; the final symbol may also be a unary variable-width path. A non-prefix-
    unique unary token path is accepted before a required literal delimiter whose first
    character is outside that token's class. -/
def Grammar.sequenceUniqueSeqFrom (g : Grammar) (fuel : Nat) : Seq → Bool
  | [] => true
  | [item] =>
      !item.optional &&
        (g.prefixUniqueFrom fuel item.sym || g.unaryUniqueFrom fuel item.sym)
  | item :: next :: rest =>
      !item.optional &&
        ((g.prefixUniqueFrom fuel item.sym &&
            g.sequenceUniqueSeqFrom fuel (next :: rest)) ||
          (!next.optional &&
            match next.sym with
            | .lit delimiter =>
                g.delimiterUniqueFrom fuel item.sym delimiter &&
                  g.sequenceUniqueSeqFrom fuel rest
            | _ => false))

/-- Conservative sequence-level uniqueness check. A missing start production has no parses;
    otherwise the start must contain one required sequence accepted by
    `sequenceUniqueSeqFrom`. -/
def Grammar.sequenceUnique (g : Grammar) : Bool :=
  match g.startProd? with
  | none => true
  | some { name := _, alts := [alt] } =>
      g.sequenceUniqueSeqFrom g.prods.length alt
  | _ => false

/-- Check that every match of `sym` consumes a nonempty prefix whose first character differs
    from `c`. This is a deliberately narrow FIRST-character exclusion analysis: literals,
    nonempty token runs, and unary required reference paths are supported. -/
def Grammar.headExcludesFrom (g : Grammar) : Nat → Sym → Char → Bool
  | _, .lit l, c =>
      match l.toList.head? with
      | none => false
      | some d => d != c
  | _, .term tok len, c =>
      let nonempty := match len with
        | .exactly n => n != 0
        | .between lo _ => lo != 0
        | .atLeastOne => true
      nonempty && !(decide (tok.mem c))
  | 0, .ref _, _ => false
  | fuel + 1, .ref name, c =>
      match g.prod? name with
      | some { name := _, alts := [[{ sym := inner, optional := false }]] } =>
          g.headExcludesFrom fuel inner c
      | _ => false
  | _, _, _ => false

/-- If `sym` is a reference to exactly one optional, nonempty literal, return that literal.
    Keeping this shape explicit makes the associated capture-map proof transparent. -/
def Grammar.optionalLiteralRef? (g : Grammar) : Nat → Sym → Option String
  | 0, _ => none
  | _fuel + 1, .ref name =>
      match g.prod? name with
      | some { name := _, alts := [[{ sym := .lit l, optional := true }]] } =>
          if l.isEmpty then none else some l
      | _ => none
  | _, _ => none

/-- Check a single start sequence beginning with a required `X ::= ["lit"]` reference. The
    remainder must already be sequence-unique and must reject `lit`'s first character. -/
def Grammar.optionalHeadUnique (g : Grammar) : Bool :=
  match g.startProd? with
  | none => true
  | some { name := _, alts := [item :: rest] } =>
      !item.optional &&
        g.sequenceUniqueSeqFrom g.prods.length rest &&
        match g.optionalLiteralRef? g.prods.length item.sym with
        | none => false
        | some l =>
            match l.toList.head? with
            | none => false
            | some c =>
                match rest with
                | next :: _ => !next.optional && g.headExcludesFrom g.prods.length next.sym c
                | [] => false
  | _ => false

/-- The first character of a required literal that directly leads a sequence. Empty literals,
    optional leaders, terminals, and references return `none`; later FIRST-set analysis can
    generalize this interface. -/
def Seq.leadingLiteral? : Seq → Option Char
  | { sym := .lit l, optional := false } :: _ => l.toList.head?
  | _ => none

/-- Check required sequence-unique alternatives whose direct leading literals have pairwise
    distinct first characters. -/
def Grammar.literalAlternativesUniqueFrom (g : Grammar) (fuel : Nat) : List Seq → Bool
  | [] => true
  | alt :: alts =>
      g.sequenceUniqueSeqFrom fuel alt &&
        match alt.leadingLiteral? with
        | none => false
        | some c =>
            alts.all (fun other =>
              match other.leadingLiteral? with
              | none => false
              | some d => c != d) &&
            g.literalAlternativesUniqueFrom fuel alts

/-- Conservative alternative-level uniqueness check. A missing start production has no
    parses; otherwise every alternative must pass `literalAlternativesUniqueFrom`. -/
def Grammar.literalAlternativesUnique (g : Grammar) : Bool :=
  match g.startProd? with
  | none => true
  | some p => g.literalAlternativesUniqueFrom g.prods.length p.alts

/-- All currently supported static uniqueness fragments. This is the checker consumers should
    use; the narrower checks remain named so their proof rules and diagnostics stay explicit. -/
def Grammar.staticUnique (g : Grammar) : Bool :=
  g.unaryUnique || g.sequenceUnique || g.literalAlternativesUnique || g.optionalHeadUnique

end Triptych
