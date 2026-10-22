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

import Lean

/-!
# Generated Verus artifact drift detection

The checked-in generated Rust/Verus files are snapshots. During a check, Triptych regenerates the
expected contents in memory and compares them with those snapshots without writing anything.

The default comparison is lexical: whitespace and comments outside literals are ignored, while
identifiers, literals, punctuation, and compound Rust/Verus operators must remain identical.
An exact mode is also available for repositories that want byte-for-byte snapshots.
-/

namespace Triptych.Verus.Drift

/-- Environment variable consumed by the Triptych elaborator's non-mutating check mode. -/
def checkEnvironmentVariable : String :=
  "TRIPTYCH_VERUS_CHECK"

/-- Stable child-process marker used by the CLI to reject sources with no `verus` clause. -/
def snapshotCurrentMessagePrefix : String :=
  "Triptych: generated Verus snapshot is current"

/-- How checked-in generated artifacts are compared with freshly generated contents. -/
inductive CompareMode where
  /-- Ignore whitespace and comments, but compare the complete Rust/Verus token stream. -/
  | syntax
  /-- Require byte-for-byte equality. -/
  | exact
  deriving Repr, Inhabited, DecidableEq

def CompareMode.description : CompareMode → String
  | .syntax => "syntax"
  | .exact => "exact"

def CompareMode.parse (value : String) : Except String CompareMode :=
  match value.toLower with
  | "syntax" => .ok .syntax
  | "exact" => .ok .exact
  | _ => .error s!"invalid {checkEnvironmentVariable} value {repr value}; expected `syntax` or \
      `exact`"

/-- Reads the private check-mode environment variable used by the CLI wrapper. -/
def modeFromEnvironment : IO (Except String (Option CompareMode)) := do
  match ← IO.getEnv checkEnvironmentVariable with
  | none => pure (.ok none)
  | some value => pure ((CompareMode.parse value).map some)

private def isIdentifierStart (character : Char) : Bool :=
  character.isAlpha || character == '_'

private def isIdentifierContinue (character : Char) : Bool :=
  character.isAlphanum || character == '_'

private def isNumberContinue (character : Char) : Bool :=
  character.isAlphanum || character == '_'

private def spanCharacters (predicate : Char → Bool) :
    List Char → List Char × List Char
  | [] => ([], [])
  | character :: rest =>
      if predicate character then
        let (taken, remaining) := spanCharacters predicate rest
        (character :: taken, remaining)
      else
        ([], character :: rest)

private def dropLineComment : List Char → List Char
  | [] => []
  | '\n' :: rest => rest
  | _ :: rest => dropLineComment rest

private def dropBlockComment (depth : Nat) : List Char → Except String (List Char)
  | [] => .error "unterminated block comment"
  | '/' :: '*' :: rest => dropBlockComment (depth + 1) rest
  | '*' :: '/' :: rest =>
      if depth == 1 then
        .ok rest
      else
        dropBlockComment (depth - 1) rest
  | _ :: rest => dropBlockComment depth rest

private def scanQuoted (quote : Char) (accumulator : List Char) :
    List Char → Except String (String × List Char)
  | [] => .error s!"unterminated {if quote == '"' then "string" else "character"} literal"
  | '\\' :: escaped :: rest =>
      scanQuoted quote (escaped :: '\\' :: accumulator) rest
  | '\\' :: [] => .error "unterminated escape sequence in literal"
  | character :: rest =>
      if character == quote then
        .ok (String.ofList ((character :: accumulator).reverse), rest)
      else
        scanQuoted quote (character :: accumulator) rest

private def consumeHashes : Nat → List Char → Option (List Char)
  | 0, rest => some rest
  | count + 1, '#' :: rest => consumeHashes count rest
  | _ + 1, _ => none

private def scanRawString (hashCount : Nat) (accumulator : List Char) :
    List Char → Except String (String × List Char)
  | [] => .error "unterminated raw string literal"
  | '"' :: rest =>
      match consumeHashes hashCount rest with
      | some remaining =>
          let closing := '"' :: List.replicate hashCount '#'
          .ok (String.ofList ((closing.reverse ++ accumulator).reverse), remaining)
      | none => scanRawString hashCount ('"' :: accumulator) rest
  | character :: rest => scanRawString hashCount (character :: accumulator) rest

private def startRawString (literalPrefix : List Char) :
    List Char → Option (Except String (String × List Char))
  | characters =>
      let (hashes, afterHashes) := spanCharacters (· == '#') characters
      match afterHashes with
      | '"' :: rest =>
          let opening := literalPrefix ++ hashes ++ ['"']
          some (scanRawString hashes.length opening.reverse rest)
      | _ => none

private def compoundOperators : List String :=
  ["<==>", "==>", "<==", "&&&", "|||", "=~=", "<<=", ">>=", "...", "..=", "::", "->",
    "=>", "==", "!=", "<=", ">=", "&&", "||", "+=", "-=", "*=", "/=", "%=", "^=", "&=",
    "|=", "<<", ">>", ".."]

private def takeCompoundOperator (characters : List Char) : Option (String × List Char) :=
  compoundOperators.findSome? fun operator =>
    let operatorCharacters := operator.toList
    if operatorCharacters.isPrefixOf characters then
      some (operator, characters.drop operatorCharacters.length)
    else
      none

private def takeIdentifier (characters : List Char) : String × List Char :=
  let (taken, remaining) := spanCharacters isIdentifierContinue characters
  (String.ofList taken, remaining)

private def takeNumber (characters : List Char) : String × List Char :=
  let (taken, remaining) := spanCharacters isNumberContinue characters
  (String.ofList taken, remaining)

private def scanLifetime (first : Char) (rest : List Char) : String × List Char :=
  let (tail, remaining) := spanCharacters isIdentifierContinue rest
  (String.ofList ('\'' :: first :: tail), remaining)

private partial def tokenizeCharacters : List Char → Except String (List String)
  | [] => .ok []
  | character :: rest =>
      if character.isWhitespace then
        tokenizeCharacters rest
      else
        match character, rest with
        | '/', '/' :: afterComment => tokenizeCharacters (dropLineComment afterComment)
        | '/', '*' :: afterComment => do
            tokenizeCharacters (← dropBlockComment 1 afterComment)
        | 'b', 'r' :: afterPrefix =>
            match startRawString ['b', 'r'] afterPrefix with
            | some result => do
                let (token, remaining) ← result
                pure (token :: (← tokenizeCharacters remaining))
            | none => do
                let (token, remaining) := takeIdentifier (character :: rest)
                pure (token :: (← tokenizeCharacters remaining))
        | 'c', 'r' :: afterPrefix =>
            match startRawString ['c', 'r'] afterPrefix with
            | some result => do
                let (token, remaining) ← result
                pure (token :: (← tokenizeCharacters remaining))
            | none => do
                let (token, remaining) := takeIdentifier (character :: rest)
                pure (token :: (← tokenizeCharacters remaining))
        | 'r', afterPrefix =>
            match startRawString ['r'] afterPrefix with
            | some result => do
                let (token, remaining) ← result
                pure (token :: (← tokenizeCharacters remaining))
            | none => do
                let (token, remaining) := takeIdentifier (character :: rest)
                pure (token :: (← tokenizeCharacters remaining))
        | 'b', '"' :: afterQuote => do
            let (token, remaining) ← scanQuoted '"' ['"', 'b'] afterQuote
            pure (token :: (← tokenizeCharacters remaining))
        | 'c', '"' :: afterQuote => do
            let (token, remaining) ← scanQuoted '"' ['"', 'c'] afterQuote
            pure (token :: (← tokenizeCharacters remaining))
        | 'b', '\'' :: afterQuote => do
            let (token, remaining) ← scanQuoted '\'' ['\'', 'b'] afterQuote
            pure (token :: (← tokenizeCharacters remaining))
        | '"', afterQuote => do
            let (token, remaining) ← scanQuoted '"' ['"'] afterQuote
            pure (token :: (← tokenizeCharacters remaining))
        | '\'', '\\' :: afterQuote => do
            let (token, remaining) ← scanQuoted '\'' ['\''] ('\\' :: afterQuote)
            pure (token :: (← tokenizeCharacters remaining))
        | '\'', quoted :: '\'' :: remaining => do
            let token := String.ofList ['\'', quoted, '\'']
            pure (token :: (← tokenizeCharacters remaining))
        | '\'', first :: afterFirst => do
            if isIdentifierStart first then
              let (token, remaining) := scanLifetime first afterFirst
              pure (token :: (← tokenizeCharacters remaining))
            else
              let (token, remaining) ← scanQuoted '\'' ['\''] (first :: afterFirst)
              pure (token :: (← tokenizeCharacters remaining))
        | _, _ => do
            if isIdentifierStart character then
              let (token, remaining) := takeIdentifier (character :: rest)
              pure (token :: (← tokenizeCharacters remaining))
            else if character.isDigit then
              let (token, remaining) := takeNumber (character :: rest)
              pure (token :: (← tokenizeCharacters remaining))
            else
              match takeCompoundOperator (character :: rest) with
              | some (token, remaining) => do
                  pure (token :: (← tokenizeCharacters remaining))
              | none => do
                  pure (String.singleton character :: (← tokenizeCharacters rest))

/-- Rust/Verus lexical tokens, with whitespace and comments outside literals removed. -/
def syntaxTokens (source : String) : Except String (List String) :=
  tokenizeCharacters source.toList

/-- The first mismatch between a freshly generated artifact and its checked-in snapshot. -/
structure Difference where
  offset : Nat
  expected : Option String
  actual : Option String
  deriving Repr, Inhabited, DecidableEq

private def firstDifferenceAux (offset : Nat) :
    List String → List String → Option Difference
  | [], [] => none
  | expected :: expectedRest, actual :: actualRest =>
      if expected == actual then
        firstDifferenceAux (offset + 1) expectedRest actualRest
      else
        some { offset, expected := some expected, actual := some actual }
  | expected :: _, [] => some { offset, expected := some expected, actual := none }
  | [], actual :: _ => some { offset, expected := none, actual := some actual }

private def firstDifference (expected actual : List String) : Option Difference :=
  firstDifferenceAux 0 expected actual

private def exactCharacters (source : String) : List String :=
  source.toList.map String.singleton

/-- Compares generated and checked-in contents according to the requested snapshot policy. -/
def compare (mode : CompareMode) (expected actual : String) :
    Except String (Option Difference) :=
  match mode with
  | .exact => .ok (firstDifference (exactCharacters expected) (exactCharacters actual))
  | .syntax => do
      let expectedTokens ← syntaxTokens expected
      let actualTokens ← syntaxTokens actual
      pure (firstDifference expectedTokens actualTokens)

private def abbreviate (value : String) : String :=
  if value.length <= 80 then value else (value.take 77).copy ++ "..."

private def describeToken : Option String → String
  | none => "<end of file>"
  | some token => reprStr (abbreviate token)

def Difference.describe (mode : CompareMode) (difference : Difference) : String :=
  let unit := if mode == .exact then "character" else "token"
  s!"first differing {unit} #{difference.offset}: expected \
      {describeToken difference.expected}, found {describeToken difference.actual}"

/--
Checks one checked-in generated file against freshly generated contents. This function never
writes the file.
-/
def checkFile (mode : CompareMode) (path : System.FilePath) (expected : String) :
    IO (Except String Unit) := do
  unless ← path.pathExists do
    return .error s!"missing generated Verus snapshot: {path}"
  let actual ← IO.FS.readFile path
  match compare mode expected actual with
  | .error message => return .error s!"cannot compare generated Verus snapshot {path}: {message}"
  | .ok none => return .ok ()
  | .ok (some difference) =>
      return .error s!"generated Verus artifact drifted: {path}\n\
        {difference.describe mode}\n\
        Regenerate it from the Triptych source after reviewing the change."

/-- Boolean convenience wrapper used by regression tests. -/
def syntaxEquivalent (left right : String) : Bool :=
  match compare .syntax left right with
  | .ok none => true
  | _ => false

end Triptych.Verus.Drift
