import Solcore.Syntax.Lexer.Result

set_option autoImplicit false

namespace Solcore.Syntax.Lexer

/-- Complete scan of a `//` body, stopping before LF. -/
structure LineCommentScan where
  endByte : Nat
  body : List Char
  remaining : List Char
  deriving Repr, BEq

/-- Scan source characters after the opening `//`. -/
def scanLineComment : Nat → List Char → LineCommentScan
  | cursor, [] => {
      endByte := cursor
      body := []
      remaining := []
    }
  | cursor, characters@('\n' :: _) => {
      endByte := cursor
      body := []
      remaining := characters
    }
  | cursor, character :: rest =>
      let tail := scanLineComment (cursor + character.utf8Size) rest
      { tail with body := character :: tail.body }

/-- Complete outcome of a nested `/* ... */` scan. -/
inductive BlockCommentScan where
  | closed
      (endByte : Nat)
      (body : List Char)
      (remaining : List Char)
  | unterminated
  deriving Repr, BEq

/--
Scan after an outer `/*`. Nested delimiters remain in the returned body; only
the outer delimiters are excluded.
-/
def scanBlockComment : Nat → Nat → List Char → List Char → BlockCommentScan
  | _, _, [], _ => .unterminated
  | cursor, depth, '/' :: '*' :: rest, bodyRev =>
      scanBlockComment (cursor + 2) (depth + 1) rest ('*' :: '/' :: bodyRev)
  | cursor, 1, '*' :: '/' :: rest, bodyRev =>
      .closed (cursor + 2) bodyRev.reverse rest
  | cursor, depth + 2, '*' :: '/' :: rest, bodyRev =>
      scanBlockComment (cursor + 2) (depth + 1) rest ('/' :: '*' :: bodyRev)
  | cursor, depth, character :: rest, bodyRev =>
      scanBlockComment
        (cursor + character.utf8Size) depth rest (character :: bodyRev)

/-- Complete outcome of a strict quoted-string scan. -/
inductive StringScan where
  | closed
      (endByte : Nat)
      (spelling : String)
      (decoded : String)
      (remaining : List Char)
  | invalidEscape
      (startByte : Nat)
      (endByte : Nat)
      (escape : Option Char)
  | unterminated
  deriving Repr, BEq

/-- Scan after an opening quote, retaining spelling and decoded value. -/
def scanString : Nat → List Char → List Char → List Char → StringScan
  | _, [], _, _ => .unterminated
  | cursor, '"' :: rest, spellingRev, decodedRev =>
      .closed
        (cursor + 1)
        (String.ofList ('"' :: spellingRev).reverse)
        (String.ofList decodedRev.reverse)
        rest
  | cursor, '\\' :: [], _, _ =>
      .invalidEscape cursor (cursor + 1) none
  | cursor, '\\' :: escaped :: rest, spellingRev, decodedRev =>
      let decoded? :=
        match escaped with
        | 'n' => some '\n'
        | 't' => some '\t'
        | '"' => some '"'
        | '\\' => some '\\'
        | _ => none
      match decoded? with
      | none =>
          .invalidEscape cursor (cursor + 1 + escaped.utf8Size) (some escaped)
      | some decoded =>
          scanString
            (cursor + 1 + escaped.utf8Size)
            rest
            (escaped :: '\\' :: spellingRev)
            (decoded :: decodedRev)
  | cursor, character :: rest, spellingRev, decodedRev =>
      scanString
        (cursor + character.utf8Size)
        rest
        (character :: spellingRev)
        (character :: decodedRev)

/-- Start a quoted-string scan with the already-consumed opening quote. -/
def scanQuotedString (startByte : Nat) (remaining : List Char) : StringScan :=
  scanString (startByte + 1) remaining ['"'] []

/-- Complete delimited-meta scan used for rejected Yul antiquotes. -/
structure MetaScan where
  endByte : Nat
  spelling : String
  remaining : List Char
  deriving Repr, BEq

/-- Scan through the first requested closing character. -/
def scanDelimitedMeta :
    Char → Nat → List Char → List Char → Option MetaScan
  | _, _, [], _ => none
  | closing, cursor, character :: rest, spellingRev =>
      let nextRev := character :: spellingRev
      let nextByte := cursor + character.utf8Size
      if character == closing then
        some {
          endByte := nextByte
          spelling := String.ofList nextRev.reverse
          remaining := rest
        }
      else
        scanDelimitedMeta closing nextByte rest nextRev

end Solcore.Syntax.Lexer
