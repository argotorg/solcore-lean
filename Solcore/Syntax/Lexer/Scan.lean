import Solcore.Syntax.Lexer.Result

set_option autoImplicit false

namespace Solcore.Syntax.Lexer

/-- Complete scan of a `//` body, stopping before LF. -/
structure LineCommentScan where
  endByte : Nat
  body : List Char
  remaining : List Char
  deriving Repr, BEq

/-- Tail-recursive scan source characters after the opening `//`. -/
private def scanLineCommentRev :
    Nat → List Char → List Char → LineCommentScan
  | cursor, [], bodyRev => {
      endByte := cursor
      body := bodyRev.reverse
      remaining := []
    }
  | cursor, characters@('\n' :: _), bodyRev => {
      endByte := cursor
      body := bodyRev.reverse
      remaining := characters
    }
  | cursor, character :: rest, bodyRev =>
      scanLineCommentRev
        (cursor + character.utf8Size) rest (character :: bodyRev)

def scanLineComment (cursor : Nat) (characters : List Char) : LineCommentScan :=
  scanLineCommentRev cursor characters []

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
      (tokenEndByte : Nat)
      (remaining : List Char)
  | invalidPrefix
      (endByte : Nat)
      (remaining : List Char)
  | unterminated
  deriving Repr, BEq

/-- Scan after an opening quote, retaining spelling and decoded value. -/
def scanString :
    Nat → List Char → List Char → List Char →
      Option (Nat × Nat × Option Char) → StringScan
  | _, [], _, _, _ => .unterminated
  | cursor, '"' :: rest, spellingRev, decodedRev, invalid =>
      match invalid with
      | some (startByte, endByte, escape) =>
          .invalidEscape startByte endByte escape (cursor + 1) rest
      | none =>
          .closed
            (cursor + 1)
            (String.ofList ('"' :: spellingRev).reverse)
            (String.ofList decodedRev.reverse)
            rest
  | _, '\\' :: [], _, _, _ => .unterminated
  | cursor, '\\' :: characters@('\n' :: _), _, _, _ =>
      .invalidPrefix (cursor + 1) characters
  | cursor, '\\' :: escaped :: rest, spellingRev, decodedRev, invalid =>
      let decoded? :=
        match escaped with
        | 'n' => some '\n'
        | 't' => some '\t'
        | '"' => some '"'
        | '\\' => some '\\'
        | _ => none
      let nextInvalid :=
        match invalid, decoded? with
        | some prior, _ => some prior
        | none, none =>
            some (cursor, cursor + 1 + escaped.utf8Size, some escaped)
        | none, some _ => none
      let nextDecodedRev :=
        match decoded? with
        | some decoded => decoded :: decodedRev
        | none => decodedRev
      scanString
        (cursor + 1 + escaped.utf8Size)
        rest
        (escaped :: '\\' :: spellingRev)
        nextDecodedRev
        nextInvalid
  | cursor, character :: rest, spellingRev, decodedRev, invalid =>
      scanString
        (cursor + character.utf8Size)
        rest
        (character :: spellingRev)
        (character :: decodedRev)
        invalid

/-- Start a quoted-string scan with the already-consumed opening quote. -/
def scanQuotedString (startByte : Nat) (remaining : List Char) : StringScan :=
  scanString (startByte + 1) remaining ['"'] [] none

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
