import Solcore.Syntax.Declaration

set_option autoImplicit false

namespace Solcore.Syntax

/-- Closed lexical failure catalog of the canonical source lexer. -/
inductive LexicalErrorKind where
  | invalidCharacter (character : Char)
  | unterminatedBlockComment
  | invalidStringEscape (escape : Option Char)
  | internalFuelExhausted
  deriving Repr, BEq, DecidableEq

/-- One deterministic lexical failure at its exact source range. -/
structure LexicalDiagnostic where
  span : SourceSpan
  kind : LexicalErrorKind
  deriving Repr, BEq, DecidableEq

/-- Successful lexical output in source order. Comments are parser trivia. -/
structure LexedFile where
  source : SourceId
  tokens : List Token
  comments : List Comment
  deriving Repr, BEq, DecidableEq

/-- Total public result of canonical lexical analysis. -/
abbrev LexResult := Except LexicalDiagnostic LexedFile

namespace Lexer

/-- Construct a half-open span owned by the source being scanned. -/
def sourceSpan (file : SourceFile) (startByte endByte : Nat) : SourceSpan := {
  source := file.id
  startByte
  endByte
}

/-- UTF-8 byte size of an executor character slice. -/
def byteSize (characters : List Char) : Nat :=
  (String.ofList characters).utf8ByteSize

/-- The executable lexer performs at most one main transition per character. -/
def fuelBound (file : SourceFile) : Nat :=
  file.content.length + 1

end Lexer

end Solcore.Syntax
