import Solcore.Syntax.Lexer.Character

set_option autoImplicit false

namespace Solcore.Syntax.Lexer

/-- Reverse accumulators used by the total lexer executor. -/
structure State where
  cursor : Nat
  remaining : List Char
  tokensRev : List Token := []
  commentsRev : List Comment := []
  diagnosticsRev : List LexicalDiagnostic := []
  deriving Repr, BEq

namespace State

/-- Initial state at the first UTF-8 byte of a source. -/
def initial (file : SourceFile) : State := {
  cursor := 0
  remaining := file.content.toList
}

/-- Skip a recognized slice without producing output. -/
def skipTo (state : State) (endByte : Nat)
    (remaining : List Char) : State :=
  { state with cursor := endByte, remaining }

/-- Emit one token whose start is the current cursor. -/
def emitToken (file : SourceFile) (state : State) (endByte : Nat)
    (remaining : List Char) (kind : TokenKind) : State :=
  {
    state with
    cursor := endByte
    remaining
    tokensRev := {
      span := sourceSpan file state.cursor endByte
      value := kind
    } :: state.tokensRev
  }

/-- Retain one comment while keeping it out of the token stream. -/
def emitComment (file : SourceFile) (state : State) (endByte : Nat)
    (remaining : List Char) (kind : CommentKind) (text : String) : State :=
  {
    state with
    cursor := endByte
    remaining
    commentsRev := {
      kind
      text
      span := sourceSpan file state.cursor endByte
    } :: state.commentsRev
  }

/-- Record a recoverable diagnostic and move to the next input position. -/
def recover (file : SourceFile) (state : State)
    (diagnosticStart diagnosticEnd nextByte : Nat)
    (remaining : List Char) (kind : LexicalErrorKind) : State :=
  {
    state with
    cursor := nextByte
    remaining
    diagnosticsRev := {
      span := sourceSpan file diagnosticStart diagnosticEnd
      kind
    } :: state.diagnosticsRev
  }

/-- Materialize all accumulated output in source order. -/
def finish (file : SourceFile) (state : State) : LexedFile := {
  source := file.id
  tokens := state.tokensRev.reverse
  comments := state.commentsRev.reverse
  diagnostics := state.diagnosticsRev.reverse
}

end State

end Solcore.Syntax.Lexer
