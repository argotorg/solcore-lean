import Solcore.Syntax.Lexer.Properties

/-! External compile consumers for canonical lexer state invariants. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Lexer

example (file : SourceFile) :
    (State.initial file).ValidFor file :=
  State.initial_validFor file

example (file : SourceFile) (state : State) (endByte : Nat)
    (remaining : List Char) (valid : state.ValidFor file)
    (progress : Advances state.cursor state.remaining endByte remaining) :
    (state.skipTo endByte remaining).ValidFor file :=
  valid.skipTo endByte remaining progress

example (file : SourceFile) (state : State) (endByte : Nat)
    (remaining : List Char) (kind : TokenKind)
    (valid : state.ValidFor file)
    (progress : Advances state.cursor state.remaining endByte remaining) :
    (state.emitToken file endByte remaining kind).ValidFor file :=
  valid.emitToken endByte remaining kind progress

example (file : SourceFile) (state : State) (endByte : Nat)
    (remaining : List Char) (kind : CommentKind) (text : String)
    (valid : state.ValidFor file)
    (progress : Advances state.cursor state.remaining endByte remaining) :
    (state.emitComment file endByte remaining kind text).ValidFor file :=
  valid.emitComment endByte remaining kind text progress

example (file : SourceFile) (state : State)
    (diagnosticStart diagnosticEnd nextByte : Nat)
    (remaining : List Char) (kind : LexicalErrorKind)
    (valid : state.ValidFor file)
    (progress : Advances state.cursor state.remaining nextByte remaining)
    (diagnosticValid :
      (sourceSpan file diagnosticStart diagnosticEnd).ValidFor file) :
    State.ValidFor
      (state.recover file diagnosticStart diagnosticEnd nextByte remaining kind)
      file :=
  valid.recover diagnosticStart diagnosticEnd nextByte remaining kind progress
    diagnosticValid

example (file : SourceFile) (state : State) (valid : state.ValidFor file) :
    let lexed := state.finish file
    lexed.source = file.id ∧
      (∀ token ∈ lexed.tokens, token.span.ValidFor file) ∧
      (∀ comment ∈ lexed.comments, comment.span.ValidFor file) ∧
      (∀ diagnostic ∈ lexed.diagnostics,
        diagnostic.span.ValidFor file) :=
  valid.finish

example (file : SourceFile) (state : State) (valid : state.ValidFor file) :
    (step file state).ValidFor file :=
  step_validFor file state valid

example (file : SourceFile) (lexed : LexedFile)
    (result : lex file = .ok lexed) :
    lexed.source = file.id ∧
      (∀ token ∈ lexed.tokens, token.span.ValidFor file) ∧
      (∀ comment ∈ lexed.comments, comment.span.ValidFor file) ∧
      (∀ diagnostic ∈ lexed.diagnostics,
        diagnostic.span.ValidFor file) :=
  lex_ok_carrier_spans file lexed result

end Tests
