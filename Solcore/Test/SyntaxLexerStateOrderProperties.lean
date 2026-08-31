import Solcore.Syntax.Lexer.Step

/-! External compile consumers for reverse-accumulator source ordering. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Lexer

example (file : SourceFile) :
    (State.initial file).OrderedValidFor file :=
  State.initial_orderedValidFor file

example (file : SourceFile) (state : State)
    (ordered : state.OrderedValidFor file) :
    (step file state).OrderedValidFor file :=
  step_orderedValidFor file state ordered

example (file : SourceFile) (state : State)
    (ordered : state.OrderedValidFor file) :
    state.tokensRev.Pairwise fun newer older =>
      older.span.endByte ≤ newer.span.startByte :=
  ordered.tokensRev_pairwise

example (file : SourceFile) (state : State) (endByte : Nat)
    (remaining : List Char) (ordered : state.OrderedValidFor file)
    (progress : Advances state.cursor state.remaining endByte remaining) :
    (state.skipTo endByte remaining).OrderedValidFor file :=
  ordered.skipTo endByte remaining progress

example (file : SourceFile) (state : State) (endByte : Nat)
    (remaining : List Char) (kind : TokenKind)
    (ordered : state.OrderedValidFor file)
    (progress : Advances state.cursor state.remaining endByte remaining)
    (strict : state.cursor < endByte) :
    (state.emitToken file endByte remaining kind).OrderedValidFor file :=
  ordered.emitToken endByte remaining kind progress strict

example (file : SourceFile) (state : State) (endByte : Nat)
    (remaining : List Char) (kind : CommentKind) (text : String)
    (ordered : state.OrderedValidFor file)
    (progress : Advances state.cursor state.remaining endByte remaining)
    (strict : state.cursor < endByte) :
    (state.emitComment file endByte remaining kind text).OrderedValidFor file :=
  ordered.emitComment endByte remaining kind text progress strict

example (file : SourceFile) (state : State)
    (diagnosticStart diagnosticEnd nextByte : Nat)
    (remaining : List Char) (kind : LexicalErrorKind)
    (ordered : state.OrderedValidFor file)
    (progress : Advances state.cursor state.remaining nextByte remaining)
    (diagnosticValid :
      (sourceSpan file diagnosticStart diagnosticEnd).ValidFor file) :
    State.OrderedValidFor
      (state.recover file diagnosticStart diagnosticEnd nextByte remaining kind)
      file :=
  ordered.recover diagnosticStart diagnosticEnd nextByte remaining kind
    progress diagnosticValid

end Tests
