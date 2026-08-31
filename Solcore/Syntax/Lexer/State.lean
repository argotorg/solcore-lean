import Solcore.Syntax.Lexer.Invariant

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

/-- Source and output-provenance invariants of one lexer executor state. -/
structure ValidFor (state : State) (file : SourceFile) : Prop where
  cursorSuffix : CursorSuffix file state.cursor state.remaining
  tokensRev : ∀ token ∈ state.tokensRev, token.span.ValidFor file
  commentsRev : ∀ comment ∈ state.commentsRev, comment.span.ValidFor file
  diagnosticsRev : ∀ diagnostic ∈ state.diagnosticsRev,
    diagnostic.span.ValidFor file

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

/-- The initial executor state satisfies every provenance invariant. -/
theorem initial_validFor (file : SourceFile) : (initial file).ValidFor file := by
  exact {
    cursorSuffix := CursorSuffix.initial file
    tokensRev := by simp [initial]
    commentsRev := by simp [initial]
    diagnosticsRev := by simp [initial]
  }

namespace ValidFor

/-- Skipping one exact source prefix preserves all state invariants. -/
theorem skipTo {file : SourceFile} {state : State}
    (valid : state.ValidFor file) (endByte : Nat)
    (remaining : List Char)
    (progress : Advances state.cursor state.remaining endByte remaining) :
    (state.skipTo endByte remaining).ValidFor file := by
  exact {
    cursorSuffix := valid.cursorSuffix.advance progress
    tokensRev := valid.tokensRev
    commentsRev := valid.commentsRev
    diagnosticsRev := valid.diagnosticsRev
  }

/-- Emitting a token after an exact scan preserves all state invariants. -/
theorem emitToken {file : SourceFile} {state : State}
    (valid : state.ValidFor file) (endByte : Nat)
    (remaining : List Char) (kind : TokenKind)
    (progress : Advances state.cursor state.remaining endByte remaining) :
    (state.emitToken file endByte remaining kind).ValidFor file := by
  have spanValid := valid.cursorSuffix.sourceSpan_validFor progress
  exact {
    cursorSuffix := valid.cursorSuffix.advance progress
    tokensRev := by
      intro token member
      rcases List.mem_cons.mp member with rfl | member
      · exact spanValid
      · exact valid.tokensRev token member
    commentsRev := valid.commentsRev
    diagnosticsRev := valid.diagnosticsRev
  }

/-- Emitting a comment after an exact scan preserves all state invariants. -/
theorem emitComment {file : SourceFile} {state : State}
    (valid : state.ValidFor file) (endByte : Nat)
    (remaining : List Char) (kind : CommentKind) (text : String)
    (progress : Advances state.cursor state.remaining endByte remaining) :
    (state.emitComment file endByte remaining kind text).ValidFor file := by
  have spanValid := valid.cursorSuffix.sourceSpan_validFor progress
  exact {
    cursorSuffix := valid.cursorSuffix.advance progress
    tokensRev := valid.tokensRev
    commentsRev := by
      intro comment member
      rcases List.mem_cons.mp member with rfl | member
      · exact spanValid
      · exact valid.commentsRev comment member
    diagnosticsRev := valid.diagnosticsRev
  }

/-- Recovering to an exact suffix preserves valid retained and new spans. -/
theorem recover {file : SourceFile} {state : State}
    (valid : state.ValidFor file)
    (diagnosticStart diagnosticEnd nextByte : Nat)
    (remaining : List Char) (kind : LexicalErrorKind)
    (progress : Advances state.cursor state.remaining nextByte remaining)
    (diagnosticValid :
      (sourceSpan file diagnosticStart diagnosticEnd).ValidFor file) :
    State.ValidFor
      (state.recover file diagnosticStart diagnosticEnd nextByte remaining kind)
      file := by
  exact {
    cursorSuffix := valid.cursorSuffix.advance progress
    tokensRev := valid.tokensRev
    commentsRev := valid.commentsRev
    diagnosticsRev := by
      intro diagnostic member
      rcases List.mem_cons.mp member with rfl | member
      · exact diagnosticValid
      · exact valid.diagnosticsRev diagnostic member
  }

/--
Finishing a valid state retains source identity and valid spans for every
exposed token, comment, and diagnostic.
-/
theorem finish {file : SourceFile} {state : State}
    (valid : state.ValidFor file) :
    let lexed := state.finish file
    lexed.source = file.id ∧
      (∀ token ∈ lexed.tokens, token.span.ValidFor file) ∧
      (∀ comment ∈ lexed.comments, comment.span.ValidFor file) ∧
      (∀ diagnostic ∈ lexed.diagnostics,
        diagnostic.span.ValidFor file) := by
  dsimp only
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro token member
    apply valid.tokensRev token
    simpa only [State.finish, List.mem_reverse] using member
  · intro comment member
    apply valid.commentsRev comment
    simpa only [State.finish, List.mem_reverse] using member
  · intro diagnostic member
    apply valid.diagnosticsRev diagnostic
    simpa only [State.finish, List.mem_reverse] using member

end ValidFor

end State

end Solcore.Syntax.Lexer
