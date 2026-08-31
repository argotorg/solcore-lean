import Solcore.Syntax.Lexer.State

/-! Source-order invariants for the lexer's reverse accumulators. -/

set_option autoImplicit false

namespace Solcore.Syntax.Lexer

namespace Advances

/-- Exact scanner progress never moves its cursor backwards. -/
theorem startByte_le_endByte {startByte endByte : Nat}
    {input remaining : List Char}
    (progress : Advances startByte input endByte remaining) :
    startByte ≤ endByte := by
  rcases progress with ⟨consumed, _partition, endEq⟩
  rw [endEq]
  omega

end Advances

namespace State

/--
Valid lexer state whose retained tokens and comments are nonempty and ordered.
The reverse-list relation reads "the older span ends before the newer begins".
-/
structure OrderedValidFor (state : State) (file : SourceFile) : Prop where
  validFor : state.ValidFor file
  tokensRev_nonempty : ∀ token ∈ state.tokensRev,
    token.span.startByte < token.span.endByte
  tokensRev_end_le_cursor : ∀ token ∈ state.tokensRev,
    token.span.endByte ≤ state.cursor
  tokensRev_pairwise : state.tokensRev.Pairwise fun newer older =>
    older.span.endByte ≤ newer.span.startByte
  commentsRev_nonempty : ∀ comment ∈ state.commentsRev,
    comment.span.startByte < comment.span.endByte
  commentsRev_end_le_cursor : ∀ comment ∈ state.commentsRev,
    comment.span.endByte ≤ state.cursor
  commentsRev_pairwise : state.commentsRev.Pairwise fun newer older =>
    older.span.endByte ≤ newer.span.startByte

/-- The empty initial accumulators satisfy every ordering invariant. -/
theorem initial_orderedValidFor (file : SourceFile) :
    (initial file).OrderedValidFor file := by
  exact {
    validFor := initial_validFor file
    tokensRev_nonempty := by simp [initial]
    tokensRev_end_le_cursor := by simp [initial]
    tokensRev_pairwise := by simp [initial]
    commentsRev_nonempty := by simp [initial]
    commentsRev_end_le_cursor := by simp [initial]
    commentsRev_pairwise := by simp [initial]
  }

namespace OrderedValidFor

/-- Exact cursor-only progress preserves reverse-accumulator ordering. -/
theorem skipTo {file : SourceFile} {state : State}
    (ordered : state.OrderedValidFor file) (endByte : Nat)
    (remaining : List Char)
    (progress : Advances state.cursor state.remaining endByte remaining) :
    (state.skipTo endByte remaining).OrderedValidFor file := by
  have cursorLe := progress.startByte_le_endByte
  exact {
    validFor := ordered.validFor.skipTo endByte remaining progress
    tokensRev_nonempty := ordered.tokensRev_nonempty
    tokensRev_end_le_cursor := by
      intro token member
      exact Nat.le_trans (ordered.tokensRev_end_le_cursor token member) cursorLe
    tokensRev_pairwise := ordered.tokensRev_pairwise
    commentsRev_nonempty := ordered.commentsRev_nonempty
    commentsRev_end_le_cursor := by
      intro comment member
      exact Nat.le_trans
        (ordered.commentsRev_end_le_cursor comment member) cursorLe
    commentsRev_pairwise := ordered.commentsRev_pairwise
  }

/--
Emitting one strictly advancing token preserves nonempty, ordered token spans.
-/
theorem emitToken {file : SourceFile} {state : State}
    (ordered : state.OrderedValidFor file) (endByte : Nat)
    (remaining : List Char) (kind : TokenKind)
    (progress : Advances state.cursor state.remaining endByte remaining)
    (strict : state.cursor < endByte) :
    (state.emitToken file endByte remaining kind).OrderedValidFor file := by
  exact {
    validFor := ordered.validFor.emitToken endByte remaining kind progress
    tokensRev_nonempty := by
      intro token member
      simp only [State.emitToken, List.mem_cons] at member
      rcases member with rfl | member
      · exact strict
      · exact ordered.tokensRev_nonempty token member
    tokensRev_end_le_cursor := by
      intro token member
      simp only [State.emitToken, List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.le_refl _
      · exact Nat.le_trans
          (ordered.tokensRev_end_le_cursor token member)
          (Nat.le_of_lt strict)
    tokensRev_pairwise := by
      simp only [State.emitToken]
      apply List.Pairwise.cons
      · intro token member
        exact ordered.tokensRev_end_le_cursor token member
      · exact ordered.tokensRev_pairwise
    commentsRev_nonempty := ordered.commentsRev_nonempty
    commentsRev_end_le_cursor := by
      intro comment member
      exact Nat.le_trans
        (ordered.commentsRev_end_le_cursor comment member)
        (Nat.le_of_lt strict)
    commentsRev_pairwise := ordered.commentsRev_pairwise
  }

/--
Emitting one strictly advancing comment preserves nonempty, ordered comments.
-/
theorem emitComment {file : SourceFile} {state : State}
    (ordered : state.OrderedValidFor file) (endByte : Nat)
    (remaining : List Char) (kind : CommentKind) (text : String)
    (progress : Advances state.cursor state.remaining endByte remaining)
    (strict : state.cursor < endByte) :
    (state.emitComment file endByte remaining kind text).OrderedValidFor file := by
  exact {
    validFor := ordered.validFor.emitComment
      endByte remaining kind text progress
    tokensRev_nonempty := ordered.tokensRev_nonempty
    tokensRev_end_le_cursor := by
      intro token member
      exact Nat.le_trans
        (ordered.tokensRev_end_le_cursor token member)
        (Nat.le_of_lt strict)
    tokensRev_pairwise := ordered.tokensRev_pairwise
    commentsRev_nonempty := by
      intro comment member
      simp only [State.emitComment, List.mem_cons] at member
      rcases member with rfl | member
      · exact strict
      · exact ordered.commentsRev_nonempty comment member
    commentsRev_end_le_cursor := by
      intro comment member
      simp only [State.emitComment, List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.le_refl _
      · exact Nat.le_trans
          (ordered.commentsRev_end_le_cursor comment member)
          (Nat.le_of_lt strict)
    commentsRev_pairwise := by
      simp only [State.emitComment]
      apply List.Pairwise.cons
      · intro comment member
        exact ordered.commentsRev_end_le_cursor comment member
      · exact ordered.commentsRev_pairwise
  }

/-- Recovery advances retained carrier bounds without changing their order. -/
theorem recover {file : SourceFile} {state : State}
    (ordered : state.OrderedValidFor file)
    (diagnosticStart diagnosticEnd nextByte : Nat)
    (remaining : List Char) (kind : LexicalErrorKind)
    (progress : Advances state.cursor state.remaining nextByte remaining)
    (diagnosticValid :
      (sourceSpan file diagnosticStart diagnosticEnd).ValidFor file) :
    State.OrderedValidFor
      (state.recover file diagnosticStart diagnosticEnd nextByte remaining kind)
      file := by
  have cursorLe := progress.startByte_le_endByte
  exact {
    validFor := ordered.validFor.recover diagnosticStart diagnosticEnd
      nextByte remaining kind progress diagnosticValid
    tokensRev_nonempty := ordered.tokensRev_nonempty
    tokensRev_end_le_cursor := by
      intro token member
      exact Nat.le_trans (ordered.tokensRev_end_le_cursor token member) cursorLe
    tokensRev_pairwise := ordered.tokensRev_pairwise
    commentsRev_nonempty := ordered.commentsRev_nonempty
    commentsRev_end_le_cursor := by
      intro comment member
      exact Nat.le_trans
        (ordered.commentsRev_end_le_cursor comment member) cursorLe
    commentsRev_pairwise := ordered.commentsRev_pairwise
  }

end OrderedValidFor

end State

end Solcore.Syntax.Lexer
