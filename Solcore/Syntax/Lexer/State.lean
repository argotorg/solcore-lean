import Solcore.Syntax.Lexer.Invariant
import Solcore.Syntax.Lexer.Contract

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

/-!
## Consolidated module: `Solcore.Syntax.Lexer.StateOrder`
-/

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

/-- Strict suffix shortening forces exact scanner progress to advance bytes. -/
theorem startByte_lt_endByte_of_remaining_length_lt
    {startByte endByte : Nat} {input remaining : List Char}
    (progress : Advances startByte input endByte remaining)
    (shorter : remaining.length < input.length) :
    startByte < endByte := by
  rcases progress with ⟨consumed, partition, endEq⟩
  have consumedNonempty : consumed ≠ [] := by
    intro empty
    subst consumed
    simp only [List.nil_append] at partition
    rw [partition] at shorter
    exact (Nat.lt_irrefl _ shorter)
  have consumedBytesPositive : 0 < byteSize consumed := by
    cases consumed with
    | nil => contradiction
    | cons character rest =>
        rw [byteSize_cons]
        exact Nat.add_pos_left character.utf8Size_pos _
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

/-- Materializing an ordered state satisfies the public lexer contract. -/
theorem finish_validFor {file : SourceFile} {state : State}
    (ordered : state.OrderedValidFor file) :
    (state.finish file).ValidFor file := by
  refine {
    source_eq := rfl
    tokens := ?_
    comments := ?_
    diagnostics := ?_
  }
  · apply SpanSequence.ValidFor.of_forall_pairwise
    · intro token member
      apply ordered.validFor.tokensRev token
      simpa only [State.finish, List.mem_reverse] using member
    · intro token _member
      exact Nat.zero_le token.span.startByte
    · intro token member
      apply ordered.tokensRev_nonempty token
      simpa only [State.finish, List.mem_reverse] using member
    · exact List.pairwise_reverse.mpr ordered.tokensRev_pairwise
  · apply SpanSequence.ValidFor.of_forall_pairwise
    · intro comment member
      apply ordered.validFor.commentsRev comment
      simpa only [State.finish, List.mem_reverse] using member
    · intro comment _member
      exact Nat.zero_le comment.span.startByte
    · intro comment member
      apply ordered.commentsRev_nonempty comment
      simpa only [State.finish, List.mem_reverse] using member
    · exact List.pairwise_reverse.mpr ordered.commentsRev_pairwise
  · intro diagnostic member
    apply ordered.validFor.diagnosticsRev diagnostic
    simpa only [State.finish, List.mem_reverse] using member

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
