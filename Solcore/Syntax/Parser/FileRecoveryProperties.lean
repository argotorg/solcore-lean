import Solcore.Syntax.Parser.File
import Solcore.Syntax.CoreTermValidity
import Solcore.Syntax.FileValidity

/-! Contracts for canonical top-level error recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

private theorem advance?_state_shape {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    input.peek? = some token ∧
      next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      exact ⟨rfl, rfl⟩

/-- Canonical provenance retained by recovered top-level items. -/
abbrev RecoveredTopItemValid :=
  TopItem.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor

/-- Finishing recovery retains one source-valid error item. -/
theorem finishRecoveredTopItem_validFor
    (first last : SourceSpan) (state : State)
    (stateValid : state.ValidFor)
    (firstValid : first.ValidFor state.file)
    (lastValid : last.ValidFor state.file)
    (ordered : first.startByte ≤ last.endByte) :
    (finishRecoveredTopItem first last state).ValidFor state
      RecoveredTopItemValid := by
  have spanValid := SourceSpan.cover_validFor firstValid lastValid ordered
  unfold finishRecoveredTopItem Reply.ValidFor
  exact ⟨.error spanValid (by simp),
    stateValid.emit_validFor _ spanValid, rfl⟩

/-- Fuel-bounded recovery preserves provenance while consuming malformed
top-level tokens. -/
theorem recoverTopItemAux_validFor (first : SourceSpan) :
    ∀ fuel last state lastIndex lastToken,
      state.ValidFor → first.ValidFor state.file →
      last.ValidFor state.file → first.startByte ≤ last.endByte →
      state.tokens[lastIndex]? = some lastToken → lastToken.span = last →
      lastIndex < state.cursor →
      (recoverTopItemAux first last fuel state).ValidFor state
        RecoveredTopItemValid := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last state lastIndex lastToken stateValid firstValid lastValid
        ordered lastFound lastSpan lastBefore
      unfold recoverTopItemAux
      split
      · exact finishRecoveredTopItem_validFor first last state stateValid
          firstValid lastValid ordered
      · cases advanced : state.advance? with
        | none =>
            exact finishRecoveredTopItem_validFor first last state stateValid
              firstValid lastValid ordered
        | some pair =>
            rcases pair with ⟨token, next⟩
            have shape := advance?_state_shape advanced
            have nextValid := stateValid.advance?_validFor advanced
            have tokenValid := stateValid.peek?_span_validFor shape.1
            have currentFound :=
              State.getElem?_eq_some_of_peek?_eq_some shape.1
            have lastBeforeCurrent :=
              stateValid.token_end_le_token_start_of_getElem?_lt lastFound
                currentFound lastBefore
            exact (inductionHypothesis token.span next state.cursor token
              nextValid (by simpa [shape.2] using firstValid)
              (by simpa [shape.2] using tokenValid)
              (Nat.le_trans ordered (Nat.le_trans
                (by simpa [lastSpan] using lastBeforeCurrent)
                tokenValid.2.1))
              (by simpa [shape.2] using currentFound) rfl
              (by simp [shape.2])).of_file_eq (by simp [shape.2])

/-- Complete top-level recovery preserves canonical source provenance. -/
theorem recoverTopItem_validFor :
    Parser.ValidFor recoverTopItem RecoveredTopItemValid := by
  intro input inputValid
  unfold recoverTopItem
  cases advanced : input.advance? with
  | none =>
      unfold rejectAt Reply.ValidFor
      exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩
  | some pair =>
      rcases pair with ⟨token, next⟩
      have shape := advance?_state_shape advanced
      have nextValid := inputValid.advance?_validFor advanced
      have tokenValid := inputValid.peek?_span_validFor shape.1
      have currentFound := State.getElem?_eq_some_of_peek?_eq_some shape.1
      exact (recoverTopItemAux_validFor token.span
        (next.remainingCount + 1) token.span next input.cursor token nextValid
        (by simpa [shape.2] using tokenValid)
        (by simpa [shape.2] using tokenValid) tokenValid.2.1
        (by simpa [shape.2] using currentFound) rfl
        (by simp [shape.2])).of_file_eq (by simp [shape.2])

/-- Finishing recovery preserves the immutable token window. -/
theorem finishRecoveredTopItem_preservesTokenWindow
    (first last : SourceSpan) :
    Parser.PreservesTokenWindow (finishRecoveredTopItem first last) := by
  intro input
  unfold finishRecoveredTopItem Reply.PreservesTokenWindow State.emit
  exact ⟨rfl, rfl⟩

/-- Fuel-bounded recovery preserves the complete token window. -/
theorem recoverTopItemAux_preservesTokenWindow
    (first last : SourceSpan) (fuel : Nat) :
    Parser.PreservesTokenWindow (recoverTopItemAux first last fuel) := by
  intro input
  induction fuel generalizing last input with
  | zero => trivial
  | succ fuel inductionHypothesis =>
      unfold recoverTopItemAux
      split
      · exact finishRecoveredTopItem_preservesTokenWindow first last input
      · cases advanced : input.advance? with
        | none =>
            exact finishRecoveredTopItem_preservesTokenWindow first last input
        | some pair =>
            rcases pair with ⟨token, next⟩
            exact (inductionHypothesis token.span next).trans (by
              simp [(advance?_state_shape advanced).2])

theorem recoverTopItemAux_preservesTokensOnSuccess
    (first last : SourceSpan) (fuel : Nat) :
    Parser.PreservesTokensOnSuccess (recoverTopItemAux first last fuel) :=
  (recoverTopItemAux_preservesTokenWindow first last fuel).preservesTokensOnSuccess

/-- A successful auxiliary recovery is monotone and retains its first span. -/
theorem recoverTopItemAux_ok_state_shape (first last : SourceSpan) :
    ∀ fuel, ∀ {input final : State} {item : TopItem},
      recoverTopItemAux first last fuel input = .ok item final →
      input.cursor ≤ final.cursor ∧
        first.startByte = item.span.startByte := by
  intro fuel
  induction fuel generalizing last with
  | zero => simp [recoverTopItemAux]
  | succ fuel inductionHypothesis =>
      intro input final item parsed
      unfold recoverTopItemAux at parsed
      split at parsed
      · unfold finishRecoveredTopItem at parsed
        cases parsed
        exact ⟨Nat.le_refl _, rfl⟩
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at parsed
            unfold finishRecoveredTopItem at parsed
            cases parsed
            exact ⟨Nat.le_refl _, rfl⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at parsed
            have recursive := inductionHypothesis token.span parsed
            exact ⟨Nat.le_trans (by
              simp [(advance?_state_shape advanced).2]) recursive.1,
              recursive.2⟩

theorem recoverTopItemAux_cursorMonotoneOnSuccess
    (first last : SourceSpan) (fuel : Nat) :
    Parser.CursorMonotoneOnSuccess (recoverTopItemAux first last fuel) :=
  fun _ _ _ parsed =>
    (recoverTopItemAux_ok_state_shape first last fuel parsed).1

/-- Complete recovery preserves the ordinary token window. -/
theorem recoverTopItem_preservesTokenWindow :
    Parser.PreservesTokenWindow recoverTopItem := by
  intro input
  unfold recoverTopItem
  cases advanced : input.advance? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some pair =>
      rcases pair with ⟨token, next⟩
      exact (recoverTopItemAux_preservesTokenWindow token.span token.span
        (next.remainingCount + 1) next).trans (by
          simp [(advance?_state_shape advanced).2])

theorem recoverTopItem_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess recoverTopItem :=
  recoverTopItem_preservesTokenWindow.preservesTokensOnSuccess

/-- Complete recovery is monotone and starts at its consumed token. -/
theorem recoverTopItem_ok_state_shape {input final : State} {item : TopItem}
    (parsed : recoverTopItem input = .ok item final) :
    input.cursor ≤ final.cursor ∧
      ∃ token, input.peek? = some token ∧
        token.span.startByte = item.span.startByte := by
  unfold recoverTopItem at parsed
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at parsed
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at parsed
      have recovered := recoverTopItemAux_ok_state_shape token.span token.span
        (next.remainingCount + 1) parsed
      exact ⟨Nat.le_trans (by simp [(advance?_state_shape advanced).2])
        recovered.1, token, (advance?_state_shape advanced).1, recovered.2⟩

/-- Successful complete recovery strictly consumes its first malformed token. -/
theorem recoverTopItem_cursor_lt_onSuccess
    {input final : State} {item : TopItem}
    (parsed : recoverTopItem input = .ok item final) :
    input.cursor < final.cursor := by
  unfold recoverTopItem at parsed
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at parsed
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at parsed
      exact Nat.lt_of_lt_of_le (by simp [(advance?_state_shape advanced).2])
        (recoverTopItemAux_ok_state_shape token.span token.span
          (next.remainingCount + 1) parsed).1

theorem recoverTopItem_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess recoverTopItem :=
  fun _ _ _ parsed => Nat.le_of_lt (recoverTopItem_cursor_lt_onSuccess parsed)

theorem recoverTopItem_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess recoverTopItem (·.span) :=
  fun _ _ _ parsed => (recoverTopItem_ok_state_shape parsed).2

/-- Every successful auxiliary recovery commits a recovery diagnostic. -/
theorem recoverTopItemAux_diagnostics_ne_nil_onSuccess
    (first last : SourceSpan) :
    ∀ fuel, ∀ {input next : State} {item : TopItem},
      recoverTopItemAux first last fuel input = .ok item next →
      next.diagnosticsRev ≠ [] := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      simp [recoverTopItemAux]
  | succ fuel inductionHypothesis =>
      intro input next item parsed
      unfold recoverTopItemAux at parsed
      split at parsed
      · unfold finishRecoveredTopItem at parsed
        cases parsed
        simp [State.emit]
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at parsed
            unfold finishRecoveredTopItem at parsed
            cases parsed
            simp [State.emit]
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at parsed
            exact inductionHypothesis token.span parsed

/-- Every successful complete recovery commits a recovery diagnostic. -/
theorem recoverTopItem_diagnostics_ne_nil_onSuccess
    {input next : State} {item : TopItem}
    (parsed : recoverTopItem input = .ok item next) :
    next.diagnosticsRev ≠ [] := by
  unfold recoverTopItem at parsed
  cases advanced : input.advance? with
  | none =>
      simp [advanced, rejectAt] at parsed
  | some pair =>
      rcases pair with ⟨token, afterToken⟩
      simp only [advanced] at parsed
      exact recoverTopItemAux_diagnostics_ne_nil_onSuccess token.span
        token.span (afterToken.remainingCount + 1) parsed

end Solcore.Syntax.Parser.FileInternals
