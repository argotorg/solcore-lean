import Solcore.Syntax.Parser.Contract
import Solcore.Syntax.CoreTermValidity
import Solcore.Syntax.ContractDeclarationValidity

/-! Contracts for canonical contract-member error recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

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

abbrev RecoveredContractMemberValid :=
  ContractMember.ValidFor CoreStatement.ValidFor
    (Expr.ValidFor CoreStatement.ValidFor)

theorem finishRecoveredMember_validFor
    (first last : SourceSpan) (state : State)
    (stateValid : state.ValidFor)
    (firstValid : first.ValidFor state.file)
    (lastValid : last.ValidFor state.file)
    (ordered : first.startByte ≤ last.endByte) :
    (finishRecoveredMember first last state).ValidFor state
      RecoveredContractMemberValid := by
  have spanValid := SourceSpan.cover_validFor firstValid lastValid ordered
  unfold finishRecoveredMember Reply.ValidFor
  exact ⟨.error spanValid (by simp),
    stateValid.emit_validFor _ spanValid, rfl⟩

theorem recoverContractMemberAux_validFor (first : SourceSpan) :
    ∀ fuel last state lastIndex lastToken,
      state.ValidFor → first.ValidFor state.file →
      last.ValidFor state.file → first.startByte ≤ last.endByte →
      state.tokens[lastIndex]? = some lastToken → lastToken.span = last →
      lastIndex < state.cursor →
      (recoverContractMemberAux first last fuel state).ValidFor state
        RecoveredContractMemberValid := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last state lastIndex lastToken stateValid firstValid lastValid
        ordered lastFound lastSpan lastBefore
      unfold recoverContractMemberAux
      split
      · exact finishRecoveredMember_validFor first last state stateValid
          firstValid lastValid ordered
      · cases advanced : state.advance? with
        | none =>
            exact finishRecoveredMember_validFor first last state stateValid
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

theorem recoverContractMember_validFor :
    Parser.ValidFor recoverContractMember RecoveredContractMemberValid := by
  intro input inputValid
  unfold recoverContractMember
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
      exact (recoverContractMemberAux_validFor token.span
        (next.remainingCount + 1) token.span next input.cursor token nextValid
        (by simpa [shape.2] using tokenValid)
        (by simpa [shape.2] using tokenValid) tokenValid.2.1
        (by simpa [shape.2] using currentFound) rfl
        (by simp [shape.2])).of_file_eq (by simp [shape.2])

theorem finishRecoveredMember_preservesTokenWindow
    (first last : SourceSpan) :
    Parser.PreservesTokenWindow (finishRecoveredMember first last) := by
  intro input
  unfold finishRecoveredMember Reply.PreservesTokenWindow State.emit
  exact ⟨rfl, rfl⟩

theorem recoverContractMemberAux_preservesTokenWindow
    (first last : SourceSpan) (fuel : Nat) :
    Parser.PreservesTokenWindow
      (recoverContractMemberAux first last fuel) := by
  intro input
  induction fuel generalizing last input with
  | zero => trivial
  | succ fuel inductionHypothesis =>
      unfold recoverContractMemberAux
      split
      · exact finishRecoveredMember_preservesTokenWindow first last input
      · cases advanced : input.advance? with
        | none =>
            exact finishRecoveredMember_preservesTokenWindow first last input
        | some pair =>
            rcases pair with ⟨token, next⟩
            exact (inductionHypothesis token.span next).trans (by
              simp [(advance?_state_shape advanced).2])

theorem recoverContractMemberAux_preservesTokensOnSuccess
    (first last : SourceSpan) (fuel : Nat) :
    Parser.PreservesTokensOnSuccess
      (recoverContractMemberAux first last fuel) :=
  (recoverContractMemberAux_preservesTokenWindow first last fuel).preservesTokensOnSuccess

theorem recoverContractMemberAux_ok_state_shape (first last : SourceSpan) :
    ∀ fuel, ∀ {input final : State} {member : ContractMember},
      recoverContractMemberAux first last fuel input = .ok member final →
      input.cursor ≤ final.cursor ∧
        first.startByte = member.span.startByte := by
  intro fuel
  induction fuel generalizing last with
  | zero => simp [recoverContractMemberAux]
  | succ fuel inductionHypothesis =>
      intro input final member parsed
      unfold recoverContractMemberAux at parsed
      split at parsed
      · unfold finishRecoveredMember at parsed
        cases parsed
        exact ⟨Nat.le_refl _, rfl⟩
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at parsed
            unfold finishRecoveredMember at parsed
            cases parsed
            exact ⟨Nat.le_refl _, rfl⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at parsed
            have recursive := inductionHypothesis token.span parsed
            exact ⟨Nat.le_trans (by
              simp [(advance?_state_shape advanced).2]) recursive.1,
              recursive.2⟩

theorem recoverContractMemberAux_cursorMonotoneOnSuccess
    (first last : SourceSpan) (fuel : Nat) :
    Parser.CursorMonotoneOnSuccess
      (recoverContractMemberAux first last fuel) :=
  fun _ _ _ parsed =>
    (recoverContractMemberAux_ok_state_shape first last fuel parsed).1

theorem recoverContractMember_preservesTokenWindow :
    Parser.PreservesTokenWindow recoverContractMember := by
  intro input
  unfold recoverContractMember
  cases advanced : input.advance? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some pair =>
      rcases pair with ⟨token, next⟩
      exact (recoverContractMemberAux_preservesTokenWindow token.span token.span
        (next.remainingCount + 1) next).trans (by
          simp [(advance?_state_shape advanced).2])

theorem recoverContractMember_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess recoverContractMember :=
  recoverContractMember_preservesTokenWindow.preservesTokensOnSuccess

theorem recoverContractMember_ok_state_shape
    {input final : State} {member : ContractMember}
    (parsed : recoverContractMember input = .ok member final) :
    input.cursor ≤ final.cursor ∧
      ∃ token, input.peek? = some token ∧
        token.span.startByte = member.span.startByte := by
  unfold recoverContractMember at parsed
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at parsed
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at parsed
      have recovered := recoverContractMemberAux_ok_state_shape token.span
        token.span (next.remainingCount + 1) parsed
      exact ⟨Nat.le_trans (by simp [(advance?_state_shape advanced).2])
        recovered.1, token, (advance?_state_shape advanced).1, recovered.2⟩

theorem recoverContractMember_cursor_lt_onSuccess
    {input final : State} {member : ContractMember}
    (parsed : recoverContractMember input = .ok member final) :
    input.cursor < final.cursor := by
  unfold recoverContractMember at parsed
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at parsed
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at parsed
      exact Nat.lt_of_lt_of_le (by simp [(advance?_state_shape advanced).2])
        (recoverContractMemberAux_ok_state_shape token.span token.span
          (next.remainingCount + 1) parsed).1

theorem recoverContractMember_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess recoverContractMember :=
  fun _ _ _ parsed =>
    Nat.le_of_lt (recoverContractMember_cursor_lt_onSuccess parsed)

theorem recoverContractMember_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess recoverContractMember (·.span) :=
  fun _ _ _ parsed => (recoverContractMember_ok_state_shape parsed).2

end Solcore.Syntax.Parser.ContractInternals
