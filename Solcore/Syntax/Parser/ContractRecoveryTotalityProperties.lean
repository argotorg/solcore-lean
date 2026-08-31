import Solcore.Syntax.Parser.ContractRecoveryProperties

/-! Fuel adequacy and result classification for contract-member recovery. -/

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

/-- More fuel than remaining tokens rules out recovery-fuel exhaustion. -/
theorem recoverContractMemberAux_ok_of_remainingCount_lt
    (first last : SourceSpan) :
    ∀ fuel state, state.remainingCount < fuel →
      ∃ member final,
        recoverContractMemberAux first last fuel state = .ok member final := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      intro state adequate
      omega
  | succ fuel inductionHypothesis =>
      intro state adequate
      unfold recoverContractMemberAux
      split
      · simp [finishRecoveredMember]
      · cases advanced : state.advance? with
        | none => simp [finishRecoveredMember]
        | some pair =>
            rcases pair with ⟨token, next⟩
            apply inductionHypothesis token.span next
            have shape := advance?_state_shape advanced
            have cursorBefore :=
              State.cursor_lt_endIndex_of_peek?_eq_some shape.1
            simp only [State.remainingCount, shape.2] at adequate ⊢
            omega

/-- The exact fuel chosen by the production parser is always adequate. -/
theorem recoverContractMemberAux_production_ok
    (first last : SourceSpan) (state : State) :
    ∃ member final,
      recoverContractMemberAux first last (state.remainingCount + 1) state =
        .ok member final :=
  recoverContractMemberAux_ok_of_remainingCount_lt first last
    (state.remainingCount + 1) state (by omega)

/-- Contract-member recovery has a total public result classification. -/
theorem recoverContractMember_total (state : State) :
    (∃ member final, recoverContractMember state = .ok member final) ∨
      (∃ failure final,
        recoverContractMember state = .reject failure final) := by
  unfold recoverContractMember
  cases advanced : state.advance? with
  | none =>
      right
      simp [rejectAt]
  | some pair =>
      rcases pair with ⟨token, next⟩
      left
      simpa only [advanced] using
        recoverContractMemberAux_production_ok token.span token.span next

/-- The public recovery parser cannot expose an internal invariant failure. -/
theorem recoverContractMember_ne_invariant (state : State)
    (error : ParserInvariantError) :
    recoverContractMember state ≠ .invariant error := by
  intro failed
  rcases recoverContractMember_total state with success | rejection
  · rcases success with ⟨member, final, recovered⟩
    rw [recovered] at failed
    contradiction
  · rcases rejection with ⟨failure, final, recovered⟩
    rw [recovered] at failed
    contradiction

/-- At the active window end recovery performs the parser's ordinary rejection. -/
theorem recoverContractMember_reject_of_atEnd (state : State)
    (atEnd : state.atEnd = true) :
    ∃ failure, recoverContractMember state = .reject failure state := by
  have cursorAtEnd : state.window.endIndex ≤ state.cursor := by
    simpa [State.atEnd] using atEnd
  simp [recoverContractMember, State.advance?, State.peek?,
    Nat.not_lt.mpr cursorAtEnd, rejectAt]

private theorem advance?_exists_of_valid_not_atEnd
    (state : State) (valid : state.ValidFor)
    (notEnd : state.atEnd = false) :
    ∃ token next, state.advance? = some (token, next) := by
  have cursorBefore : state.cursor < state.window.endIndex := by
    simpa [State.atEnd] using notEnd
  have cursorBound : state.cursor < state.tokens.size :=
    Nat.lt_of_lt_of_le cursorBefore valid.endIndex_le_size
  let token := state.tokens[state.cursor]'cursorBound
  have found : state.tokens[state.cursor]? = some token := by
    apply Array.getElem?_eq_some_iff.mpr
    exact ⟨cursorBound, rfl⟩
  refine ⟨token, { state with cursor := state.cursor + 1 }, ?_⟩
  simp [State.advance?, State.peek?, cursorBefore, found]

/-- A valid non-end state is recovered successfully, never rejected. -/
theorem recoverContractMember_ok_of_valid_not_atEnd
    (state : State) (valid : state.ValidFor)
    (notEnd : state.atEnd = false) :
    ∃ member final, recoverContractMember state = .ok member final := by
  rcases advance?_exists_of_valid_not_atEnd state valid notEnd with
    ⟨token, next, advanced⟩
  unfold recoverContractMember
  simpa only [advanced] using
    recoverContractMemberAux_production_ok token.span token.span next

end Solcore.Syntax.Parser.ContractInternals
