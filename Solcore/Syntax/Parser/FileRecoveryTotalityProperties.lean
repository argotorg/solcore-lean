import Solcore.Syntax.Parser.FileRecoveryProperties

/-! Resource and totality contracts for canonical top-level recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- More fuel than remaining tokens is sufficient for recovery to finish. -/
theorem recoverTopItemAux_exists_ok_of_remainingCount_lt
    (first last : SourceSpan) :
    ∀ fuel state, state.remainingCount < fuel →
      ∃ item final,
        recoverTopItemAux first last fuel state = .ok item final := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      intro state enough
      simp at enough
  | succ fuel inductionHypothesis =>
      intro state enough
      unfold recoverTopItemAux
      split
      · exact ⟨_, _, rfl⟩
      · cases advanced : state.advance? with
        | none => exact ⟨_, _, rfl⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            change ∃ item final,
              recoverTopItemAux first token.span fuel next = .ok item final
            apply inductionHypothesis
            unfold State.advance? at advanced
            cases found : state.peek? with
            | none => simp [found] at advanced
            | some current =>
                simp only [found, Option.map_some] at advanced
                cases advanced
                have cursorBeforeEnd :=
                  State.cursor_lt_endIndex_of_peek?_eq_some found
                simp only [State.remainingCount] at enough ⊢
                omega

/-- The production fuel selected by `recoverTopItem` always suffices. -/
theorem recoverTopItemAux_production_exists_ok
    (first last : SourceSpan) (state : State) :
    ∃ item final,
      recoverTopItemAux first last (state.remainingCount + 1) state =
        .ok item final :=
  recoverTopItemAux_exists_ok_of_remainingCount_lt first last
    (state.remainingCount + 1) state (by omega)

/-- Recovery has only an ordinary success or rejection, never an invariant. -/
theorem recoverTopItem_ordinary (state : State) :
    (∃ item final, recoverTopItem state = .ok item final) ∨
      (∃ failure final, recoverTopItem state = .reject failure final) := by
  unfold recoverTopItem
  cases advanced : state.advance? with
  | none => exact Or.inr ⟨_, _, rfl⟩
  | some pair =>
      rcases pair with ⟨token, next⟩
      exact Or.inl (recoverTopItemAux_production_exists_ok
        token.span token.span next)

/-- Top-level recovery cannot expose a fuel or progress invariant. -/
theorem recoverTopItem_ne_invariant (state : State)
    (error : ParserInvariantError) :
    recoverTopItem state ≠ .invariant error := by
  intro invariantResult
  rcases recoverTopItem_ordinary state with
    ⟨item, final, result⟩ | ⟨failure, final, result⟩ <;>
      rw [result] at invariantResult <;> contradiction

/-- A valid nonempty recovery window succeeds and strictly consumes input. -/
theorem recoverTopItem_exists_ok_of_validFor_not_atEnd
    (state : State) (stateValid : state.ValidFor)
    (notAtEnd : state.atEnd = false) :
    ∃ item final,
      recoverTopItem state = .ok item final ∧
        state.cursor < final.cursor := by
  have cursorBeforeEnd : state.cursor < state.window.endIndex := by
    simpa [State.atEnd] using notAtEnd
  have cursorBeforeSize : state.cursor < state.tokens.size :=
    Nat.lt_of_lt_of_le cursorBeforeEnd stateValid.endIndex_le_size
  let token := state.tokens[state.cursor]
  have tokenFound : state.tokens[state.cursor]? = some token := by
    exact Array.getElem?_eq_some_iff.mpr ⟨cursorBeforeSize, rfl⟩
  have peekFound : state.peek? = some token := by
    unfold State.peek?
    simp [cursorBeforeEnd, tokenFound]
  have advanced : state.advance? = some
      (token, { state with cursor := state.cursor + 1 }) := by
    simp [State.advance?, peekFound]
  unfold recoverTopItem
  simp only [advanced]
  rcases recoverTopItemAux_production_exists_ok token.span token.span
      { state with cursor := state.cursor + 1 } with
    ⟨item, final, result⟩
  exact ⟨item, final, result,
    recoverTopItem_cursor_lt_onSuccess (by
      unfold recoverTopItem
      simpa only [advanced] using result)⟩

/-- At a window end, recovery reports its ordinary top-item rejection. -/
theorem recoverTopItem_eq_rejectAt_of_atEnd
    (state : State) (atEnd : state.atEnd = true) :
    recoverTopItem state =
      rejectAt state { head := .topItem, tail := [] } .topItem := by
  have cursorAtEnd : state.window.endIndex ≤ state.cursor := by
    simpa [State.atEnd] using atEnd
  have peekNone : state.peek? = none := by
    unfold State.peek?
    simp [Nat.not_lt_of_ge cursorAtEnd]
  unfold recoverTopItem State.advance?
  simp [peekNone]

/-- On valid input, recovery succeeds exactly away from the window end. -/
theorem recoverTopItem_exists_ok_iff_not_atEnd
    (state : State) (stateValid : state.ValidFor) :
    (∃ item final, recoverTopItem state = .ok item final) ↔
      state.atEnd = false := by
  constructor
  · rintro ⟨item, final, recovered⟩
    rcases (recoverTopItem_ok_state_shape recovered).2 with
      ⟨token, tokenFound, _⟩
    have cursorBeforeEnd :=
      State.cursor_lt_endIndex_of_peek?_eq_some tokenFound
    simpa [State.atEnd] using cursorBeforeEnd
  · intro notAtEnd
    rcases recoverTopItem_exists_ok_of_validFor_not_atEnd state stateValid
        notAtEnd with
      ⟨item, final, recovered, _⟩
    exact ⟨item, final, recovered⟩

end Solcore.Syntax.Parser.FileInternals
