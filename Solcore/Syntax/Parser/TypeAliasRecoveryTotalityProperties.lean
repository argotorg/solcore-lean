import Solcore.Syntax.Parser.TypeAliasProperties

/-! Fuel adequacy and totality for malformed type-alias RHS recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TypeAliasInternals

/-- More fuel than remaining tokens makes alias-value recovery terminate. -/
theorem recoverTypeAliasValueAux_exists_ok_of_remainingCount_lt
    (first : SourceSpan) :
  ∀ fuel last state, state.remainingCount < fuel →
      ∃ value final,
        recoverTypeAliasValueAux first last fuel state = .ok value final := by
  intro fuel last
  induction fuel generalizing last with
  | zero =>
      intro state adequate
      omega
  | succ fuel inductionHypothesis =>
      intro state adequate
      unfold recoverTypeAliasValueAux
      split
      · simp [finishRecoveredType]
      · cases advanced : state.advance? with
        | none => simp [finishRecoveredType]
        | some pair =>
            rcases pair with ⟨token, next⟩
            apply inductionHypothesis token.span next
            unfold State.advance? at advanced
            cases found : state.peek? with
            | none => simp [found] at advanced
            | some current =>
                simp only [found, Option.map_some] at advanced
                cases advanced
                have cursorBeforeEnd :=
                  State.cursor_lt_endIndex_of_peek?_eq_some found
                simp only [State.remainingCount] at adequate ⊢
                omega

/-- The production fuel selected by recovery is always adequate. -/
theorem recoverTypeAliasValueAux_production_exists_ok
    (first last : SourceSpan) (state : State) :
    ∃ value final,
      recoverTypeAliasValueAux first last (state.remainingCount + 1) state =
        .ok value final :=
  recoverTypeAliasValueAux_exists_ok_of_remainingCount_lt first
    (state.remainingCount + 1) last state (by omega)

/-- Adequately fueled auxiliary recovery has an ordinary result. -/
theorem recoverTypeAliasValueAux_ordinary_of_remainingCount_lt
    (first last : SourceSpan) (fuel : Nat) (state : State)
    (adequate : state.remainingCount < fuel) :
    (∃ value final,
      recoverTypeAliasValueAux first last fuel state = .ok value final) ∨
      (∃ failure final,
        recoverTypeAliasValueAux first last fuel state =
          .reject failure final) :=
  Or.inl (recoverTypeAliasValueAux_exists_ok_of_remainingCount_lt first
    fuel last state adequate)

/-- Adequate auxiliary recovery cannot expose an invariant failure. -/
theorem recoverTypeAliasValueAux_ne_invariant_of_remainingCount_lt
    (first last : SourceSpan) (fuel : Nat) (state : State)
    (adequate : state.remainingCount < fuel)
    (error : ParserInvariantError) :
    recoverTypeAliasValueAux first last fuel state ≠ .invariant error := by
  intro invariantResult
  rcases recoverTypeAliasValueAux_exists_ok_of_remainingCount_lt first
      fuel last state adequate with ⟨value, final, result⟩
  rw [result] at invariantResult
  contradiction

/-- The production auxiliary parser has only an ordinary result. -/
theorem recoverTypeAliasValueAux_production_ordinary
    (first last : SourceSpan) (state : State) :
    (∃ value final,
      recoverTypeAliasValueAux first last (state.remainingCount + 1) state =
        .ok value final) ∨
      (∃ failure final,
        recoverTypeAliasValueAux first last (state.remainingCount + 1) state =
          .reject failure final) :=
  Or.inl (recoverTypeAliasValueAux_production_exists_ok first last state)

/-- Production auxiliary recovery cannot exhaust its fuel. -/
theorem recoverTypeAliasValueAux_production_ne_invariant
    (first last : SourceSpan) (state : State)
    (error : ParserInvariantError) :
    recoverTypeAliasValueAux first last (state.remainingCount + 1) state ≠
      .invariant error :=
  recoverTypeAliasValueAux_ne_invariant_of_remainingCount_lt first last
    (state.remainingCount + 1) state (by omega) error

/-- Alias-value recovery returns either its recovered type or a rejection. -/
theorem recoverTypeAliasValue_ordinary (state : State) :
    (∃ value final, recoverTypeAliasValue state = .ok value final) ∨
      (∃ failure final,
        recoverTypeAliasValue state = .reject failure final) := by
  unfold recoverTypeAliasValue
  split
  · right
    simp [rejectAt]
  · cases advanced : state.advance? with
    | none =>
        right
        simp [rejectAt]
    | some pair =>
        rcases pair with ⟨token, next⟩
        left
        simpa only [advanced] using
          recoverTypeAliasValueAux_production_exists_ok
            token.span token.span next

/-- The malformed alias-value recovery entry point is invariant-free. -/
theorem recoverTypeAliasValue_ne_invariant (state : State)
    (error : ParserInvariantError) :
    recoverTypeAliasValue state ≠ .invariant error := by
  intro invariantResult
  rcases recoverTypeAliasValue_ordinary state with
    ⟨value, final, result⟩ | ⟨failure, final, result⟩ <;>
    rw [result] at invariantResult <;> contradiction

end Solcore.Syntax.Parser.TypeAliasInternals
