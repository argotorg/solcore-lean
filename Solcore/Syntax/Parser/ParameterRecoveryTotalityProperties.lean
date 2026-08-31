import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.ParameterProperties

/-! Production-fuel adequacy for malformed function-parameter recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

theorem recoverParameterAux_exists_ok_of_remainingCount_lt
    (first : SourceSpan) :
    ∀ fuel last state, state.remainingCount < fuel →
      ∃ value final,
        recoverParameterAux first last fuel state = .ok value final := by
  intro fuel last
  induction fuel generalizing last with
  | zero =>
      intro state adequate
      omega
  | succ fuel inductionHypothesis =>
      intro state adequate
      unfold recoverParameterAux
      split
      · exact ⟨_, _, rfl⟩
      · cases advanced : state.advance? with
        | none => exact ⟨_, _, rfl⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            change ∃ value final,
              recoverParameterAux first token.span fuel next = .ok value final
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

theorem recoverParameterAux_ordinary_of_remainingCount_lt
    (first last : SourceSpan) (fuel : Nat) (state : State)
    (adequate : state.remainingCount < fuel) :
    (∃ value final,
      recoverParameterAux first last fuel state = .ok value final) ∨
    (∃ failure final,
      recoverParameterAux first last fuel state = .reject failure final) :=
  Or.inl (recoverParameterAux_exists_ok_of_remainingCount_lt first
    fuel last state adequate)

theorem recoverParameterAux_ne_invariant_of_remainingCount_lt
    (first last : SourceSpan) (fuel : Nat) (state : State)
    (adequate : state.remainingCount < fuel)
    (error : ParserInvariantError) :
    recoverParameterAux first last fuel state ≠ .invariant error := by
  intro failed
  rcases recoverParameterAux_exists_ok_of_remainingCount_lt first fuel last
      state adequate with ⟨value, final, result⟩
  rw [result] at failed
  contradiction

theorem recoverParameterAux_production_exists_ok
    (first last : SourceSpan) (state : State) :
    ∃ value final,
      recoverParameterAux first last (state.remainingCount + 1) state =
        .ok value final :=
  recoverParameterAux_exists_ok_of_remainingCount_lt first
    (state.remainingCount + 1) last state (by omega)

theorem recoverParameterAux_production_ordinary (first last : SourceSpan) :
    Parser.Ordinary (fun state =>
      recoverParameterAux first last (state.remainingCount + 1) state) := by
  intro state
  exact Or.inl (recoverParameterAux_production_exists_ok first last state)

theorem recoverParameterAux_production_ne_invariant
    (first last : SourceSpan) (state : State)
    (error : ParserInvariantError) :
    recoverParameterAux first last (state.remainingCount + 1) state ≠
      .invariant error :=
  (recoverParameterAux_production_ordinary first last).ne_invariant state error

/-- Public recovery either succeeds or performs its ordinary empty-input reject. -/
theorem recoverParameter_ordinary : Parser.Ordinary recoverParameter := by
  intro state
  unfold recoverParameter
  cases advanced : state.advance? with
  | none =>
      exact Or.inr ⟨_, state, rfl⟩
  | some pair =>
      rcases pair with ⟨token, next⟩
      exact Or.inl (by
        simpa only [advanced] using
          recoverParameterAux_production_exists_ok token.span token.span next)

theorem recoverParameter_invariantFreeOnValid :
    Parser.InvariantFreeOnValid recoverParameter :=
  recoverParameter_ordinary.invariantFreeOnValid

theorem recoverParameter_ne_invariant (state : State)
    (error : ParserInvariantError) :
    recoverParameter state ≠ .invariant error :=
  recoverParameter_ordinary.ne_invariant state error

end Solcore.Syntax.Parser.FunctionParameterInternals
