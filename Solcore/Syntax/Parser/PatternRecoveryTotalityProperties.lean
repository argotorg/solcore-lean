import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.PatternProperties

/-! Production-fuel adequacy for malformed pattern recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- More fuel than remaining tokens makes pattern recovery terminate. -/
theorem recoverPatternAux_exists_ok_of_remainingCount_lt
    (first : SourceSpan) :
    ∀ fuel last state, state.remainingCount < fuel →
      ∃ value final,
        recoverPatternAux first last fuel state = .ok value final := by
  intro fuel last
  induction fuel generalizing last with
  | zero =>
      intro state adequate
      omega
  | succ fuel inductionHypothesis =>
      intro state adequate
      unfold recoverPatternAux
      split
      · exact ⟨_, _, rfl⟩
      · cases advanced : state.advance? with
        | none => exact ⟨_, _, rfl⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            change ∃ value final,
              recoverPatternAux first token.span fuel next = .ok value final
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

/-- Adequately fueled recovery has an ordinary success result. -/
theorem recoverPatternAux_ordinary_of_remainingCount_lt
    (first last : SourceSpan) (fuel : Nat) (state : State)
    (adequate : state.remainingCount < fuel) :
    (∃ value final,
      recoverPatternAux first last fuel state = .ok value final) ∨
      (∃ failure final,
        recoverPatternAux first last fuel state = .reject failure final) :=
  Or.inl (recoverPatternAux_exists_ok_of_remainingCount_lt first
    fuel last state adequate)

theorem recoverPatternAux_ne_invariant_of_remainingCount_lt
    (first last : SourceSpan) (fuel : Nat) (state : State)
    (adequate : state.remainingCount < fuel)
    (error : ParserInvariantError) :
    recoverPatternAux first last fuel state ≠ .invariant error := by
  intro failed
  rcases recoverPatternAux_exists_ok_of_remainingCount_lt first fuel last state
      adequate with ⟨value, final, result⟩
  rw [result] at failed
  contradiction

/-- The production recovery fuel is always adequate. -/
theorem recoverPatternAux_production_exists_ok
    (first last : SourceSpan) (state : State) :
    ∃ value final,
      recoverPatternAux first last (state.remainingCount + 1) state =
        .ok value final :=
  recoverPatternAux_exists_ok_of_remainingCount_lt first
    (state.remainingCount + 1) last state (by omega)

/-- Production-fueled recovery is ordinary on every input state. -/
theorem recoverPatternAux_production_ordinary (first last : SourceSpan) :
    Parser.Ordinary (fun state =>
      recoverPatternAux first last (state.remainingCount + 1) state) := by
  intro state
  exact Or.inl (recoverPatternAux_production_exists_ok first last state)

/-- Production-fueled recovery is invariant-free on valid parser states. -/
theorem recoverPatternAux_production_invariantFreeOnValid
    (first last : SourceSpan) :
    Parser.InvariantFreeOnValid (fun state =>
      recoverPatternAux first last (state.remainingCount + 1) state) :=
  (recoverPatternAux_production_ordinary first last).invariantFreeOnValid

/-- Production-fueled recovery cannot expose an internal invariant. -/
theorem recoverPatternAux_production_ne_invariant
    (first last : SourceSpan) (state : State)
    (error : ParserInvariantError) :
    recoverPatternAux first last (state.remainingCount + 1) state ≠
      .invariant error :=
  (recoverPatternAux_production_ordinary first last).ne_invariant state error

end Solcore.Syntax.Parser.PatternInternals
