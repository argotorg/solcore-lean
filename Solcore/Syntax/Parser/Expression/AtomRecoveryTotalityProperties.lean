import Solcore.Syntax.Parser.Expression.AtomProperties
import Solcore.Syntax.Parser.InvariantFreeProperties

/-! Production-fuel adequacy for malformed expression-atom recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- More fuel than remaining tokens makes atom recovery terminate. -/
theorem recoverAtomAux_exists_ok_of_remainingCount_lt
    (first : SourceSpan) :
    ∀ fuel last state, state.remainingCount < fuel →
      ∃ value final,
        recoverAtomAux first last fuel state = .ok value final := by
  intro fuel last
  induction fuel generalizing last with
  | zero =>
      intro state adequate
      omega
  | succ fuel inductionHypothesis =>
      intro state adequate
      unfold recoverAtomAux
      split
      · exact ⟨_, _, rfl⟩
      · cases advanced : state.advance? with
        | none => exact ⟨_, _, rfl⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            change ∃ value final,
              recoverAtomAux first token.span fuel next = .ok value final
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

/-- The production recovery fuel is always adequate. -/
theorem recoverAtomAux_production_exists_ok
    (first last : SourceSpan) (state : State) :
    ∃ value final,
      recoverAtomAux first last (state.remainingCount + 1) state =
        .ok value final :=
  recoverAtomAux_exists_ok_of_remainingCount_lt first
    (state.remainingCount + 1) last state (by omega)

theorem recoverAtomAux_ne_invariant_of_remainingCount_lt
    (first last : SourceSpan) (fuel : Nat) (state : State)
    (adequate : state.remainingCount < fuel)
    (error : ParserInvariantError) :
    recoverAtomAux first last fuel state ≠ .invariant error := by
  intro failed
  rcases recoverAtomAux_exists_ok_of_remainingCount_lt first fuel last state
      adequate with ⟨value, final, result⟩
  rw [result] at failed
  contradiction

/-- Complete atom recovery has an ordinary result on every input. -/
theorem recoverAtom_ordinary : Parser.Ordinary recoverAtom := by
  intro input
  unfold recoverAtom
  cases advanced : input.advance? with
  | none => exact Or.inr ⟨_, _, rfl⟩
  | some pair =>
      rcases pair with ⟨token, next⟩
      exact Or.inl (recoverAtomAux_production_exists_ok
        token.span token.span next)

theorem recoverAtom_invariantFreeOnValid :
    Parser.InvariantFreeOnValid recoverAtom :=
  recoverAtom_ordinary.invariantFreeOnValid

theorem recoverAtom_ne_invariant (input : State)
    (error : ParserInvariantError) :
    recoverAtom input ≠ .invariant error :=
  recoverAtom_ordinary.ne_invariant input error

end Solcore.Syntax.Parser.ExpressionAtomInternals
