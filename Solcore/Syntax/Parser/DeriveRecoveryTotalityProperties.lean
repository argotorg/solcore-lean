import Solcore.Syntax.Parser.Derive
import Solcore.Syntax.Parser.PrimitiveTotalityProperties

/-! Fuel adequacy and ordinary control flow for derive recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.DeriveAttributeInternals

/-- More fuel than remaining tokens makes the recovery tail ordinary. -/
theorem recoverTail_ordinary_of_remainingCount_lt
    (hash last : SourceSpan) :
    ∀ fuel state, state.remainingCount < fuel →
      (∃ derive next,
        recoverTail hash last fuel state = .ok derive next) ∨
      (∃ failure next,
        recoverTail hash last fuel state = .reject failure next) := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      intro state adequate
      omega
  | succ fuel inductionHypothesis =>
      intro state adequate
      unfold recoverTail
      split
      · cases closingResult : symbol .rightBracket .topItem state with
        | ok closing next =>
            dsimp only
            exact Or.inl ⟨_, _, rfl⟩
        | reject failure rejected =>
            exact Or.inr ⟨failure, rejected, rfl⟩
        | invariant error =>
            exact False.elim
              (symbol_ne_invariant .rightBracket .topItem state error
                closingResult)
      · split
        · exact Or.inl ⟨_, _, rfl⟩
        · cases advanced : state.advance? with
          | none => exact Or.inl ⟨_, _, rfl⟩
          | some pair =>
              rcases pair with ⟨token, next⟩
              change
                (∃ derive final,
                  recoverTail hash token.span fuel next = .ok derive final) ∨
                (∃ failure final,
                  recoverTail hash token.span fuel next =
                    .reject failure final)
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

/-- Adequate derive recovery fuel excludes its internal invariant branch. -/
theorem recoverTail_ne_invariant_of_remainingCount_lt
    (hash last : SourceSpan) (fuel : Nat) (state : State)
    (adequate : state.remainingCount < fuel)
    (error : ParserInvariantError) :
    recoverTail hash last fuel state ≠ .invariant error := by
  intro failed
  rcases recoverTail_ordinary_of_remainingCount_lt hash last fuel state
      adequate with
    ⟨derive, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- The exact production fuel chosen for a recovery tail is sufficient. -/
theorem recoverTail_production_ordinary
    (hash last : SourceSpan) (state : State) :
    (∃ derive next,
      recoverTail hash last (state.remainingCount + 1) state =
        .ok derive next) ∨
      (∃ failure next,
        recoverTail hash last (state.remainingCount + 1) state =
          .reject failure next) :=
  recoverTail_ordinary_of_remainingCount_lt hash last
    (state.remainingCount + 1) state (by omega)

/-- The proof-visible recovered derive parser is ordinary on every input. -/
theorem recovered_ordinary : Parser.Ordinary recovered := by
  intro input
  unfold recovered
  cases hashResult : symbol .hash .topItem input with
  | ok hash afterHash =>
      dsimp only
      cases openingResult : symbol .leftBracket .topItem afterHash with
      | ok opening next =>
          dsimp only
          exact recoverTail_production_ordinary hash.span opening.span next
      | reject failure rejected =>
          exact Or.inr ⟨failure, rejected, rfl⟩
      | invariant error =>
          exact False.elim
            (symbol_ne_invariant .leftBracket .topItem afterHash error
              openingResult)
  | reject failure rejected =>
      exact Or.inr ⟨failure, rejected, rfl⟩
  | invariant error =>
      exact False.elim
        (symbol_ne_invariant .hash .topItem input error hashResult)

/-- Recovered derive parsing cannot expose fuel or primitive invariants. -/
theorem recovered_ne_invariant (input : State)
    (error : ParserInvariantError) :
    recovered input ≠ .invariant error :=
  recovered_ordinary.ne_invariant input error

end Solcore.Syntax.Parser.DeriveAttributeInternals
