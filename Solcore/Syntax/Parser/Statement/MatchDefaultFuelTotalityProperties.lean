import Solcore.Syntax.Parser.BlockFuelTotalityProperties
import Solcore.Syntax.Parser.Statement.MatchProperties

/-! Fuel-aware totality for the optional Core-match `default` body. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/--
A present `default` spends one keyword token before entering its recursive
block; an absent default succeeds without consuming input.
-/
theorem optionalDefaultBody_ordinary_of_statementFuel
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (statementFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 2) :
    (∃ body next, optionalDefaultBody statement input = .ok body next) ∨
      (∃ failure next,
        optionalDefaultBody statement input = .reject failure next) := by
  unfold optionalDefaultBody
  simp only [getState, bind]
  split
  · rcases (keyword_ordinary .defaultKw .statement) input with
      ⟨marker, afterMarker, markerResult⟩ |
      ⟨failure, rejected, markerResult⟩
    · have markerReply := keyword_validFor .defaultKw .statement input
        inputValid
      rw [markerResult] at markerReply
      have markerWindow := keyword_preservesTokenWindow .defaultKw
        .statement input
      rw [markerResult] at markerWindow
      have bodyBudget :
          afterMarker.remainingCount < statementFuel + 1 :=
        remainingCount_lt_after_strict_progress markerReply.2.1
          markerWindow.2
          (acceptToken_cursor_lt_onSuccess (.keyword .defaultKw)
            .statement (· == .keyword .defaultKw) markerResult)
          adequate
      rcases coreBlock_ordinary_of_statementFuel statement .require
          statementFuel statementContract statementStrict afterMarker
            markerReply.2.1 bodyBudget with
        ⟨body, final, bodyResult⟩ |
        ⟨failure, rejected, bodyResult⟩
      · exact Or.inl ⟨some body, final, by
          simp only [markerResult, bodyResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [markerResult, bodyResult]⟩
    · exact Or.inr ⟨failure, rejected, by simp only [markerResult]⟩
  · exact Or.inl ⟨none, input, rfl⟩

/-- Adequate recursive-statement fuel excludes every helper invariant. -/
theorem optionalDefaultBody_ne_invariant_of_statementFuel
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (statementFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 2)
    (error : ParserInvariantError) :
    optionalDefaultBody statement input ≠ .invariant error := by
  intro failed
  rcases optionalDefaultBody_ordinary_of_statementFuel statement
      statementFuel statementContract statementStrict input inputValid
        adequate with
    ⟨body, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.MatchInternals
