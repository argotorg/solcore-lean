import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.ExpressionProperties

/-! Fuel-aware totality for left-associative expression layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/--
The loop fuel decreases after a recognized operator, while the independent
operand fuel remains adequate because every successful operand is strict.
-/
theorem leftAssociativeTail_ordinary_of_fuels
    (operand : Parser Expr) (operandFuel precedence : Nat)
    (contract : FuelElementTotalityContract operand operandFuel) :
    ∀ loopFuel left input,
      input.ValidFor →
      input.remainingCount < loopFuel →
      input.remainingCount < operandFuel →
      (∃ expression next,
        leftAssociativeTail operand precedence loopFuel left input =
          .ok expression next) ∨
      (∃ failure next,
        leftAssociativeTail operand precedence loopFuel left input =
          .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro left input inputValid loopAdequate operandAdequate
      omega
  | succ loopFuel inductionHypothesis =>
      intro left input inputValid loopAdequate operandAdequate
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none =>
          exact Or.inl ⟨left, input, by
            simp only [leftAssociativeTail, operatorResult]⟩
      | some operator =>
          rcases binaryAtPrecedence?_some_state_shape operatorResult with
            ⟨operatorToken, operatorFound, _decoded, _span⟩
          let afterOperator := { input with cursor := input.cursor + 1 }
          have consumedResult :
              consumeBinary operator input = .ok () afterOperator := by
            exact consumeBinary_ok_state_shape operator input
          have consumedValid := consumeBinary_reply_validFor operator
            inputValid operatorFound
          rw [consumedResult] at consumedValid
          have afterOperatorAdequate :
              afterOperator.remainingCount < operandFuel :=
            remainingCount_lt_of_cursor_le (by rfl)
              (by dsimp [afterOperator]; omega)
              operandAdequate
          rcases contract.ordinary afterOperator consumedValid.2.1
              afterOperatorAdequate with
            ⟨right, next, operandResult⟩ |
            ⟨failure, rejected, operandResult⟩
          · have rightValid := contract.validFor afterOperator
              consumedValid.2.1
            rw [operandResult] at rightValid
            have rightWindow := contract.preservesTokenWindow afterOperator
            rw [operandResult] at rightWindow
            have rightProgress := contract.cursorLtOnSuccess operandResult
            have nextWindow : next.window = input.window := by
              exact rightWindow.2
            have inputProgress : input.cursor < next.cursor := by
              exact Nat.lt_trans (by simp [afterOperator]) rightProgress
            have nextLoopAdequate :
                next.remainingCount < loopFuel :=
              remainingCount_lt_after_strict_progress rightValid.2.1
                nextWindow inputProgress loopAdequate
            have nextOperandAdequate :
                next.remainingCount < operandFuel :=
              remainingCount_lt_of_cursor_le nextWindow
                (Nat.le_of_lt inputProgress) operandAdequate
            rcases inductionHypothesis (binaryNode left operator right) next
                rightValid.2.1 nextLoopAdequate nextOperandAdequate with
              ⟨expression, final, recursiveResult⟩ |
              ⟨failure, rejected, recursiveResult⟩
            · exact Or.inl ⟨expression, final, by
                simp only [leftAssociativeTail, operatorResult,
                  consumedResult, operandResult]
                exact recursiveResult⟩
            · exact Or.inr ⟨failure, rejected, by
                simp only [leftAssociativeTail, operatorResult,
                  consumedResult, operandResult]
                exact recursiveResult⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [leftAssociativeTail, operatorResult,
                consumedResult, operandResult]⟩

theorem leftAssociativeTail_ne_invariant_of_fuels
    (operand : Parser Expr) (operandFuel precedence loopFuel : Nat)
    (contract : FuelElementTotalityContract operand operandFuel)
    (left : Expr) (input : State) (inputValid : input.ValidFor)
    (loopAdequate : input.remainingCount < loopFuel)
    (operandAdequate : input.remainingCount < operandFuel)
    (error : ParserInvariantError) :
    leftAssociativeTail operand precedence loopFuel left input ≠
      .invariant error := by
  intro failed
  rcases leftAssociativeTail_ordinary_of_fuels operand operandFuel
      precedence contract loopFuel left input inputValid loopAdequate
      operandAdequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- One complete left-associative layer inherits its operand fuel bound. -/
theorem leftAssociative_ordinary_of_elementFuel
    (operand : Parser Expr) (operandFuel precedence : Nat)
    (contract : FuelElementTotalityContract operand operandFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < operandFuel) :
    (∃ expression next,
      leftAssociative operand precedence input = .ok expression next) ∨
    (∃ failure next,
      leftAssociative operand precedence input = .reject failure next) := by
  rcases contract.ordinary input inputValid adequate with
    ⟨left, next, operandResult⟩ | ⟨failure, rejected, operandResult⟩
  · have leftValid := contract.validFor input inputValid
    rw [operandResult] at leftValid
    have leftWindow := contract.preservesTokenWindow input
    rw [operandResult] at leftWindow
    have nextAdequate : next.remainingCount < operandFuel :=
      remainingCount_lt_of_cursor_le leftWindow.2
        (Nat.le_of_lt (contract.cursorLtOnSuccess operandResult)) adequate
    rcases leftAssociativeTail_ordinary_of_fuels operand operandFuel
        precedence contract (next.remainingCount + 1) left next
        leftValid.2.1 (by omega) nextAdequate with
      ⟨expression, final, tailResult⟩ |
      ⟨failure, rejected, tailResult⟩
    · exact Or.inl ⟨expression, final, by
        simp only [leftAssociative, operandResult]
        exact tailResult⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [leftAssociative, operandResult]
        exact tailResult⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [leftAssociative, operandResult]⟩

theorem leftAssociative_ne_invariant_of_elementFuel
    (operand : Parser Expr) (operandFuel precedence : Nat)
    (contract : FuelElementTotalityContract operand operandFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < operandFuel)
    (error : ParserInvariantError) :
    leftAssociative operand precedence input ≠ .invariant error := by
  intro failed
  rcases leftAssociative_ordinary_of_elementFuel operand operandFuel
      precedence contract input inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionInternals
