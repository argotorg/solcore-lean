import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.ExpressionProperties

/-! Fuel-aware totality for non-associative expression layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

theorem nonAssociative_ordinary_of_elementFuel
    (operand : Parser Expr) (operandFuel precedence : Nat)
    (contract : FuelElementTotalityContract operand operandFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < operandFuel) :
    (∃ expression next,
      nonAssociative operand precedence input = .ok expression next) ∨
    (∃ failure next,
      nonAssociative operand precedence input = .reject failure next) := by
  rcases contract.ordinary input inputValid adequate with
    ⟨left, next, leftResult⟩ | ⟨failure, rejected, leftResult⟩
  · have leftValid := contract.validFor input inputValid
    rw [leftResult] at leftValid
    have leftWindow := contract.preservesTokenWindow input
    rw [leftResult] at leftWindow
    have nextAdequate : next.remainingCount < operandFuel :=
      remainingCount_lt_of_cursor_le leftWindow.2
        (Nat.le_of_lt (contract.cursorLtOnSuccess leftResult)) adequate
    cases operatorResult : binaryAtPrecedence? next precedence with
    | none =>
        exact Or.inl ⟨left, next, by
          simp only [nonAssociative, leftResult, operatorResult]⟩
    | some operator =>
        rcases binaryAtPrecedence?_some_state_shape operatorResult with
          ⟨operatorToken, operatorFound, _decoded, _span⟩
        let afterOperator := { next with cursor := next.cursor + 1 }
        have consumedResult :
            consumeBinary operator next = .ok () afterOperator := by
          exact consumeBinary_ok_state_shape operator next
        have consumedValid := consumeBinary_reply_validFor operator
          leftValid.2.1 operatorFound
        rw [consumedResult] at consumedValid
        have afterOperatorAdequate :
            afterOperator.remainingCount < operandFuel :=
          remainingCount_lt_of_cursor_le (by rfl)
            (by dsimp [afterOperator]; omega) nextAdequate
        rcases contract.ordinary afterOperator consumedValid.2.1
            afterOperatorAdequate with
          ⟨right, final, rightResult⟩ |
          ⟨failure, rejected, rightResult⟩
        · exact Or.inl ⟨binaryNode left operator right, final, by
            simp only [nonAssociative, leftResult, operatorResult,
              consumedResult, rightResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [nonAssociative, leftResult, operatorResult,
              consumedResult, rightResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [nonAssociative, leftResult]⟩

theorem nonAssociative_ne_invariant_of_elementFuel
    (operand : Parser Expr) (operandFuel precedence : Nat)
    (contract : FuelElementTotalityContract operand operandFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < operandFuel)
    (error : ParserInvariantError) :
    nonAssociative operand precedence input ≠ .invariant error := by
  intro failed
  rcases nonAssociative_ordinary_of_elementFuel operand operandFuel
      precedence contract input inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionInternals
