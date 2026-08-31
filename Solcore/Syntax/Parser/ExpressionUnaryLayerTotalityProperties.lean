import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.ExpressionUnaryTotalityProperties

/-! Fuel-aware totality for complete prefix-unary expression layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- Prefix scanning preserves the fuel bound required by the postfix parser. -/
theorem expressionUnary_ordinary_of_postfixFuel
    (nested : Parser Expr) (block : Parser Block) (postfixFuel : Nat)
    (postfixContract : FuelElementTotalityContract
      (expressionPostfix nested block) postfixFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < postfixFuel) :
    (∃ expression next,
      expressionUnary nested block input = .ok expression next) ∨
    (∃ failure next,
      expressionUnary nested block input = .reject failure next) := by
  rcases unaryOperators_production_exists_ok [] input with
    ⟨operators, afterOperators, operatorsResult⟩
  have operatorsValid := unaryOperators_validFor
    (input.remainingCount + 1) [] input inputValid (by
      simp [List.ValidFor])
  rw [operatorsResult] at operatorsValid
  have operatorsWindow := unaryOperators_preservesTokenWindow
    (input.remainingCount + 1) [] input
  rw [operatorsResult] at operatorsWindow
  have operatorsCursor := unaryOperators_cursorMonotoneOnSuccess
    (input.remainingCount + 1) [] input operators afterOperators
      operatorsResult
  have afterOperatorsAdequate :
      afterOperators.remainingCount < postfixFuel :=
    remainingCount_lt_of_cursor_le operatorsWindow.2 operatorsCursor adequate
  rcases postfixContract.ordinary afterOperators operatorsValid.2.1
      afterOperatorsAdequate with
    ⟨base, next, postfixResult⟩ | ⟨failure, rejected, postfixResult⟩
  · exact Or.inl ⟨applyUnaryOperators operators base, next, by
      simp only [expressionUnary, operatorsResult, postfixResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [expressionUnary, operatorsResult, postfixResult]⟩

theorem expressionUnary_ne_invariant_of_postfixFuel
    (nested : Parser Expr) (block : Parser Block) (postfixFuel : Nat)
    (postfixContract : FuelElementTotalityContract
      (expressionPostfix nested block) postfixFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < postfixFuel)
    (error : ParserInvariantError) :
    expressionUnary nested block input ≠ .invariant error := by
  intro failed
  rcases expressionUnary_ordinary_of_postfixFuel nested block postfixFuel
      postfixContract input inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionInternals
