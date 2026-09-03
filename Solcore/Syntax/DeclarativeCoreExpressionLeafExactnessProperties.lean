import Solcore.Syntax.DeclarativeCoreIdentifierExpressionOutcomeProperties
import Solcore.Syntax.DeclarativeCoreLiteralOutcomeProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact literal, Boolean-first name, and identifier Core expression leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The current Core literal token fixes its spelling and complete source span. -/
theorem CoreLiteralParses.value_unique {input : Remainder}
    {left right : Syntax.CoreLiteral} {afterLeft afterRight : Remainder}
    (leftParsed : CoreLiteralParses input left afterLeft)
    (rightParsed : CoreLiteralParses input right afterRight) : left = right := by
  cases leftParsed <;> cases rightParsed <;> grind [TokenAt.token_unique]

/-- A Core literal fixes its exact value and complete final remainder. -/
theorem CoreLiteralParses.result_unique {input : Remainder}
    {left right : Syntax.CoreLiteral} {afterLeft afterRight : Remainder}
    (leftParsed : CoreLiteralParses input left afterLeft)
    (rightParsed : CoreLiteralParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    CoreLiteralOrdinaryParses.output_unique leftParsed rightParsed⟩

/-- Ordinary Core literal outcomes fix both values and rejecting endpoints. -/
theorem coreLiteralExactOutcomeSpec :
    ExactDeterministicOutcomeSpec CoreLiteralOrdinaryParses CoreLiteralRejects where
  toDeterministicOutcomeSpec := coreLiteralDeterministicOutcomeSpec
  successValueUnique := CoreLiteralParses.value_unique
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    cases leftRejected
    cases rightRejected
    rfl

/-- Wrapping a Core literal preserves its exact AST and source span. -/
theorem LiteralExpressionOrdinaryParses.value_unique {input : Remainder}
    {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : LiteralExpressionOrdinaryParses input left afterLeft)
    (rightParsed : LiteralExpressionOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftLiteral =>
      cases rightParsed with
      | parsed rightLiteral =>
          cases leftLiteral.value_unique rightLiteral
          rfl

/-- Literal-expression leaves have exact ordinary outcomes. -/
theorem literalExpressionExactOutcomeSpec :
    ExactDeterministicOutcomeSpec LiteralExpressionOrdinaryParses LiteralExpressionRejects where
  toDeterministicOutcomeSpec := literalExpressionDeterministicOutcomeSpec
  successValueUnique := LiteralExpressionOrdinaryParses.value_unique
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    cases leftRejected
    cases rightRejected
    rfl

/-- Boolean-keyword names have a unique exact spelling and span. -/
theorem BooleanIdentifierParses.value_unique {input : Remainder}
    {left right : Syntax.Identifier} {afterLeft afterRight : Remainder}
    (leftParsed : BooleanIdentifierParses input left afterLeft)
    (rightParsed : BooleanIdentifierParses input right afterRight) : left = right := by
  cases leftParsed <;> cases rightParsed <;> grind [TokenAt.token_unique]

/-- Boolean-first name priority fixes the complete identifier value. -/
theorem ExpressionNameOrdinaryParses.value_unique {input : Remainder}
    {left right : Syntax.Identifier} {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionNameOrdinaryParses input left afterLeft)
    (rightParsed : ExpressionNameOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | boolean leftBoolean =>
      cases rightParsed with
      | boolean rightBoolean => exact leftBoolean.value_unique rightBoolean
      | identifier rightTrueAbsent rightFalseAbsent _ =>
          cases leftBoolean with
          | trueKeyword token => exact False.elim (rightTrueAbsent ⟨_, token⟩)
          | falseKeyword token => exact False.elim (rightFalseAbsent ⟨_, token⟩)
  | identifier leftTrueAbsent leftFalseAbsent leftIdentifier =>
      cases rightParsed with
      | boolean rightBoolean =>
          cases rightBoolean with
          | trueKeyword token => exact False.elim (leftTrueAbsent ⟨_, token⟩)
          | falseKeyword token => exact False.elim (leftFalseAbsent ⟨_, token⟩)
      | identifier _ _ rightIdentifier => exact leftIdentifier.value_unique rightIdentifier

/-- An ordinary expression name fixes its value and final remainder. -/
theorem ExpressionNameOrdinaryParses.result_unique {input : Remainder}
    {left right : Syntax.Identifier} {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionNameOrdinaryParses input left afterLeft)
    (rightParsed : ExpressionNameOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Boolean-first expression names have exact ordinary outcomes. -/
theorem expressionNameExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ExpressionNameOrdinaryParses ExpressionNameRejects where
  toDeterministicOutcomeSpec := expressionNameDeterministicOutcomeSpec
  successValueUnique := ExpressionNameOrdinaryParses.value_unique
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    cases leftRejected
    cases rightRejected
    rfl

/-- The ordinary identifier-expression wrapper preserves its exact name and span. -/
theorem IdentifierExpressionOrdinaryParses.value_unique {input : Remainder}
    {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : IdentifierExpressionOrdinaryParses input left afterLeft)
    (rightParsed : IdentifierExpressionOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftName =>
      cases rightParsed with
      | parsed rightName =>
          cases ExpressionNameOrdinaryParses.value_unique leftName rightName
          rfl

/-- Identifier-expression leaves have exact ordinary outcomes. -/
theorem identifierExpressionExactOutcomeSpec :
    ExactDeterministicOutcomeSpec IdentifierExpressionOrdinaryParses IdentifierExpressionRejects where
  toDeterministicOutcomeSpec := identifierExpressionDeterministicOutcomeSpec
  successValueUnique := IdentifierExpressionOrdinaryParses.value_unique
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    cases leftRejected with
    | nameRejected leftName =>
        cases rightRejected with
        | nameRejected rightName =>
            exact expressionNameExactOutcomeSpec.rejectOutputUnique leftName rightName

end Solcore.Syntax.DeclarativeGrammar
