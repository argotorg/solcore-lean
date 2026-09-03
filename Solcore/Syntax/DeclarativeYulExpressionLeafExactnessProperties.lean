import Solcore.Syntax.DeclarativePrimitiveExactnessProperties
import Solcore.Syntax.DeclarativeYulExpressionOrdinaryCoreProperties

/-! Exact values and endpoints of non-recursive inline-Yul expression leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The current token fixes an ordinary Yul name, including its source span. -/
theorem YulNameOrdinaryParses.value_unique {input : Remainder}
    {left right : Syntax.YulIdentifier} {afterLeft afterRight : Remainder}
    (leftParsed : YulNameOrdinaryParses input left afterLeft)
    (rightParsed : YulNameOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind [IdentifierParses, IdentifierParses.value_unique, TokenAt.token_unique]

/-- An ordinary Yul name fixes its complete value and final remainder. -/
theorem YulNameOrdinaryParses.result_unique {input : Remainder}
    {left right : Syntax.YulIdentifier} {afterLeft afterRight : Remainder}
    (leftParsed : YulNameOrdinaryParses input left afterLeft)
    (rightParsed : YulNameOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Rejected ordinary Yul names have one non-consuming endpoint. -/
theorem YulNameRejects.output_unique {input left right : Remainder}
    (leftRejected : YulNameRejects input left)
    (rightRejected : YulNameRejects input right) : left = right := by
  cases leftRejected
  cases rightRejected
  rfl

/-- Ordinary Yul names have exact successful values and rejecting endpoints. -/
theorem yulNameExactOutcomeSpec :
    ExactDeterministicOutcomeSpec YulNameOrdinaryParses YulNameRejects where
  toDeterministicOutcomeSpec := yulNameDeterministicOutcomeSpec
  successValueUnique := YulNameOrdinaryParses.value_unique
  rejectOutputUnique := YulNameRejects.output_unique

/-- The current literal token fixes its complete Yul literal value. -/
theorem YulLiteralParses.value_unique {input : Remainder}
    {left right : Syntax.YulLiteral} {afterLeft afterRight : Remainder}
    (leftParsed : YulLiteralParses input left afterLeft)
    (rightParsed : YulLiteralParses input right afterRight) : left = right := by
  cases leftParsed <;> cases rightParsed <;> grind [TokenAt.token_unique]

/-- An inline-Yul literal fixes both its value and final remainder. -/
theorem YulLiteralParses.result_unique {input : Remainder}
    {left right : Syntax.YulLiteral} {afterLeft afterRight : Remainder}
    (leftParsed : YulLiteralParses input left afterLeft)
    (rightParsed : YulLiteralParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
