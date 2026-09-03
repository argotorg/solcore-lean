import Solcore.Syntax.DeclarativeFinishExportOutcomeProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact export finishing for a fixed start span and declaration payload. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The exact semicolon fixes the full export AST at a shared start and payload. -/
theorem FinishExportParses.result_unique
    {start : SourceSpan} {value : Syntax.ExportDeclValue}
    {input afterLeft afterRight : Remainder} {left right : Syntax.ExportDecl}
    (leftParsed : FinishExportParses start value input left afterLeft)
    (rightParsed : FinishExportParses start value input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  have outputEq := leftParsed.output_unique rightParsed
  rcases leftParsed with ⟨leftSpan, leftToken, _, leftValue⟩
  rcases rightParsed with ⟨rightSpan, rightToken, _, rightValue⟩
  have spanEq := congrArg (fun token : Token => token.span)
    (leftToken.token_unique rightToken)
  simp_all

/-- Missing export semicolons reject at the unchanged complete remainder. -/
theorem FinishExportRejects.output_unique {input left right : Remainder}
    (leftRejected : FinishExportRejects input left)
    (rightRejected : FinishExportRejects input right) : left = right := by
  cases leftRejected
  cases rightRejected
  rfl

/-- Export finishing has exact values and endpoints at fixed supplied data. -/
theorem finishExportExactOutcomeSpec (start : SourceSpan)
    (value : Syntax.ExportDeclValue) :
    ExactDeterministicOutcomeSpec (FinishExportOrdinaryParses start value)
      FinishExportRejects where
  toDeterministicOutcomeSpec := finishExportDeterministicOutcomeSpec start value
  successValueUnique := fun left right => (left.result_unique right).1
  rejectOutputUnique := FinishExportRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
