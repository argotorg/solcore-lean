import Solcore.Syntax.DeclarativeCoreStatementSimpleGrammar
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact source spans and remainders for optional Core statement semicolons. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Maximal optional semicolon parsing fixes its optional span and remainder. -/
theorem OptionalStatementSemicolonParses.result_unique
    {input : Remainder} {left right : Option SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalStatementSemicolonParses input left afterLeft)
    (rightParsed : OptionalStatementSemicolonParses input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl⟩
      | present rightSpan rightToken =>
          exact False.elim (leftAbsent ⟨rightSpan, rightToken.1⟩)
  | present leftSpan leftToken =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (rightAbsent ⟨leftSpan, leftToken.1⟩)
      | present rightSpan rightToken =>
          rcases leftToken.result_unique rightToken with
            ⟨spanEq, outputEq⟩
          exact ⟨congrArg some spanEq, outputEq⟩

end Solcore.Syntax.DeclarativeGrammar
