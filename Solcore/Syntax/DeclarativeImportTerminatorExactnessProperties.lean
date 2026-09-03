import Solcore.Syntax.DeclarativeImportTerminatorOutcomeProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact import termination, including diagnosed nonconsuming recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A shared preceding span fixes both consumed and recovered terminator values. -/
theorem ImportTerminatorOrdinaryParses.result_unique (lastSpan : SourceSpan)
    {input afterLeft afterRight : Remainder} {left right : SourceSpan}
    (leftParsed : ImportTerminatorOrdinaryParses lastSpan input left afterLeft)
    (rightParsed : ImportTerminatorOrdinaryParses lastSpan input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | semicolon _ leftToken =>
      cases rightParsed with
      | semicolon _ rightToken => exact leftToken.result_unique rightToken
      | recovered absent _ => exact False.elim (absent ⟨_, leftToken.1⟩)
  | recovered absent _ =>
      cases rightParsed with
      | semicolon _ rightToken => exact False.elim (absent ⟨_, rightToken.1⟩)
      | recovered => exact ⟨rfl, rfl⟩

/-- Import-terminator rejection fixes the original complete remainder. -/
theorem ImportTerminatorRejects.output_unique {input left right : Remainder}
    (leftRejected : ImportTerminatorRejects input left)
    (rightRejected : ImportTerminatorRejects input right) : left = right := by
  cases leftRejected
  cases rightRejected
  rfl

/-- The full import-terminator contract is exact at each fixed preceding span. -/
theorem importTerminatorExactOutcomeSpec (lastSpan : SourceSpan) :
    ExactDeterministicOutcomeSpec (ImportTerminatorOrdinaryParses lastSpan)
      ImportTerminatorRejects where
  toDeterministicOutcomeSpec := importTerminatorDeterministicOutcomeSpec lastSpan
  successValueUnique := fun left right =>
    (left.result_unique lastSpan right).1
  rejectOutputUnique := ImportTerminatorRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
