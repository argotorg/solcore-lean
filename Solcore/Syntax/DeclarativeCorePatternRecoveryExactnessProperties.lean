import Solcore.Syntax.DeclarativeCorePatternRecoveryOutcomeProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact error values and endpoints for ordinary Core pattern recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- With fixed first and last retained spans, recovery fixes its error pattern
and final remainder. -/
theorem PatternRecoveryScanParses.result_unique :
    ∀ {first last : SourceSpan} {input : Remainder}
      {left right : Syntax.Pattern} {afterLeft afterRight : Remainder},
      PatternRecoveryScanParses first last input left afterLeft →
      PatternRecoveryScanParses first last input right afterRight →
      left = right ∧ afterLeft = afterRight := by
  intro first last input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing right afterRight with
  | stop leftStops =>
      intro rightParsed
      cases rightParsed with
      | stop => exact ⟨rfl, rfl⟩
      | next rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next rightContinues rightCurrent rightTail =>
          have currentEq := leftCurrent.token_unique rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- With fixed retained endpoint spans, recovery fixes its complete error AST. -/
theorem PatternRecoveryScanParses.value_unique
    {first last : SourceSpan} {input : Remainder}
    {left right : Syntax.Pattern} {afterLeft afterRight : Remainder}
    (leftParsed : PatternRecoveryScanParses first last input left afterLeft)
    (rightParsed : PatternRecoveryScanParses first last input right afterRight) :
    left = right :=
  (leftParsed.result_unique rightParsed).1

/-- The mandatory first token fixes both scan spans and the recovery result. -/
theorem PatternRecoveryParses.result_unique
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : PatternRecoveryParses input left afterLeft)
    (rightParsed : PatternRecoveryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightCurrent rightScan =>
          have currentEq := leftCurrent.token_unique rightCurrent
          cases currentEq
          exact leftScan.result_unique rightScan

/-- Complete pattern recovery fixes its error AST. -/
theorem PatternRecoveryParses.value_unique
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : PatternRecoveryParses input left afterLeft)
    (rightParsed : PatternRecoveryParses input right afterRight) :
    left = right :=
  (leftParsed.result_unique rightParsed).1

/-- An unavailable mandatory token yields one nonconsuming rejection endpoint. -/
theorem PatternRecoveryRejects.output_unique
    {input left right : Remainder}
    (leftRejected : PatternRecoveryRejects input left)
    (rightRejected : PatternRecoveryRejects input right) : left = right := by
  rw [leftRejected.output_eq, rightRejected.output_eq]

/-- Ordinary malformed-pattern recovery has fully exact outcomes. -/
theorem patternRecoveryExactOutcomeSpec :
    ExactDeterministicOutcomeSpec PatternRecoveryParses PatternRecoveryRejects where
  toDeterministicOutcomeSpec := patternRecoveryDeterministicOutcomeSpec
  successValueUnique := PatternRecoveryParses.value_unique
  rejectOutputUnique := PatternRecoveryRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
