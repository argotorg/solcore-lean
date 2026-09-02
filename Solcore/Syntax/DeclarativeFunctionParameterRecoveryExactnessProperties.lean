import Solcore.Syntax.DeclarativeCoreLambdaParameterRecoveryOutcomeProperties
import Solcore.Syntax.DeclarativeExactOutcomeSpec
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact values for malformed named-function-parameter recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- With fixed first and outer-last spans, a recovery scan fixes its error
parameter and final remainder. -/
theorem FunctionParameterRecoveryScanParses.result_unique :
    ∀ {first last : SourceSpan} {input : Remainder}
      {left right : Syntax.FunctionParameter}
      {afterLeft afterRight : Remainder},
      FunctionParameterRecoveryScanParses first last input left afterLeft →
      FunctionParameterRecoveryScanParses first last input right afterRight →
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

/-- With fixed first and outer-last spans, a recovery scan fixes its value. -/
theorem FunctionParameterRecoveryScanParses.value_unique
    {first last : SourceSpan} {input : Remainder}
    {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterRecoveryScanParses first last input left
      afterLeft)
    (rightParsed : FunctionParameterRecoveryScanParses first last input right
      afterRight) : left = right :=
  (leftParsed.result_unique rightParsed).1

/-- Complete malformed-parameter recovery fixes its value and remainder. -/
theorem FunctionParameterRecoveryParses.result_unique
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterRecoveryParses input left afterLeft)
    (rightParsed : FunctionParameterRecoveryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightCurrent rightScan =>
          have currentEq := leftCurrent.token_unique rightCurrent
          cases currentEq
          exact leftScan.result_unique rightScan

/-- Complete malformed-parameter recovery fixes its error parameter. -/
theorem FunctionParameterRecoveryParses.value_unique
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterRecoveryParses input left afterLeft)
    (rightParsed : FunctionParameterRecoveryParses input right afterRight) :
    left = right :=
  (leftParsed.result_unique rightParsed).1

/-- An unavailable recovery first token has one nonconsuming endpoint. -/
theorem FunctionParameterRecoveryRejects.output_unique
    {input left right : Remainder}
    (leftRejected : FunctionParameterRecoveryRejects input left)
    (rightRejected : FunctionParameterRecoveryRejects input right) :
    left = right := by
  rw [leftRejected.output_eq, rightRejected.output_eq]

/-- Standalone malformed-parameter recovery has fully exact outcomes. -/
theorem functionParameterRecoveryExactOutcomeSpec :
    ExactDeterministicOutcomeSpec FunctionParameterRecoveryParses
      FunctionParameterRecoveryRejects where
  toDeterministicOutcomeSpec :=
    functionParameterRecoveryDeterministicOutcomeSpec
  successValueUnique := FunctionParameterRecoveryParses.value_unique
  rejectOutputUnique := FunctionParameterRecoveryRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
