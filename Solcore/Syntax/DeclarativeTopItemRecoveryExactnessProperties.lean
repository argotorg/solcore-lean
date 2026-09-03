import Solcore.Syntax.DeclarativePrimitiveExactnessProperties
import Solcore.Syntax.DeclarativeTopItemRecoveryOutcomeProperties

/-! Exact recovery values and endpoints for top-level source-file items. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- With the same first and last consumed spans, a recovery scan fixes its
error item and final remainder. -/
theorem TopItemRecoveryScanParses.result_unique
    {first last : SourceSpan} {input : Remainder}
    {left right : Syntax.TopItem} {afterLeft afterRight : Remainder}
    (leftParsed : TopItemRecoveryScanParses first last input left afterLeft)
    (rightParsed : TopItemRecoveryScanParses first last input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | stop leftStops =>
      cases rightParsed with
      | stop => exact ⟨rfl, rfl⟩
      | next rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail ih =>
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next rightContinues rightCurrent rightTail =>
          have tokenEq := leftCurrent.token_unique rightCurrent
          cases tokenEq
          exact ih rightTail

/-- A recovery scan at fixed span history has one exact error-item AST. -/
theorem TopItemRecoveryScanParses.value_unique
    {first last : SourceSpan} {input : Remainder}
    {left right : Syntax.TopItem} {afterLeft afterRight : Remainder}
    (leftParsed : TopItemRecoveryScanParses first last input left afterLeft)
    (rightParsed : TopItemRecoveryScanParses first last input right afterRight) :
    left = right :=
  (leftParsed.result_unique rightParsed).1

/-- The mandatory first token fixes the initial spans; complete recovery fixes
both its exact error item and final remainder. -/
theorem TopItemRecoveryParses.result_unique
    {input : Remainder} {left right : Syntax.TopItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : TopItemRecoveryParses input left afterLeft)
    (rightParsed : TopItemRecoveryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightCurrent rightScan =>
          have tokenEq := leftCurrent.token_unique rightCurrent
          cases tokenEq
          exact leftScan.result_unique rightScan

/-- Complete top-item recovery fixes its full error-item AST. -/
theorem TopItemRecoveryParses.value_unique
    {input : Remainder} {left right : Syntax.TopItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : TopItemRecoveryParses input left afterLeft)
    (rightParsed : TopItemRecoveryParses input right afterRight) :
    left = right :=
  (leftParsed.result_unique rightParsed).1

/-- Every recovery rejection selects the same original input endpoint. -/
theorem TopItemRecoveryRejects.output_unique {input left right : Remainder}
    (leftRejected : TopItemRecoveryRejects input left)
    (rightRejected : TopItemRecoveryRejects input right) : left = right :=
  leftRejected.output_eq.trans rightRejected.output_eq.symm

/-- Top-item recovery has unconditional exact ordinary outcomes. -/
theorem topItemRecoveryExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TopItemRecoveryParses TopItemRecoveryRejects where
  toDeterministicOutcomeSpec := topItemRecoveryDeterministicOutcomeSpec
  successValueUnique := TopItemRecoveryParses.value_unique
  rejectOutputUnique := TopItemRecoveryRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
