import Solcore.Syntax.DeclarativeYulExpressionFuelGrammar
import Solcore.Syntax.DeclarativeYulExpressionLayerExactnessProperties

/-! Exact fixed-fuel and public inline-Yul expression outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every recursive Yul-expression fuel has exact success and reject outcomes. -/
theorem yulExpressionExactOutcomeSpecWithFuel (fuel : Nat) :
    ExactDeterministicOutcomeSpec
      (YulExpressionOrdinaryParsesWithFuel fuel)
      (YulExpressionRejectsWithFuel fuel) := by
  induction fuel with
  | zero =>
      exact {
        toDeterministicOutcomeSpec := yulExpressionOutcomeSpecWithFuel 0
        successValueUnique := by
          intro input left right afterLeft afterRight leftParsed
          exact False.elim (YulExpressionOrdinaryParsesWithFuel.zero leftParsed)
        rejectOutputUnique := by
          intro input left right leftRejected
          exact False.elim (YulExpressionRejectsWithFuel.zero leftRejected)
      }
  | succ fuel inductionHypothesis =>
      exact yulExpressionLayerExactOutcomeSpec inductionHypothesis

/-- Fixed-fuel ordinary Yul expressions fix their complete AST. -/
theorem YulExpressionOrdinaryParsesWithFuel.value_unique {fuel : Nat}
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionOrdinaryParsesWithFuel fuel input left afterLeft)
    (rightParsed : YulExpressionOrdinaryParsesWithFuel fuel input right
      afterRight) : left = right :=
  (yulExpressionExactOutcomeSpecWithFuel fuel).successValueUnique
    leftParsed rightParsed

/-- Fixed-fuel ordinary Yul expressions fix their complete result. -/
theorem YulExpressionOrdinaryParsesWithFuel.result_unique {fuel : Nat}
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionOrdinaryParsesWithFuel fuel input left afterLeft)
    (rightParsed : YulExpressionOrdinaryParsesWithFuel fuel input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  (yulExpressionExactOutcomeSpecWithFuel fuel).successResultUnique
    leftParsed rightParsed

/-- Fixed-fuel Yul-expression rejection fixes its complete endpoint. -/
theorem YulExpressionRejectsWithFuel.output_unique {fuel : Nat}
    {input left right : Remainder}
    (leftRejected : YulExpressionRejectsWithFuel fuel input left)
    (rightRejected : YulExpressionRejectsWithFuel fuel input right) :
    left = right :=
  (yulExpressionExactOutcomeSpecWithFuel fuel).rejectOutputUnique
    leftRejected rightRejected

/-- The input-selected public fuel preserves exact ordinary expression outcomes. -/
theorem yulExpressionPublicExactOutcomeSpec :
    ExactDeterministicOutcomeSpec YulExpressionOrdinaryParses
      YulExpressionPublicRejects where
  toDeterministicOutcomeSpec := yulExpressionPublicOutcomeSpec
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (yulExpressionExactOutcomeSpecWithFuel
      (yulExpressionPublicFuel input)).successValueUnique leftParsed rightParsed
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    exact (yulExpressionExactOutcomeSpecWithFuel
      (yulExpressionPublicFuel input)).rejectOutputUnique
        leftRejected rightRejected

/-- Exact public outcomes stated with the concrete boundary-rejection relation. -/
theorem yulExpressionExactOutcomeSpec :
    ExactDeterministicOutcomeSpec YulExpressionOrdinaryParses
      YulExpressionRejects where
  toDeterministicOutcomeSpec := yulExpressionPublicDeterministicOutcomeSpec
  successValueUnique := yulExpressionPublicExactOutcomeSpec.successValueUnique
  rejectOutputUnique := YulExpressionRejects.output_unique

/-- Public ordinary Yul expressions fix the complete AST and final remainder. -/
theorem YulExpressionOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionOrdinaryParses input left afterLeft)
    (rightParsed : YulExpressionOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  yulExpressionExactOutcomeSpec.successResultUnique leftParsed rightParsed

/-- Public ordinary Yul expressions fix the complete AST. -/
theorem YulExpressionOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionOrdinaryParses input left afterLeft)
    (rightParsed : YulExpressionOrdinaryParses input right afterRight) :
    left = right :=
  yulExpressionExactOutcomeSpec.successValueUnique leftParsed rightParsed

/-- Public fuel-indexed Yul-expression rejection fixes its complete endpoint. -/
theorem YulExpressionPublicRejects.output_unique
    {input left right : Remainder}
    (leftRejected : YulExpressionPublicRejects input left)
    (rightRejected : YulExpressionPublicRejects input right) : left = right :=
  yulExpressionPublicExactOutcomeSpec.rejectOutputUnique leftRejected rightRejected

end Solcore.Syntax.DeclarativeGrammar
