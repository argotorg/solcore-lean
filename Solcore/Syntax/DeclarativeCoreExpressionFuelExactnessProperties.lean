import Solcore.Syntax.DeclarativeCoreExpressionStepExactnessProperties
import Solcore.Syntax.DeclarativeCoreTermFuelEquationProperties

/-! Base and successor exactness for mutually recursive Core expression fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Fuel zero has neither an ordinary expression success nor rejection. -/
theorem coreExpressionExactOutcomeSpecWithFuel_zero :
    ExactDeterministicOutcomeSpec (CoreExpressionOrdinaryParsesWithFuel 0)
      (CoreExpressionRejectsWithFuel 0) where
  toDeterministicOutcomeSpec := coreExpressionOutcomeSpecWithFuel 0
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed
    exact False.elim (CoreExpressionOrdinaryParsesWithFuel.zero leftParsed)
  rejectOutputUnique := by
    intro input left right leftRejected
    exact False.elim (CoreExpressionRejectsWithFuel.zero leftRejected)

/-- Exact expressions and statements at one preceding fuel yield the next
expression layer. Types and lambda parameters need no recursive assumption. -/
theorem coreExpressionExactOutcomeSpecWithFuel_succ (fuel : Nat)
    (expressionOutcomes : ExactDeterministicOutcomeSpec
      (CoreExpressionOrdinaryParsesWithFuel fuel) (CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ExactDeterministicOutcomeSpec
      (CoreStatementOrdinaryParsesWithFuel fuel) (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec (CoreExpressionOrdinaryParsesWithFuel (fuel + 1))
      (CoreExpressionRejectsWithFuel (fuel + 1)) := by
  change ExactDeterministicOutcomeSpec
    (CoreExpressionStepOrdinaryParses (coreExpressionStepRelationsWithFuel fuel))
    (CoreExpressionStepRejects (coreExpressionStepRelationsWithFuel fuel))
  exact coreExpressionStepExactOutcomeSpec (coreExpressionStepRelationsWithFuel fuel)
    expressionOutcomes lambdaParameterPublicExactOutcomeSpec typeExprExactOutcomeSpec
    (isolatedCoreBlockExactOutcomeSpec (coreBlockExactOutcomeSpec .require statementOutcomes))

end Solcore.Syntax.DeclarativeGrammar
