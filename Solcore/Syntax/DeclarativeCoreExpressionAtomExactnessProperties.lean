import Solcore.Syntax.DeclarativeCoreBlockIsolationExactnessProperties
import Solcore.Syntax.DeclarativeCoreExpressionAtomCoreExactnessProperties
import Solcore.Syntax.DeclarativeCoreExpressionAtomRecoveryExactnessProperties
import Solcore.Syntax.DeclarativeCoreLambdaParameterExactnessProperties

/-! Exact public Core atoms, including fixed-previous-fuel lambda bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact nested expressions, parameters, types, and bodies fix all public atom
outcomes, including transactional rewind and diagnosed recovery. -/
theorem coreExpressionAtomExactOutcomeSpec (relations : CoreExpressionStepRelations)
    (nestedOutcomes : ExactDeterministicOutcomeSpec
      relations.nestedOrdinary relations.nestedRejects)
    (parameterOutcomes : ExactDeterministicOutcomeSpec
      relations.parameterOrdinary relations.parameterRejects)
    (typeOutcomes : ExactDeterministicOutcomeSpec
      relations.typeOrdinary relations.typeRejects)
    (blockOutcomes : ExactDeterministicOutcomeSpec
      relations.blockOrdinary relations.blockRejects) :
    ExactDeterministicOutcomeSpec relations.atomOrdinary relations.atomRejects :=
  expressionAtomExactOutcomeSpecOfSuccess
    (expressionAtomCoreDeterministicOutcomeSpec nestedOutcomes.toDeterministicOutcomeSpec
      parameterOutcomes.toDeterministicOutcomeSpec typeOutcomes.toDeterministicOutcomeSpec
      blockOutcomes.toDeterministicOutcomeSpec)
    (ExpressionAtomCoreOrdinaryParses.value_unique nestedOutcomes parameterOutcomes
      typeOutcomes blockOutcomes)

/-- Only expression and statement outcomes at the preceding fuel are needed
for the next step's atom grammar; no successor-level outcome is assumed. -/
theorem coreExpressionAtomExactOutcomeSpecWithFuel (fuel : Nat)
    (expressionOutcomes : ExactDeterministicOutcomeSpec
      (CoreExpressionOrdinaryParsesWithFuel fuel) (CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ExactDeterministicOutcomeSpec
      (CoreStatementOrdinaryParsesWithFuel fuel) (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec
      (coreExpressionStepRelationsWithFuel fuel).atomOrdinary
      (coreExpressionStepRelationsWithFuel fuel).atomRejects :=
  coreExpressionAtomExactOutcomeSpec (coreExpressionStepRelationsWithFuel fuel)
    expressionOutcomes lambdaParameterPublicExactOutcomeSpec typeExprExactOutcomeSpec
    (isolatedCoreBlockExactOutcomeSpec (coreBlockExactOutcomeSpec .require statementOutcomes))

end Solcore.Syntax.DeclarativeGrammar
