import Solcore.Syntax.DeclarativeCoreExpressionAtomExactnessProperties
import Solcore.Syntax.DeclarativeCoreExpressionLayerExactnessProperties
import Solcore.Syntax.DeclarativeCoreExpressionPostfixExactnessProperties

/-! Full exactness of a complete Core expression step over exact children. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact child outcomes compose through atom priority, recovery, postfix
extension, and the entire operator stack without stronger rejection premises. -/
theorem coreExpressionStepExactOutcomeSpec (relations : CoreExpressionStepRelations)
    (nestedOutcomes : ExactDeterministicOutcomeSpec
      relations.nestedOrdinary relations.nestedRejects)
    (parameterOutcomes : ExactDeterministicOutcomeSpec
      relations.parameterOrdinary relations.parameterRejects)
    (typeOutcomes : ExactDeterministicOutcomeSpec
      relations.typeOrdinary relations.typeRejects)
    (blockOutcomes : ExactDeterministicOutcomeSpec
      relations.blockOrdinary relations.blockRejects) :
    ExactDeterministicOutcomeSpec (CoreExpressionStepOrdinaryParses relations)
      (CoreExpressionStepRejects relations) :=
  expressionLayerExactOutcomeSpec nestedOutcomes
    (expressionPostfixExactOutcomeSpec
      (coreExpressionAtomExactOutcomeSpec relations nestedOutcomes
        parameterOutcomes typeOutcomes blockOutcomes) nestedOutcomes)

end Solcore.Syntax.DeclarativeGrammar
