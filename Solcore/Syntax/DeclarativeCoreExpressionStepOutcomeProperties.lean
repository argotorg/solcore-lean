import Solcore.Syntax.DeclarativeCoreExpressionAtomCoreOutcomeProperties
import Solcore.Syntax.DeclarativeCoreExpressionAtomPublicOutcomeProperties
import Solcore.Syntax.DeclarativeCoreExpressionLayerOutcomeProperties
import Solcore.Syntax.DeclarativeCoreExpressionPostfixOutcomeProperties
import Solcore.Syntax.DeclarativeCoreExpressionStepOutcomeGrammar

/-! Deterministic outcomes for one complete Core expression step. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Compose subordinate deterministic contracts through atom dispatch,
public recovery, postfix parsing, and the complete operator stack. -/
theorem coreExpressionStepDeterministicOutcomeSpec
    (relations : CoreExpressionStepRelations)
    (nestedOutcomes : DeterministicOutcomeSpec relations.nestedOrdinary
      relations.nestedRejects)
    (parameterOutcomes : DeterministicOutcomeSpec relations.parameterOrdinary
      relations.parameterRejects)
    (typeOutcomes : DeterministicOutcomeSpec relations.typeOrdinary
      relations.typeRejects)
    (blockOutcomes : DeterministicOutcomeSpec relations.blockOrdinary
      relations.blockRejects) :
    DeterministicOutcomeSpec
      (CoreExpressionStepOrdinaryParses relations)
      (CoreExpressionStepRejects relations) := by
  have coreOutcomes : DeterministicOutcomeSpec relations.atomCoreOrdinary
      relations.atomCoreRejects :=
    expressionAtomCoreDeterministicOutcomeSpec nestedOutcomes
      parameterOutcomes typeOutcomes blockOutcomes
  have atomOutcomes : DeterministicOutcomeSpec relations.atomOrdinary
      relations.atomRejects :=
    expressionAtomDeterministicOutcomeSpec coreOutcomes
  have postfixOutcomes : DeterministicOutcomeSpec relations.postfixOrdinary
      relations.postfixRejects :=
    expressionPostfixDeterministicOutcomeSpec atomOutcomes nestedOutcomes
  exact expressionLayerDeterministicOutcomeSpec nestedOutcomes postfixOutcomes

end Solcore.Syntax.DeclarativeGrammar
