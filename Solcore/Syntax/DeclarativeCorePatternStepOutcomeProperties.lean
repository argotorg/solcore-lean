import Solcore.Syntax.DeclarativeCorePatternComptimeOutcomeProperties
import Solcore.Syntax.DeclarativeCorePatternCoreOutcomeProperties
import Solcore.Syntax.DeclarativeCorePatternDotConstructorOutcomeProperties
import Solcore.Syntax.DeclarativeCorePatternParenthesizedOutcomeProperties
import Solcore.Syntax.DeclarativeCorePatternPublicOutcomeProperties
import Solcore.Syntax.DeclarativeCorePatternQualifiedOutcomeProperties
import Solcore.Syntax.DeclarativeCorePatternStepOutcomeGrammar

/-! Deterministic outcomes for one complete Core pattern recursion step. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Compose nested pattern and expression contracts through the four recursive
branches, ordered core dispatcher, and public recovery boundary. -/
theorem corePatternStepDeterministicOutcomeSpec
    (relations : CorePatternStepRelations)
    (nestedOutcomes : DeterministicOutcomeSpec relations.nestedOrdinary
      relations.nestedRejects)
    (expressionOutcomes : DeterministicOutcomeSpec
      relations.expressionOrdinary relations.expressionRejects) :
    DeterministicOutcomeSpec
      (CorePatternStepOrdinaryParses relations)
      (CorePatternStepRejects relations) := by
  have parenthesizedOutcomes : DeterministicOutcomeSpec
      relations.parenthesizedOrdinary relations.parenthesizedRejects :=
    parenthesizedPatternDeterministicOutcomeSpec nestedOutcomes
  have dotOutcomes : DeterministicOutcomeSpec
      relations.dotConstructorOrdinary relations.dotConstructorRejects :=
    dotConstructorPatternDeterministicOutcomeSpec nestedOutcomes
  have comptimeOutcomes : DeterministicOutcomeSpec relations.comptimeOrdinary
      relations.comptimeRejects :=
    comptimePatternDeterministicOutcomeSpec expressionOutcomes
  have qualifiedOutcomes : DeterministicOutcomeSpec
      relations.qualifiedOrdinary relations.qualifiedRejects :=
    qualifiedPatternDeterministicOutcomeSpec nestedOutcomes
  have coreOutcomes : DeterministicOutcomeSpec relations.coreOrdinary
      relations.coreRejects :=
    patternCoreDeterministicOutcomeSpec parenthesizedOutcomes dotOutcomes
      comptimeOutcomes qualifiedOutcomes
  exact patternLayerDeterministicOutcomeSpec coreOutcomes

end Solcore.Syntax.DeclarativeGrammar
