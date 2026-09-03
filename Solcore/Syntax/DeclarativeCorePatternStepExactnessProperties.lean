import Solcore.Syntax.DeclarativeCorePatternConstructorValueProperties
import Solcore.Syntax.DeclarativeCorePatternCoreValueProperties
import Solcore.Syntax.DeclarativeCorePatternLayerExactnessProperties
import Solcore.Syntax.DeclarativeCorePatternParenthesizedValueProperties
import Solcore.Syntax.DeclarativeCorePatternStepOutcomeProperties

/-! Exact outcomes of one recursive Core pattern step. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact preceding pattern and expression outcomes make the complete next
pattern step exact without a raw Core-rejection uniqueness premise. -/
theorem corePatternStepExactOutcomeSpec
    (relations : CorePatternStepRelations)
    (nestedOutcomes : ExactDeterministicOutcomeSpec relations.nestedOrdinary
      relations.nestedRejects)
    (expressionOutcomes : ExactDeterministicOutcomeSpec
      relations.expressionOrdinary relations.expressionRejects) :
    ExactDeterministicOutcomeSpec
      (CorePatternStepOrdinaryParses relations)
      (CorePatternStepRejects relations) := by
  have coreOutcomes : DeterministicOutcomeSpec relations.coreOrdinary
      relations.coreRejects :=
    patternCoreDeterministicOutcomeSpec
      (parenthesizedPatternDeterministicOutcomeSpec
        nestedOutcomes.toDeterministicOutcomeSpec)
      (dotConstructorPatternDeterministicOutcomeSpec
        nestedOutcomes.toDeterministicOutcomeSpec)
      (comptimePatternDeterministicOutcomeSpec
        expressionOutcomes.toDeterministicOutcomeSpec)
      (qualifiedPatternDeterministicOutcomeSpec
        nestedOutcomes.toDeterministicOutcomeSpec)
  exact patternLayerExactOutcomeSpec coreOutcomes
    (PatternCoreOrdinaryParses.value_unique
      (parenthesizedOrdinary := relations.parenthesizedOrdinary)
      (dotConstructorOrdinary := relations.dotConstructorOrdinary)
      (comptimeOrdinary := relations.comptimeOrdinary)
      (qualifiedOrdinary := relations.qualifiedOrdinary)
      (ParenthesizedPatternOrdinaryParses.value_unique nestedOutcomes)
      (DotConstructorPatternOrdinaryParses.value_unique nestedOutcomes)
      (ComptimePatternOrdinaryParses.value_unique expressionOutcomes)
      (QualifiedPatternOrdinaryParses.value_unique nestedOutcomes))

/-- One complete pattern step fixes its successful AST and final remainder. -/
theorem CorePatternStepOrdinaryParses.result_unique
    {relations : CorePatternStepRelations}
    (nestedOutcomes : ExactDeterministicOutcomeSpec relations.nestedOrdinary
      relations.nestedRejects)
    (expressionOutcomes : ExactDeterministicOutcomeSpec
      relations.expressionOrdinary relations.expressionRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : CorePatternStepOrdinaryParses relations input left afterLeft)
    (rightParsed : CorePatternStepOrdinaryParses relations input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  (corePatternStepExactOutcomeSpec relations nestedOutcomes expressionOutcomes)
    |>.successResultUnique leftParsed rightParsed

end Solcore.Syntax.DeclarativeGrammar
