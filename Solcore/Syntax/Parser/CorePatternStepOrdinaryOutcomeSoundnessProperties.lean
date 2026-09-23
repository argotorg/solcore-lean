import Solcore.Syntax.DeclarativeCorePatternStepOutcomeProperties
import Solcore.Syntax.Parser.CorePatternComptimeOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CorePatternCoreOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CorePatternDotConstructorOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CorePatternParenthesizedOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CorePatternPublicOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CorePatternQualifiedOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.Pattern

/-! One-call executable outcomes for a complete Core pattern step. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Compose the four recursive branches, ordered core dispatcher, and public
recovery boundary into one executable ordinary outcome. -/
theorem corePatternStep_ordinaryOutcome_sound
    (nested : Parser Pattern) (expression : Parser Expr)
    (relations : DeclarativeGrammar.CorePatternStepRelations)
    (nestedSuccessSound : ∀ {input output : State} {pattern : Pattern},
      nested input = .ok pattern output → relations.nestedOrdinary
        input.declarativeRemainder pattern output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → relations.nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedWindow : Parser.PreservesTokenWindow nested)
    (expressionSuccessSound :
      ∀ {input output : State} {value : Expr},
        expression input = .ok value output → relations.expressionOrdinary
          input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        expression input = .reject failure rejected →
          relations.expressionRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    (∀ {input output : State} {pattern : Pattern},
      patternLayer nested expression input = .ok pattern output →
        DeclarativeGrammar.CorePatternStepOrdinaryParses relations
          input.declarativeRemainder pattern output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      patternLayer nested expression input = .reject failure rejected →
        DeclarativeGrammar.CorePatternStepRejects relations
          input.declarativeRemainder rejected.declarativeRemainder) := by
  have parenthesizedSound :=
    PatternInternals.parenthesizedPattern_ordinaryOutcome_sound nested
      relations.nestedOrdinary relations.nestedRejects nestedSuccessSound
        nestedRejectSound
  have dotSound :=
    PatternInternals.dotConstructorPattern_ordinaryOutcome_sound nested
      relations.nestedOrdinary relations.nestedRejects nestedSuccessSound
        nestedRejectSound nestedWindow
  have comptimeSound :=
    PatternInternals.comptimePattern_ordinaryOutcome_sound expression
      relations.expressionOrdinary relations.expressionRejects
        expressionSuccessSound expressionRejectSound
  have qualifiedSound :=
    PatternInternals.qualifiedPattern_ordinaryOutcome_sound nested
      relations.nestedOrdinary relations.nestedRejects nestedSuccessSound
        nestedRejectSound nestedWindow
  have coreSound := PatternInternals.patternCore_ordinaryOutcome_sound nested
    expression relations.parenthesizedOrdinary
      relations.dotConstructorOrdinary relations.comptimeOrdinary
        relations.qualifiedOrdinary relations.parenthesizedRejects
          relations.dotConstructorRejects relations.comptimeRejects
            relations.qualifiedRejects parenthesizedSound.1 dotSound.1
              comptimeSound.1 qualifiedSound.1 parenthesizedSound.2
                dotSound.2 comptimeSound.2 qualifiedSound.2
  have coreWindow := PatternInternals.patternCore_preservesTokenWindow nested
    expression nestedWindow expressionWindow
  exact patternLayer_ordinaryOutcome_sound nested expression
    relations.coreOrdinary relations.coreRejects coreSound.1 coreSound.2
      coreWindow

/-- Re-export the deterministic contract under the executable bridge name. -/
theorem corePatternStep_ordinaryOutcomeSpec
    (relations : DeclarativeGrammar.CorePatternStepRelations)
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      relations.nestedOrdinary relations.nestedRejects)
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      relations.expressionOrdinary relations.expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.CorePatternStepOrdinaryParses relations)
      (DeclarativeGrammar.CorePatternStepRejects relations) :=
  DeclarativeGrammar.corePatternStepDeterministicOutcomeSpec relations
    nestedOutcomes expressionOutcomes

end Solcore.Syntax.Parser
