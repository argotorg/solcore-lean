import Solcore.Syntax.DeclarativeCoreExpressionStepOutcomeProperties
import Solcore.Syntax.Parser.CoreExpressionAtomCoreOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreExpressionAtomPublicOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreExpressionLayerOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreExpressionPostfixOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.Expression.Atom
import Solcore.Syntax.Parser.ParameterProperties

/-!
One-call executable ordinary outcomes for a complete Core expression step.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Compose the exact executable bridges through atom dispatch, public atom
recovery, postfix parsing, and the complete operator stack. -/
theorem coreExpressionStep_ordinaryOutcome_sound
    (nested : Parser Expr) (block : Parser Block)
    (relations : DeclarativeGrammar.CoreExpressionStepRelations)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → relations.nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → relations.nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedWindow : Parser.PreservesTokenWindow nested)
    (parameterSuccessSound :
      ∀ {input output : State} {parameter : LambdaParameter},
        lambdaParameter input = .ok parameter output →
          relations.parameterOrdinary input.declarativeRemainder parameter
            output.declarativeRemainder)
    (parameterRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        lambdaParameter input = .reject failure rejected →
          relations.parameterRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → relations.typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → relations.typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (blockSuccessSound : ∀ {input output : State} {body : Block},
      block input = .ok body output → relations.blockOrdinary
        input.declarativeRemainder body output.declarativeRemainder)
    (blockRejectSound : ∀ {input rejected : State} {failure : Failure},
      block input = .reject failure rejected → relations.blockRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (blockWindow : Parser.PreservesTokenWindow block) :
    (∀ {input output : State} {expression : Expr},
      expressionLayer nested block input = .ok expression output →
        DeclarativeGrammar.CoreExpressionStepOrdinaryParses relations
          input.declarativeRemainder expression output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      expressionLayer nested block input = .reject failure rejected →
        DeclarativeGrammar.CoreExpressionStepRejects relations
          input.declarativeRemainder rejected.declarativeRemainder) := by
  have coreSound :=
    ExpressionAtomInternals.expressionAtomCore_ordinaryOutcome_sound nested
      block relations.nestedOrdinary relations.nestedRejects
        relations.parameterOrdinary relations.parameterRejects
          relations.typeOrdinary relations.typeRejects
            relations.blockOrdinary relations.blockRejects nestedSuccessSound
              nestedRejectSound nestedWindow parameterSuccessSound
                parameterRejectSound lambdaParameter_preservesTokenWindow
                  typeSuccessSound typeRejectSound blockSuccessSound
                    blockRejectSound
  have coreWindow :=
    ExpressionAtomInternals.expressionAtomCore_preservesTokenWindow nested
      block nestedWindow blockWindow
  have atomSound := expressionAtom_ordinaryOutcome_sound nested block
    relations.atomCoreOrdinary relations.atomCoreRejects coreSound.1
      coreSound.2 coreWindow
  have postfixSound := expressionPostfix_ordinaryOutcome_sound nested block
    relations.atomOrdinary relations.nestedOrdinary relations.atomRejects
      relations.nestedRejects atomSound.1 atomSound.2 nestedSuccessSound
        nestedRejectSound nestedWindow
  exact expressionLayer_ordinaryOutcome_sound nested block
    relations.nestedOrdinary relations.postfixOrdinary
      relations.nestedRejects relations.postfixRejects nestedSuccessSound
        nestedRejectSound postfixSound.1 postfixSound.2

/-- Re-export the deterministic contract under the executable bridge name. -/
theorem coreExpressionStep_ordinaryOutcomeSpec
    (relations : DeclarativeGrammar.CoreExpressionStepRelations)
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      relations.nestedOrdinary relations.nestedRejects)
    (parameterOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      relations.parameterOrdinary relations.parameterRejects)
    (typeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      relations.typeOrdinary relations.typeRejects)
    (blockOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      relations.blockOrdinary relations.blockRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.CoreExpressionStepOrdinaryParses relations)
      (DeclarativeGrammar.CoreExpressionStepRejects relations) :=
  DeclarativeGrammar.coreExpressionStepDeterministicOutcomeSpec relations
    nestedOutcomes parameterOutcomes typeOutcomes blockOutcomes

end Solcore.Syntax.Parser
