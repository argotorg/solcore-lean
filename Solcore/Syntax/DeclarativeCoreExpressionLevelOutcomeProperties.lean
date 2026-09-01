import Solcore.Syntax.DeclarativeCoreBlockOutcomeProperties
import Solcore.Syntax.DeclarativeCoreBlockIsolationOutcomeProperties
import Solcore.Syntax.DeclarativeCoreExpressionStepOutcomeProperties
import Solcore.Syntax.DeclarativeCoreLambdaParameterPublicOutcomeProperties
import Solcore.Syntax.DeclarativeCoreTypeOutcomeProperties

/-! Reusable declarative levels for recursive Core expression outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One complete ordinary/rejection approximation of recursive expressions. -/
structure CoreExpressionLevel where
  ordinaryParses : Remainder → Syntax.Expr → Remainder → Prop
  rejects : Remainder → Remainder → Prop
  outcomes : DeterministicOutcomeSpec ordinaryParses rejects

namespace CoreExpressionLevel

/-- Fuel zero recognizes no expression success or rejection outcome. -/
def empty : CoreExpressionLevel where
  ordinaryParses := fun _ _ _ => False
  rejects := fun _ _ => False
  outcomes := {
    successOutputUnique := by
      intro input left right afterLeft afterRight leftParsed
      exact False.elim leftParsed
    successRejectDisjoint := by
      intro input rejected rejection
      exact False.elim rejection
  }

/-- Relations supplied to one expression step by the preceding expression
level, fixed public type and lambda-parameter outcomes, and one statement
outcome for isolated required-tail blocks. -/
def stepRelations (previous : CoreExpressionLevel)
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    CoreExpressionStepRelations where
  nestedOrdinary := previous.ordinaryParses
  nestedRejects := previous.rejects
  parameterOrdinary := LambdaParameterOrdinaryParses
    TypeExprOrdinaryParses TypeExprRejects
  parameterRejects := LambdaParameterRejects TypeExprRejects
  typeOrdinary := TypeExprOrdinaryParses
  typeRejects := TypeExprRejects
  blockOrdinary := IsolatedCoreBlockOrdinaryParses
    (CoreBlockOrdinaryParses statementOrdinary .require)
    (CoreBlockRejects statementOrdinary statementRejects .require)
  blockRejects := IsolatedCoreBlockRejects
    (CoreBlockRejects statementOrdinary statementRejects .require)

/-- Add one public recursive expression layer using one supplied statement
outcome for isolated required-tail blocks at this recursion depth. -/
def next (previous : CoreExpressionLevel)
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects) : CoreExpressionLevel where
  ordinaryParses := CoreExpressionStepOrdinaryParses
    (previous.stepRelations statementOrdinary statementRejects)
  rejects := CoreExpressionStepRejects
    (previous.stepRelations statementOrdinary statementRejects)
  outcomes := coreExpressionStepDeterministicOutcomeSpec
    (previous.stepRelations statementOrdinary statementRejects)
      previous.outcomes
      (lambdaParameterDeterministicOutcomeSpec
        typeExprDeterministicOutcomeSpec)
      typeExprDeterministicOutcomeSpec
      (isolatedCoreBlockDeterministicOutcomeSpec
        (coreBlockDeterministicOutcomeSpec .require statementOutcomes))

end CoreExpressionLevel

end Solcore.Syntax.DeclarativeGrammar
