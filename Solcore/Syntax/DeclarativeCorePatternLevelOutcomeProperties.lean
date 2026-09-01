import Solcore.Syntax.DeclarativeCorePatternStepOutcomeProperties

/-! Reusable declarative levels for recursive Core pattern outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One complete ordinary/rejection approximation of recursive patterns. -/
structure CorePatternLevel where
  ordinaryParses : Remainder → Syntax.Pattern → Remainder → Prop
  rejects : Remainder → Remainder → Prop
  outcomes : DeterministicOutcomeSpec ordinaryParses rejects

namespace CorePatternLevel

/-- Fuel zero recognizes no pattern success or rejection outcome. -/
def empty : CorePatternLevel where
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

/-- Relations supplied to one pattern step by the previous pattern level and
one expression outcome. -/
def stepRelations (previous : CorePatternLevel)
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop) :
    CorePatternStepRelations where
  nestedOrdinary := previous.ordinaryParses
  nestedRejects := previous.rejects
  expressionOrdinary := expressionOrdinary
  expressionRejects := expressionRejects

/-- Add one public recursive pattern layer using one supplied expression
outcome at the preceding recursion depth. -/
def next (previous : CorePatternLevel)
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) : CorePatternLevel where
  ordinaryParses := CorePatternStepOrdinaryParses
    (previous.stepRelations expressionOrdinary expressionRejects)
  rejects := CorePatternStepRejects
    (previous.stepRelations expressionOrdinary expressionRejects)
  outcomes := corePatternStepDeterministicOutcomeSpec
    (previous.stepRelations expressionOrdinary expressionRejects)
      previous.outcomes expressionOutcomes

end CorePatternLevel

end Solcore.Syntax.DeclarativeGrammar
