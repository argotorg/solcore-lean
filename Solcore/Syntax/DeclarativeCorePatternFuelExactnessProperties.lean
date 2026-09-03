import Solcore.Syntax.DeclarativeCorePatternStepExactnessProperties
import Solcore.Syntax.DeclarativeCoreTermFuelEquationProperties

/-! Base and successor lifts for exact mutually recursive Core pattern fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Fuel zero admits neither an ordinary pattern success nor rejection. -/
theorem corePatternExactOutcomeSpecWithFuel_zero :
    ExactDeterministicOutcomeSpec
      (CorePatternOrdinaryParsesWithFuel 0)
      (CorePatternRejectsWithFuel 0) where
  toDeterministicOutcomeSpec := corePatternOutcomeSpecWithFuel 0
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed
    exact False.elim (CorePatternOrdinaryParsesWithFuel.zero leftParsed)
  rejectOutputUnique := by
    intro input left right leftRejected
    exact False.elim (CorePatternRejectsWithFuel.zero leftRejected)

/-- Pattern and expression exactness at the same preceding fuel supplies
pattern exactness at the successor fuel; no successor expression is assumed. -/
theorem corePatternExactOutcomeSpecWithFuel_succ
    (fuel : Nat)
    (patternOutcomes : ExactDeterministicOutcomeSpec
      (CorePatternOrdinaryParsesWithFuel fuel)
      (CorePatternRejectsWithFuel fuel))
    (expressionOutcomes : ExactDeterministicOutcomeSpec
      (CoreExpressionOrdinaryParsesWithFuel fuel)
      (CoreExpressionRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec
      (CorePatternOrdinaryParsesWithFuel (fuel + 1))
      (CorePatternRejectsWithFuel (fuel + 1)) := by
  change ExactDeterministicOutcomeSpec
    (CorePatternStepOrdinaryParses (corePatternStepRelationsWithFuel fuel))
    (CorePatternStepRejects (corePatternStepRelationsWithFuel fuel))
  exact corePatternStepExactOutcomeSpec
    (corePatternStepRelationsWithFuel fuel) patternOutcomes expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
