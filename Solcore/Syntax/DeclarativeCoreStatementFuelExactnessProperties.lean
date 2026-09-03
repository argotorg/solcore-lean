import Solcore.Syntax.DeclarativeCoreStatementLayerExactnessProperties
import Solcore.Syntax.DeclarativeCoreTermFuelEquationProperties

/-! Base and successor lifts for exact mutually recursive Core statement fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Fuel zero admits neither an ordinary statement success nor rejection. -/
theorem coreStatementExactOutcomeSpecWithFuel_zero :
    ExactDeterministicOutcomeSpec
      (CoreStatementOrdinaryParsesWithFuel 0)
      (CoreStatementRejectsWithFuel 0) where
  toDeterministicOutcomeSpec := coreStatementOutcomeSpecWithFuel 0
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed
    exact False.elim (CoreStatementOrdinaryParsesWithFuel.zero leftParsed)
  rejectOutputUnique := by
    intro input left right leftRejected
    exact False.elim (CoreStatementRejectsWithFuel.zero leftRejected)

/-- Statement, expression, and pattern exactness at the same preceding fuel
supplies exact successor statements, with no other recursive prerequisites. -/
theorem coreStatementExactOutcomeSpecWithFuel_succ
    (fuel : Nat)
    (statementOutcomes : ExactDeterministicOutcomeSpec
      (CoreStatementOrdinaryParsesWithFuel fuel)
      (CoreStatementRejectsWithFuel fuel))
    (expressionOutcomes : ExactDeterministicOutcomeSpec
      (CoreExpressionOrdinaryParsesWithFuel fuel)
      (CoreExpressionRejectsWithFuel fuel))
    (patternOutcomes : ExactDeterministicOutcomeSpec
      (CorePatternOrdinaryParsesWithFuel fuel)
      (CorePatternRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec
      (CoreStatementOrdinaryParsesWithFuel (fuel + 1))
      (CoreStatementRejectsWithFuel (fuel + 1)) := by
  change ExactDeterministicOutcomeSpec
    (StatementLayerOrdinaryParses
      (CoreStatementOrdinaryParsesWithFuel fuel)
      (CoreStatementRejectsWithFuel fuel)
      (CoreExpressionOrdinaryParsesWithFuel fuel)
      (CoreExpressionRejectsWithFuel fuel)
      (CorePatternOrdinaryParsesWithFuel fuel)
      (CorePatternRejectsWithFuel fuel))
    (StatementLayerRejects
      (CoreStatementOrdinaryParsesWithFuel fuel)
      (CoreStatementRejectsWithFuel fuel)
      (CoreExpressionOrdinaryParsesWithFuel fuel)
      (CoreExpressionRejectsWithFuel fuel)
      (CorePatternOrdinaryParsesWithFuel fuel)
      (CorePatternRejectsWithFuel fuel))
  exact statementLayerExactOutcomeSpec statementOutcomes expressionOutcomes
    patternOutcomes

end Solcore.Syntax.DeclarativeGrammar
