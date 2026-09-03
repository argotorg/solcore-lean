import Solcore.Syntax.DeclarativeCoreExpressionFuelExactnessProperties
import Solcore.Syntax.DeclarativeCorePatternFuelExactnessProperties
import Solcore.Syntax.DeclarativeCoreStatementFuelExactnessProperties

/-! Unconditional exactness of mutually recursive Core terms at every fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- All three mutually recursive grammars are exact at each fixed fuel.
Successor expressions use preceding expressions/statements, patterns use
preceding patterns/expressions, and statements use all three preceding levels. -/
theorem coreTermExactOutcomeSpecsWithFuel (fuel : Nat) :
    ExactDeterministicOutcomeSpec (CoreExpressionOrdinaryParsesWithFuel fuel)
      (CoreExpressionRejectsWithFuel fuel) ∧
    ExactDeterministicOutcomeSpec (CorePatternOrdinaryParsesWithFuel fuel)
      (CorePatternRejectsWithFuel fuel) ∧
    ExactDeterministicOutcomeSpec (CoreStatementOrdinaryParsesWithFuel fuel)
      (CoreStatementRejectsWithFuel fuel) := by
  induction fuel with
  | zero =>
      exact ⟨coreExpressionExactOutcomeSpecWithFuel_zero,
        corePatternExactOutcomeSpecWithFuel_zero,
        coreStatementExactOutcomeSpecWithFuel_zero⟩
  | succ fuel ih =>
      exact ⟨coreExpressionExactOutcomeSpecWithFuel_succ fuel ih.1 ih.2.2,
        corePatternExactOutcomeSpecWithFuel_succ fuel ih.2.1 ih.1,
        coreStatementExactOutcomeSpecWithFuel_succ fuel ih.2.2 ih.1 ih.2.1⟩

/-- Fixed-fuel Core expressions have exact ASTs and complete outcome endpoints. -/
theorem coreExpressionExactOutcomeSpecWithFuel (fuel : Nat) :
    ExactDeterministicOutcomeSpec (CoreExpressionOrdinaryParsesWithFuel fuel)
      (CoreExpressionRejectsWithFuel fuel) :=
  (coreTermExactOutcomeSpecsWithFuel fuel).1

/-- Fixed-fuel Core patterns have exact ASTs and complete outcome endpoints. -/
theorem corePatternExactOutcomeSpecWithFuel (fuel : Nat) :
    ExactDeterministicOutcomeSpec (CorePatternOrdinaryParsesWithFuel fuel)
      (CorePatternRejectsWithFuel fuel) :=
  (coreTermExactOutcomeSpecsWithFuel fuel).2.1

/-- Fixed-fuel Core statements have exact ASTs and complete outcome endpoints. -/
theorem coreStatementExactOutcomeSpecWithFuel (fuel : Nat) :
    ExactDeterministicOutcomeSpec (CoreStatementOrdinaryParsesWithFuel fuel)
      (CoreStatementRejectsWithFuel fuel) :=
  (coreTermExactOutcomeSpecsWithFuel fuel).2.2

end Solcore.Syntax.DeclarativeGrammar
