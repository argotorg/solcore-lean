import Solcore.Syntax.DeclarativeCoreTermExactnessProperties
import Solcore.Syntax.Parser.CoreTermFuelOrdinaryOutcomeSoundnessProperties

/-! Exact executable Core outcomes at an explicitly shared recursion fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- The declarative expression outcome is exact at every fixed fuel. -/
theorem coreExpressionWithFuel_exactOutcomeSpec (fuel : Nat) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.CoreExpressionOrdinaryParsesWithFuel fuel)
      (DeclarativeGrammar.CoreExpressionRejectsWithFuel fuel) :=
  DeclarativeGrammar.coreExpressionExactOutcomeSpecWithFuel fuel

/-- Fixed-fuel expression successes agree on the complete AST and remainder. -/
theorem coreExpressionWithFuel_success_result_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {left right : Expr}
    (leftResult : coreExpressionWithFuel fuel input = .ok left leftOutput)
    (rightResult : coreExpressionWithFuel fuel input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (coreExpressionWithFuel_exactOutcomeSpec fuel).successResultUnique
    (coreExpressionWithFuel_success_ordinary_sound fuel leftResult)
    (coreExpressionWithFuel_success_ordinary_sound fuel rightResult)

/-- Fixed-fuel expression rejections agree on the complete remainder. -/
theorem coreExpressionWithFuel_reject_output_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : coreExpressionWithFuel fuel input = .reject leftFailure leftOutput)
    (rightResult : coreExpressionWithFuel fuel input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (coreExpressionWithFuel_exactOutcomeSpec fuel).rejectOutputUnique
    (coreExpressionWithFuel_reject_ordinary_sound fuel leftResult)
    (coreExpressionWithFuel_reject_ordinary_sound fuel rightResult)

/-- The declarative pattern outcome is exact at every fixed fuel. -/
theorem corePatternWithFuel_exactOutcomeSpec (fuel : Nat) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.CorePatternOrdinaryParsesWithFuel fuel)
      (DeclarativeGrammar.CorePatternRejectsWithFuel fuel) :=
  DeclarativeGrammar.corePatternExactOutcomeSpecWithFuel fuel

/-- Fixed-fuel pattern successes agree on the complete AST and remainder. -/
theorem corePatternWithFuel_success_result_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {left right : Pattern}
    (leftResult : corePatternWithFuel fuel input = .ok left leftOutput)
    (rightResult : corePatternWithFuel fuel input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (corePatternWithFuel_exactOutcomeSpec fuel).successResultUnique
    (corePatternWithFuel_success_ordinary_sound fuel leftResult)
    (corePatternWithFuel_success_ordinary_sound fuel rightResult)

/-- Fixed-fuel pattern rejections agree on the complete remainder. -/
theorem corePatternWithFuel_reject_output_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : corePatternWithFuel fuel input = .reject leftFailure leftOutput)
    (rightResult : corePatternWithFuel fuel input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (corePatternWithFuel_exactOutcomeSpec fuel).rejectOutputUnique
    (corePatternWithFuel_reject_ordinary_sound fuel leftResult)
    (corePatternWithFuel_reject_ordinary_sound fuel rightResult)

/-- The declarative statement outcome is exact at every fixed fuel. -/
theorem coreStatementWithFuel_exactOutcomeSpec (fuel : Nat) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
      (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel) :=
  DeclarativeGrammar.coreStatementExactOutcomeSpecWithFuel fuel

/-- Fixed-fuel statement successes agree on the complete AST and remainder. -/
theorem coreStatementWithFuel_success_result_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {left right : Statement}
    (leftResult : coreStatementWithFuel fuel input = .ok left leftOutput)
    (rightResult : coreStatementWithFuel fuel input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (coreStatementWithFuel_exactOutcomeSpec fuel).successResultUnique
    (coreStatementWithFuel_success_ordinary_sound fuel leftResult)
    (coreStatementWithFuel_success_ordinary_sound fuel rightResult)

/-- Fixed-fuel statement rejections agree on the complete remainder. -/
theorem coreStatementWithFuel_reject_output_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : coreStatementWithFuel fuel input = .reject leftFailure leftOutput)
    (rightResult : coreStatementWithFuel fuel input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (coreStatementWithFuel_exactOutcomeSpec fuel).rejectOutputUnique
    (coreStatementWithFuel_reject_ordinary_sound fuel leftResult)
    (coreStatementWithFuel_reject_ordinary_sound fuel rightResult)

end Solcore.Syntax.Parser.TermInternals
