import Solcore.Syntax.DeclarativeYulExpressionExactnessProperties
import Solcore.Syntax.Parser.YulExpressionFuelCleanSoundnessProperties

/-! Public executable bridges for the concrete recursive Yul-expression grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every public parser success follows the concrete ordinary recursive
grammar selected from the input token remainder. -/
theorem yulExpression_success_ordinary_sound
    {input output : State} {expression : YulExpr}
    (result : yulExpression input = .ok expression output) :
    DeclarativeGrammar.YulExpressionOrdinaryParses
      input.declarativeRemainder expression output.declarativeRemainder := by
  unfold yulExpression at result
  simpa [DeclarativeGrammar.YulExpressionOrdinaryParses,
    DeclarativeGrammar.yulExpressionPublicFuel, State.declarativeRemainder,
    State.remainingCount] using
      YulExpressionInternals.withFuel_success_ordinary_fuel_sound
        (input.remainingCount + 1) result

/-- Every public ordinary rejection follows the concrete public fuel-indexed
rejection relation. -/
theorem yulExpression_reject_public_sound
    {input rejected : State} {failure : Failure}
    (result : yulExpression input = .reject failure rejected) :
    DeclarativeGrammar.YulExpressionPublicRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold yulExpression at result
  simpa [DeclarativeGrammar.YulExpressionPublicRejects,
    DeclarativeGrammar.yulExpressionPublicFuel, State.declarativeRemainder,
    State.remainingCount] using
      YulExpressionInternals.withFuel_reject_fuel_sound
        (input.remainingCount + 1) result

/-- Every diagnostic-free public parser success follows the concrete clean
recursive grammar. -/
theorem yulExpression_success_clean_sound
    {input output : State} {expression : YulExpr}
    (diagnosticFree : output.diagnosticsRev = [])
    (result : yulExpression input = .ok expression output) :
    DeclarativeGrammar.YulExpressionParses input.declarativeRemainder
      expression output.declarativeRemainder := by
  unfold yulExpression at result
  simpa [DeclarativeGrammar.YulExpressionParses,
    DeclarativeGrammar.yulExpressionPublicFuel, State.declarativeRemainder,
    State.remainingCount] using
      YulExpressionInternals.withFuel_success_clean_fuel_sound
        (input.remainingCount + 1) diagnosticFree result

/-- Public diagnostic reflection used by the concrete declarative bridge. -/
theorem yulExpression_public_reflectsDiagnosticFreeForDeclarativeSoundness :
    Parser.ReflectsDiagnosticFreeOnSuccess yulExpression := by
  intro input expression output result diagnosticFree
  unfold yulExpression at result
  exact
    YulExpressionInternals.withFuel_reflectsDiagnosticFreeForDeclarativeSoundness
      (input.remainingCount + 1) input expression output result diagnosticFree

/-- Deterministic ordinary outcomes of the public grammar, stated with its
fuel-indexed public rejection relation. -/
theorem yulExpression_publicOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.YulExpressionOrdinaryParses
      DeclarativeGrammar.YulExpressionPublicRejects :=
  DeclarativeGrammar.yulExpressionPublicOutcomeSpec

/-- The same public outcome contract against the concrete boundary rejection
relation consumed by recursive transactional parsers. -/
theorem yulExpression_publicConcreteOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.YulExpressionOrdinaryParses
      DeclarativeGrammar.YulExpressionRejects :=
  DeclarativeGrammar.yulExpressionPublicDeterministicOutcomeSpec

namespace YulExpressionInternals

/-- Re-export exact outcomes at each fixed recursive expression fuel. -/
theorem withFuel_exactOutcomeSpec (fuel : Nat) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.YulExpressionOrdinaryParsesWithFuel fuel)
      (DeclarativeGrammar.YulExpressionRejectsWithFuel fuel) :=
  DeclarativeGrammar.yulExpressionExactOutcomeSpecWithFuel fuel

/-- Fixed-fuel executable successes agree on their complete declarative result. -/
theorem withFuel_success_result_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {left right : YulExpr}
    (leftResult : withFuel fuel input = .ok left leftOutput)
    (rightResult : withFuel fuel input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.YulExpressionOrdinaryParsesWithFuel.result_unique
    (withFuel_success_ordinary_fuel_sound fuel leftResult)
    (withFuel_success_ordinary_fuel_sound fuel rightResult)

/-- Fixed-fuel executable rejections agree on their exact declarative endpoint. -/
theorem withFuel_reject_output_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : withFuel fuel input = .reject leftFailure leftOutput)
    (rightResult : withFuel fuel input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.YulExpressionRejectsWithFuel.output_unique
    (withFuel_reject_fuel_sound fuel leftResult)
    (withFuel_reject_fuel_sound fuel rightResult)

end YulExpressionInternals

/-- Re-export exact public ordinary outcomes with input-selected fuel. -/
theorem yulExpression_publicExactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.YulExpressionOrdinaryParses
      DeclarativeGrammar.YulExpressionPublicRejects :=
  DeclarativeGrammar.yulExpressionPublicExactOutcomeSpec

/-- Exact public expression outcomes against the concrete boundary rejection. -/
theorem yulExpression_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.YulExpressionOrdinaryParses
      DeclarativeGrammar.YulExpressionRejects :=
  DeclarativeGrammar.yulExpressionExactOutcomeSpec

/-- Public executable expression successes agree on their AST and remainder. -/
theorem yulExpression_success_result_unique
    {input leftOutput rightOutput : State} {left right : YulExpr}
    (leftResult : yulExpression input = .ok left leftOutput)
    (rightResult : yulExpression input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.YulExpressionOrdinaryParses.result_unique
    (yulExpression_success_ordinary_sound leftResult)
    (yulExpression_success_ordinary_sound rightResult)

/-- Public executable expression rejections agree on their complete endpoint. -/
theorem yulExpression_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : yulExpression input = .reject leftFailure leftOutput)
    (rightResult : yulExpression input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.YulExpressionPublicRejects.output_unique
    (yulExpression_reject_public_sound leftResult)
    (yulExpression_reject_public_sound rightResult)

end Solcore.Syntax.Parser
