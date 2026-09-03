import Solcore.Syntax.Parser.YulExpressionPublicFuelSoundnessProperties

/-! External compile consumers of exact fixed-fuel and public Yul expressions. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulExpressionExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @DeclarativeGrammar.yulNameExactOutcomeSpec
example := @DeclarativeGrammar.YulNameOrdinaryParses.result_unique
example := @DeclarativeGrammar.YulNameRejects.output_unique
example := @DeclarativeGrammar.YulLiteralParses.result_unique
example := @DeclarativeGrammar.OptionalYulCallArgumentsOrdinaryParses.result_unique
example := @DeclarativeGrammar.YulNamedExpressionOrdinaryParses.result_unique
example := @DeclarativeGrammar.YulExpressionCoreOrdinaryParses.result_unique
example := @DeclarativeGrammar.YulExpressionRecoveryScanParses.result_unique
example := @DeclarativeGrammar.YulExpressionLayerOrdinaryParses.result_unique
example := @DeclarativeGrammar.yulExpressionLayerExactOutcomeSpec
example := @DeclarativeGrammar.YulExpressionOrdinaryParsesWithFuel.value_unique
example := @DeclarativeGrammar.YulExpressionOrdinaryParsesWithFuel.result_unique
example := @DeclarativeGrammar.YulExpressionRejectsWithFuel.output_unique
example := @DeclarativeGrammar.YulExpressionOrdinaryParses.value_unique
example := @DeclarativeGrammar.YulExpressionOrdinaryParses.result_unique
example := @DeclarativeGrammar.YulExpressionPublicRejects.output_unique

example (fuel : Nat) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.YulExpressionOrdinaryParsesWithFuel fuel)
      (DeclarativeGrammar.YulExpressionRejectsWithFuel fuel) :=
  YulExpressionInternals.withFuel_exactOutcomeSpec fuel

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.YulExpressionOrdinaryParses
    DeclarativeGrammar.YulExpressionPublicRejects :=
  yulExpression_publicExactOutcomeSpec

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.YulExpressionOrdinaryParses
    DeclarativeGrammar.YulExpressionRejects :=
  yulExpression_exactOutcomeSpec

example (fuel : Nat) {input leftOutput rightOutput : State}
    {left right : YulExpr}
    (leftResult : YulExpressionInternals.withFuel fuel input =
      .ok left leftOutput)
    (rightResult : YulExpressionInternals.withFuel fuel input =
      .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  YulExpressionInternals.withFuel_success_result_unique fuel leftResult rightResult

example (fuel : Nat) {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : YulExpressionInternals.withFuel fuel input =
      .reject leftFailure leftOutput)
    (rightResult : YulExpressionInternals.withFuel fuel input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  YulExpressionInternals.withFuel_reject_output_unique fuel leftResult rightResult

example {input leftOutput rightOutput : State} {left right : YulExpr}
    (leftResult : yulExpression input = .ok left leftOutput)
    (rightResult : yulExpression input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  yulExpression_success_result_unique leftResult rightResult

example {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : yulExpression input = .reject leftFailure leftOutput)
    (rightResult : yulExpression input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  yulExpression_reject_output_unique leftResult rightResult

end Solcore.Test.SyntaxParserYulExpressionExactnessProperties
