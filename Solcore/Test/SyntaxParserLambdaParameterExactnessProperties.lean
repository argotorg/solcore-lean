import Solcore.Syntax.Parser.CoreLambdaParameterOrdinaryOutcomeSoundnessProperties

/-! External consumers of exact public lambda-parameter outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserLambdaParameterExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @DeclarativeGrammar.lambdaParameterPublicExactOutcomeSpec
example := @DeclarativeGrammar.LambdaParameterOrdinaryParses.result_unique
example := @DeclarativeGrammar.LambdaParameterRejects.output_unique

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    (DeclarativeGrammar.LambdaParameterOrdinaryParses
      DeclarativeGrammar.TypeExprOrdinaryParses DeclarativeGrammar.TypeExprRejects)
    (DeclarativeGrammar.LambdaParameterRejects DeclarativeGrammar.TypeExprRejects) :=
  lambdaParameter_exactOutcomeSpec

example {input leftOutput rightOutput : State} {left right : LambdaParameter}
    (leftResult : lambdaParameter input = .ok left leftOutput)
    (rightResult : lambdaParameter input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  lambdaParameter_success_result_unique leftResult rightResult

example {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : lambdaParameter input = .reject leftFailure leftOutput)
    (rightResult : lambdaParameter input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  lambdaParameter_reject_output_unique leftResult rightResult

end Solcore.Test.SyntaxParserLambdaParameterExactnessProperties
