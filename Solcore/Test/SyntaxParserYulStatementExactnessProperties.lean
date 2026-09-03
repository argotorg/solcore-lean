import Solcore.Syntax.Parser.YulBodyPublicSoundnessProperties

/-! External consumers of exact recursive Yul statement and body outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulStatementExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @DeclarativeGrammar.YulBlockItemsParses.result_unique
example := @DeclarativeGrammar.YulBlockItemsRejects.output_unique
example := @DeclarativeGrammar.yulBlockExactOutcomeSpec
example := @DeclarativeGrammar.YulNamesOrdinaryParses.result_unique
example := @DeclarativeGrammar.YulExpressionStatementOrdinaryParses.value_unique
example := @DeclarativeGrammar.yulExpressionStatementExactOutcomeSpec
example := @DeclarativeGrammar.YulReturnBuiltinOrdinaryParses.value_unique
example := @DeclarativeGrammar.YulControlTokenOrdinaryParses.value_unique
example := @DeclarativeGrammar.YulLetStatementOrdinaryParses.value_unique
example := @DeclarativeGrammar.YulAssignmentOrdinaryParses.value_unique
example := @DeclarativeGrammar.YulIfStatementOrdinaryParses.value_unique
example := @DeclarativeGrammar.YulForStatementOrdinaryParses.value_unique
example := @DeclarativeGrammar.YulFunctionStatementOrdinaryParses.value_unique
example := @DeclarativeGrammar.YulSwitchStatementOrdinaryParses.value_unique
example := @DeclarativeGrammar.OptionalYulDefaultParses.result_unique
example := @DeclarativeGrammar.YulNameStatementOrdinaryParses.value_unique
example := @DeclarativeGrammar.yulStatementCoreExactOutcomeSpec
example := @DeclarativeGrammar.yulStatementTerminatedExactOutcomeSpec
example := @DeclarativeGrammar.YulStatementRecoveryScanParses.value_unique
example := @DeclarativeGrammar.yulStatementLayerExactOutcomeSpec
example := @DeclarativeGrammar.YulBodyOrdinaryParses.result_unique
example := @DeclarativeGrammar.YulBodyRejects.output_unique

example (fuel : Nat) : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
    (DeclarativeGrammar.YulStatementRejectsWithFuel fuel) :=
  yulStatementWithFuel_exactOutcomeSpec fuel

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.YulStatementOrdinaryParses
    DeclarativeGrammar.YulStatementPublicRejects :=
  yulStatement_publicExactOutcomeSpec

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.YulStatementOrdinaryParses
    DeclarativeGrammar.YulStatementRejects :=
  yulStatement_exactOutcomeSpec

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.YulBodyOutcomeParses DeclarativeGrammar.YulBodyRejects :=
  yulBody_exactOutcomeSpec

example (fuel : Nat) {input leftOutput rightOutput : State}
    {left right : YulStmt}
    (leftResult : yulStatementWithFuel fuel input = .ok left leftOutput)
    (rightResult : yulStatementWithFuel fuel input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  yulStatementWithFuel_success_result_unique fuel leftResult rightResult

example (fuel : Nat) {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : yulStatementWithFuel fuel input = .reject leftFailure leftOutput)
    (rightResult : yulStatementWithFuel fuel input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  yulStatementWithFuel_reject_output_unique fuel leftResult rightResult

example {input leftOutput rightOutput : State} {left right : YulStmt}
    (leftResult : yulStatement input = .ok left leftOutput)
    (rightResult : yulStatement input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  yulStatement_success_result_unique leftResult rightResult

example {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : yulStatement input = .reject leftFailure leftOutput)
    (rightResult : yulStatement input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  yulStatement_reject_output_unique leftResult rightResult

example {input leftOutput rightOutput : State} {left right : YulParsedBlock}
    (leftResult : yulBody input = .ok left leftOutput)
    (rightResult : yulBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  yulBody_success_result_unique leftResult rightResult

example {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : yulBody input = .reject leftFailure leftOutput)
    (rightResult : yulBody input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  yulBody_reject_output_unique leftResult rightResult

end Solcore.Test.SyntaxParserYulStatementExactnessProperties
