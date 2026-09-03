import Solcore.Syntax.DeclarativeCoreTermPublicExactnessProperties
import Solcore.Syntax.Parser.CoreTermFuelExactnessProperties
import Solcore.Syntax.Parser.CoreTermPublicOrdinaryOutcomeSoundnessProperties

/-! Unconditional exact executable outcomes for public Core terms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public expression exactness needs no recursive outcome assumptions. -/
theorem expression_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      DeclarativeGrammar.CoreExpressionPublicRejects :=
  DeclarativeGrammar.coreExpressionPublicExactOutcomeSpec

/-- Public expression successes agree on the complete AST and remainder. -/
theorem expression_success_result_unique
    {input leftOutput rightOutput : State} {left right : Expr}
    (leftResult : expression input = .ok left leftOutput)
    (rightResult : expression input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  expression_exactOutcomeSpec.successResultUnique
    (expression_success_ordinary_sound leftResult)
    (expression_success_ordinary_sound rightResult)

/-- Public expression rejections agree on the complete declarative endpoint. -/
theorem expression_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : expression input = .reject leftFailure leftOutput)
    (rightResult : expression input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  expression_exactOutcomeSpec.rejectOutputUnique
    (expression_reject_ordinary_sound leftResult)
    (expression_reject_ordinary_sound rightResult)

/-- Public pattern exactness needs no recursive outcome assumptions. -/
theorem pattern_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.CorePatternOrdinaryParses
      DeclarativeGrammar.CorePatternPublicRejects :=
  DeclarativeGrammar.corePatternPublicExactOutcomeSpec

/-- Public pattern successes agree on the complete AST and remainder. -/
theorem pattern_success_result_unique
    {input leftOutput rightOutput : State} {left right : Pattern}
    (leftResult : pattern input = .ok left leftOutput)
    (rightResult : pattern input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  pattern_exactOutcomeSpec.successResultUnique
    (pattern_success_ordinary_sound leftResult)
    (pattern_success_ordinary_sound rightResult)

/-- Public pattern rejections agree on the complete declarative endpoint. -/
theorem pattern_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : pattern input = .reject leftFailure leftOutput)
    (rightResult : pattern input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  pattern_exactOutcomeSpec.rejectOutputUnique
    (pattern_reject_ordinary_sound leftResult)
    (pattern_reject_ordinary_sound rightResult)

/-- Public statement exactness needs no recursive outcome assumptions. -/
theorem statement_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.CoreStatementOrdinaryParses
      DeclarativeGrammar.CoreStatementPublicRejects :=
  DeclarativeGrammar.coreStatementPublicExactOutcomeSpec

/-- Public statement successes agree on the complete AST and remainder. -/
theorem statement_success_result_unique
    {input leftOutput rightOutput : State} {left right : Statement}
    (leftResult : statement input = .ok left leftOutput)
    (rightResult : statement input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  statement_exactOutcomeSpec.successResultUnique
    (statement_success_ordinary_sound leftResult)
    (statement_success_ordinary_sound rightResult)

/-- Public statement rejections agree on the complete declarative endpoint. -/
theorem statement_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : statement input = .reject leftFailure leftOutput)
    (rightResult : statement input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  statement_exactOutcomeSpec.rejectOutputUnique
    (statement_reject_ordinary_sound leftResult)
    (statement_reject_ordinary_sound rightResult)

end Solcore.Syntax.Parser

