import Solcore.Syntax.DeclarativeSyntaxExactnessProperties
import Solcore.Syntax.Parser.TopItemOrdinaryOutcomeSoundnessProperties

/-! Unconditional executable exactness for plain and derive-aware top items. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Exact declaration outcomes close this public top-item boundary. -/
theorem plainTopItem_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.PlainTopItemOrdinaryParses DeclarativeGrammar.PlainTopItemRejects :=
  DeclarativeGrammar.plainTopItemExactOutcomeSpec

/-- Successful top items agree on their complete located AST and remainder. -/
theorem plainTopItem_success_result_unique
    {input leftOutput rightOutput : State} {left right : TopItem}
    (leftResult : plainTopItem input = .ok left leftOutput)
    (rightResult : plainTopItem input = .ok right rightOutput) :
    left = right ∧ leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  plainTopItem_exactOutcomeSpec.successResultUnique
    (plainTopItem_success_ordinaryOutcome_sound leftResult)
    (plainTopItem_success_ordinaryOutcome_sound rightResult)

/-- Rejected top items agree on their complete declarative endpoint. -/
theorem plainTopItem_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : plainTopItem input = .reject leftFailure leftOutput)
    (rightResult : plainTopItem input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  plainTopItem_exactOutcomeSpec.rejectOutputUnique
    (plainTopItem_reject_ordinaryOutcome_sound leftResult)
    (plainTopItem_reject_ordinaryOutcome_sound rightResult)

/-- Exact declaration outcomes close this public top-item boundary. -/
theorem topItem_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects :=
  DeclarativeGrammar.topItemExactOutcomeSpec

/-- Successful top items agree on their complete located AST and remainder. -/
theorem topItem_success_result_unique
    {input leftOutput rightOutput : State} {left right : TopItem}
    (leftResult : topItem input = .ok left leftOutput)
    (rightResult : topItem input = .ok right rightOutput) :
    left = right ∧ leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  topItem_exactOutcomeSpec.successResultUnique
    (topItem_success_ordinaryOutcome_sound leftResult)
    (topItem_success_ordinaryOutcome_sound rightResult)

/-- Rejected top items agree on their complete declarative endpoint. -/
theorem topItem_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : topItem input = .reject leftFailure leftOutput)
    (rightResult : topItem input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  topItem_exactOutcomeSpec.rejectOutputUnique
    (topItem_reject_ordinaryOutcome_sound leftResult)
    (topItem_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.FileInternals
