import Solcore.Syntax.Parser.CoreTermPublicExactnessProperties
import Solcore.Syntax.Parser.CoreBlockPublicIsolationOrdinaryOutcomeSoundnessProperties

/-! Exact public raw and isolated blocks under both tail-expression policies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public raw block exactness no longer assumes statement exactness. -/
theorem block_exactOutcomeSpec (policy : TailExpressionPolicy) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.CoreBlockPublicOrdinaryParses policy.declarative)
      (DeclarativeGrammar.CoreBlockPublicRejects policy.declarative) :=
  block_exactOutcomeSpec_of_statementFuel
    DeclarativeGrammar.coreStatementExactOutcomeSpecWithFuel policy

/-- Public raw block successes agree on their full AST and remainder. -/
theorem block_success_result_unique (policy : TailExpressionPolicy)
    {input leftOutput rightOutput : State} {left right : Block}
    (leftResult : block policy input = .ok left leftOutput)
    (rightResult : block policy input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (block_exactOutcomeSpec policy).successResultUnique
    (block_success_ordinary_sound policy leftResult)
    (block_success_ordinary_sound policy rightResult)

/-- Public raw block rejections agree on their complete endpoint. -/
theorem block_reject_output_unique (policy : TailExpressionPolicy)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : block policy input = .reject leftFailure leftOutput)
    (rightResult : block policy input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (block_exactOutcomeSpec policy).rejectOutputUnique
    (block_reject_ordinary_sound policy leftResult)
    (block_reject_ordinary_sound policy rightResult)

/-- Public isolated block exactness no longer assumes statement exactness. -/
theorem isolatedCoreBlockPublic_exactOutcomeSpec (policy : TailExpressionPolicy) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses policy.declarative)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects policy.declarative) :=
  isolatedCoreBlockPublic_exactOutcomeSpec_of_statementFuel
    DeclarativeGrammar.coreStatementExactOutcomeSpecWithFuel policy

/-- Public isolated block successes agree on their full AST and remainder. -/
theorem isolatedCoreBlockPublic_success_result_unique (policy : TailExpressionPolicy)
    {input leftOutput rightOutput : State} {left right : Block}
    (leftResult : isolateBlock (block policy) input = .ok left leftOutput)
    (rightResult : isolateBlock (block policy) input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (isolatedCoreBlockPublic_exactOutcomeSpec policy).successResultUnique
    (isolatedCoreBlockPublic_success_ordinary_sound policy leftResult)
    (isolatedCoreBlockPublic_success_ordinary_sound policy rightResult)

/-- Public isolated block rejections agree on their complete endpoint. -/
theorem isolatedCoreBlockPublic_reject_output_unique (policy : TailExpressionPolicy)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : isolateBlock (block policy) input = .reject leftFailure leftOutput)
    (rightResult : isolateBlock (block policy) input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (isolatedCoreBlockPublic_exactOutcomeSpec policy).rejectOutputUnique
    (isolatedCoreBlockPublic_reject_ordinary_sound policy leftResult)
    (isolatedCoreBlockPublic_reject_ordinary_sound policy rightResult)

end Solcore.Syntax.Parser

