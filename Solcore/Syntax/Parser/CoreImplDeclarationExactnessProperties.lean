import Solcore.Syntax.DeclarativeCoreDeclarationExactnessProperties
import Solcore.Syntax.Parser.Impl

/-! Unconditional executable exactness for implementation declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ImplInternals

/-- Implementation-method exactness requires no recursive body premise. -/
theorem implMethod_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplMethodOrdinaryParses
      DeclarativeGrammar.ImplMethodRejects :=
  DeclarativeGrammar.implMethodExactOutcomeSpec

/-- Method successes agree on their complete AST and remainder. -/
theorem implMethod_success_result_unique
    {input leftOutput rightOutput : State} {left right : ImplMethod}
    (leftResult : implMethod input = .ok left leftOutput)
    (rightResult : implMethod input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implMethod_exactOutcomeSpec.successResultUnique
    (implMethod_success_ordinaryOutcome_sound leftResult)
    (implMethod_success_ordinaryOutcome_sound rightResult)

/-- Method rejections agree on their complete declarative endpoint. -/
theorem implMethod_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : implMethod input = .reject leftFailure leftOutput)
    (rightResult : implMethod input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implMethod_exactOutcomeSpec.rejectOutputUnique
    (implMethod_reject_ordinaryOutcome_sound leftResult)
    (implMethod_reject_ordinaryOutcome_sound rightResult)

/-- Implementation-body exactness requires no recursive method premise. -/
theorem implBody_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ImplBodyRejects :=
  DeclarativeGrammar.implBodyExactOutcomeSpec

/-- Body successes agree on their parser value, including spans and method order. -/
theorem implBody_success_result_unique
    {input leftOutput rightOutput : State} {left right : ImplBody}
    (leftResult : implBody input = .ok left leftOutput)
    (rightResult : implBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implBody_success_result_unique_of_method
    DeclarativeGrammar.implMethodExactOutcomeSpec leftResult rightResult

/-- Implementation-body rejections agree on their declarative endpoint. -/
theorem implBody_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : implBody input = .reject leftFailure leftOutput)
    (rightResult : implBody input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implBody_exactOutcomeSpec.rejectOutputUnique
    (implBody_reject_ordinaryOutcome_sound leftResult)
    (implBody_reject_ordinaryOutcome_sound rightResult)

end ImplInternals

/-- Implementation-declaration exactness requires no recursive body premise. -/
theorem implDecl_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplDeclOrdinaryParses
      DeclarativeGrammar.ImplDeclRejects :=
  DeclarativeGrammar.implDeclExactOutcomeSpec

/-- Complete implementation successes agree on their AST and remainder. -/
theorem implDecl_success_result_unique
    {input leftOutput rightOutput : State} {left right : ImplDecl}
    (leftResult : implDecl input = .ok left leftOutput)
    (rightResult : implDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implDecl_exactOutcomeSpec.successResultUnique
    (implDecl_success_ordinaryOutcome_sound leftResult)
    (implDecl_success_ordinaryOutcome_sound rightResult)

/-- Complete implementation rejections agree on their declarative endpoint. -/
theorem implDecl_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : implDecl input = .reject leftFailure leftOutput)
    (rightResult : implDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implDecl_exactOutcomeSpec.rejectOutputUnique
    (implDecl_reject_ordinaryOutcome_sound leftResult)
    (implDecl_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
