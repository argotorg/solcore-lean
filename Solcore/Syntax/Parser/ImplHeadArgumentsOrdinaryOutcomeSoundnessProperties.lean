import Solcore.Syntax.DeclarativeImplHeadArgumentsExactnessProperties
import Solcore.Syntax.Parser.ImplHeadArgumentsOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ImplHeadArgumentsOrdinarySuccessSoundnessProperties

/-! Complete broad ordinary outcomes for implementation head arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

/-- Package the executable delimited/refinement success and the only ordinary
rejection stage. -/
theorem implHeadArguments_ordinaryOutcome_sound :
    (∀ {input afterValues output : State}
      {values : DelimitedList TypeExpr}
      {arguments : NonemptyDelimitedList TypeExpr},
      delimited .less .greater false typeExpr .typeExpr .topLevel input =
          .ok values afterValues →
        requireImplArguments values afterValues = .ok arguments output →
          DeclarativeGrammar.ImplHeadArgumentsOrdinaryParses
            input.declarativeRemainder arguments
              output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      delimited .less .greater false typeExpr .typeExpr .topLevel input =
          .reject failure rejected →
        DeclarativeGrammar.ImplHeadArgumentsRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨implHeadArguments_success_ordinaryOutcome_sound,
    implHeadArguments_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad implementation head argument
outcomes. -/
theorem implHeadArguments_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ImplHeadArgumentsOrdinaryParses
      DeclarativeGrammar.ImplHeadArgumentsRejects :=
  DeclarativeGrammar.implHeadArgumentsDeterministicOutcomeSpec

/-- Re-export exact implementation head-argument values and rejection
endpoints. -/
theorem implHeadArguments_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplHeadArgumentsOrdinaryParses
      DeclarativeGrammar.ImplHeadArgumentsRejects :=
  DeclarativeGrammar.implHeadArgumentsExactOutcomeSpec

/-- Two successful executable head-argument pipelines have the same refined
arguments and final declarative remainder. -/
theorem implHeadArguments_success_result_unique
    {input leftAfterValues rightAfterValues leftOutput rightOutput : State}
    {leftValues rightValues : DelimitedList TypeExpr}
    {left right : NonemptyDelimitedList TypeExpr}
    (leftValuesResult : delimited .less .greater false typeExpr .typeExpr
      .topLevel input = .ok leftValues leftAfterValues)
    (leftArgumentsResult : requireImplArguments leftValues leftAfterValues =
      .ok left leftOutput)
    (rightValuesResult : delimited .less .greater false typeExpr .typeExpr
      .topLevel input = .ok rightValues rightAfterValues)
    (rightArgumentsResult :
      requireImplArguments rightValues rightAfterValues =
        .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ImplHeadArgumentsOrdinaryParses.result_unique
    (implHeadArguments_success_ordinaryOutcome_sound leftValuesResult
      leftArgumentsResult)
    (implHeadArguments_success_ordinaryOutcome_sound rightValuesResult
      rightArgumentsResult)

/-- Two rejected executable head-argument parses have the same declarative
endpoint. -/
theorem implHeadArguments_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : delimited .less .greater false typeExpr .typeExpr .topLevel
      input = .reject leftFailure leftOutput)
    (rightResult : delimited .less .greater false typeExpr .typeExpr .topLevel
      input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ImplHeadArgumentsRejects.output_unique
    (implHeadArguments_reject_ordinaryOutcome_sound leftResult)
    (implHeadArguments_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.ImplInternals
