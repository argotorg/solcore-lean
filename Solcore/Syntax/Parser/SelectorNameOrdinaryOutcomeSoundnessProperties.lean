import Solcore.Syntax.DeclarativeSelectorNameExactnessProperties
import Solcore.Syntax.DeclarativeSelectorNameOutcomeProperties
import Solcore.Syntax.Parser.SelectorNameOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.SelectorNameOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for selector names. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package selector-name success and exact prioritized rejection. -/
theorem selectorName_ordinaryOutcome_sound (context : ParseContext) :
    (∀ {input output : State} {selector : SelectorName},
      selectorName context input = .ok selector output →
        DeclarativeGrammar.SelectorNameOrdinaryParses
          input.declarativeRemainder selector output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      selectorName context input = .reject failure rejected →
        DeclarativeGrammar.SelectorNameRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨selectorName_success_ordinaryOutcome_sound context,
    selectorName_reject_ordinaryOutcome_sound context⟩

/-- Re-export deterministic and exclusive selector-name outcomes. -/
theorem selectorName_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.SelectorNameOrdinaryParses
      DeclarativeGrammar.SelectorNameRejects :=
  DeclarativeGrammar.selectorNameDeterministicOutcomeSpec


/-- Exact values and endpoints for the independent selectorName grammar. -/
theorem selectorName_exactOutcomeSpec  :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.SelectorNameOrdinaryParses DeclarativeGrammar.SelectorNameRejects :=
  DeclarativeGrammar.selectorNameExactOutcomeSpec

/-- Executable successes agree on their complete value and remainder. -/
theorem selectorName_success_result_unique (context : ParseContext)
    {input leftOutput rightOutput : State} {left right : SelectorName}
    (leftResult : selectorName context input = .ok left leftOutput)
    (rightResult : selectorName context input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectorName_exactOutcomeSpec ).successResultUnique
    (selectorName_success_ordinaryOutcome_sound context leftResult)
    (selectorName_success_ordinaryOutcome_sound context rightResult)

/-- Executable rejections agree on their complete declarative endpoint. -/
theorem selectorName_reject_output_unique (context : ParseContext)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : selectorName context input = .reject leftFailure leftOutput)
    (rightResult : selectorName context input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectorName_exactOutcomeSpec ).rejectOutputUnique
    (selectorName_reject_ordinaryOutcome_sound context leftResult)
    (selectorName_reject_ordinaryOutcome_sound context rightResult)

end Solcore.Syntax.Parser
