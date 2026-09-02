import Solcore.Syntax.DeclarativeDeriveTargetOutcomeProperties
import Solcore.Syntax.DeclarativeDeriveTargetExactnessProperties
import Solcore.Syntax.Parser.DeriveTargetOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.DeriveTargetSoundnessProperties

/-! Complete broad executable outcomes for dotted derive targets. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export successful derive-target reflection under the ordinary-outcome
naming convention. -/
theorem deriveTarget_success_ordinaryOutcome_sound {input output : State}
    {target : DeriveTarget}
    (result : deriveTarget input = .ok target output) :
    DeclarativeGrammar.DeriveTargetParses input.declarativeRemainder target
      output.declarativeRemainder :=
  deriveTarget_success_sound result

/-- Package unconditional executable success and exact rejection for one
dotted derive target. -/
theorem deriveTarget_ordinaryOutcome_sound :
    (∀ {input output : State} {target : DeriveTarget},
      deriveTarget input = .ok target output →
        DeclarativeGrammar.DeriveTargetParses input.declarativeRemainder
          target output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      deriveTarget input = .reject failure rejected →
        DeclarativeGrammar.DeriveTargetRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨deriveTarget_success_ordinaryOutcome_sound,
    deriveTarget_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive derive-target outcomes. -/
theorem deriveTarget_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.DeriveTargetParses
      DeclarativeGrammar.DeriveTargetRejects :=
  DeclarativeGrammar.deriveTargetDeterministicOutcomeSpec

/-- Re-export full value and rejection-endpoint functionality for derive
targets at the executable reflection boundary. -/
theorem deriveTarget_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.DeriveTargetParses
      DeclarativeGrammar.DeriveTargetRejects :=
  DeclarativeGrammar.deriveTargetExactOutcomeSpec

/-- Two successful executable reflections have the same declarative target
and final remainder. -/
theorem deriveTarget_success_result_unique
    {input leftOutput rightOutput : State} {left right : DeriveTarget}
    (leftResult : deriveTarget input = .ok left leftOutput)
    (rightResult : deriveTarget input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.DeriveTargetParses.result_unique
    (deriveTarget_success_ordinaryOutcome_sound leftResult)
    (deriveTarget_success_ordinaryOutcome_sound rightResult)

/-- Two rejected executable reflections have the same exact declarative
endpoint. -/
theorem deriveTarget_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : deriveTarget input = .reject leftFailure leftOutput)
    (rightResult : deriveTarget input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.DeriveTargetRejects.output_unique
    (deriveTarget_reject_ordinaryOutcome_sound leftResult)
    (deriveTarget_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
