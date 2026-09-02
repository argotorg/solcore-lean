import Solcore.Syntax.DeclarativeDeriveAttributeRecoveryExactnessProperties
import Solcore.Syntax.Parser.DeriveAttributeRecoveredOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.DeriveAttributeRecoveredOrdinarySuccessSoundnessProperties

/-! Complete broad executable outcomes for derive-attribute recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export recovered-path success reflection outside the internal
namespace. -/
theorem deriveAttributeRecovered_success_ordinaryOutcome_sound
    {input output : State} {value : DeriveAttribute}
    (result : DeriveAttributeInternals.recovered input = .ok value output) :
    DeclarativeGrammar.DeriveAttributeRecoveredParses
      input.declarativeRemainder value output.declarativeRemainder :=
  DeriveAttributeInternals.recovered_success_ordinaryOutcome_sound result

/-- Re-export recovered-path rejection reflection outside the internal
namespace. -/
theorem deriveAttributeRecovered_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : DeriveAttributeInternals.recovered input =
      .reject failure rejected) :
    DeclarativeGrammar.DeriveAttributeRecoveredRejects
      input.declarativeRemainder rejected.declarativeRemainder :=
  DeriveAttributeInternals.recovered_reject_ordinaryOutcome_sound result

/-- Package unconditional success and exact rejection reflection for the
recovered derive-attribute path. -/
theorem deriveAttributeRecovered_ordinaryOutcome_sound :
    (∀ {input output : State} {value : DeriveAttribute},
      DeriveAttributeInternals.recovered input = .ok value output →
        DeclarativeGrammar.DeriveAttributeRecoveredParses
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      DeriveAttributeInternals.recovered input = .reject failure rejected →
        DeclarativeGrammar.DeriveAttributeRecoveredRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨deriveAttributeRecovered_success_ordinaryOutcome_sound,
    deriveAttributeRecovered_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive recovered derive outcomes. -/
theorem deriveAttributeRecovered_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.DeriveAttributeRecoveredParses
      DeclarativeGrammar.DeriveAttributeRecoveredRejects :=
  DeclarativeGrammar.deriveAttributeRecoveredDeterministicOutcomeSpec

/-- Re-export exact recovered-path value and rejection-endpoint
functionality. -/
theorem deriveAttributeRecovered_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.DeriveAttributeRecoveredParses
      DeclarativeGrammar.DeriveAttributeRecoveredRejects :=
  DeclarativeGrammar.deriveAttributeRecoveredExactOutcomeSpec

/-- Two successful recovered-path reflections have the same derive attribute
and final declarative remainder. -/
theorem deriveAttributeRecovered_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : DeriveAttribute}
    (leftResult : DeriveAttributeInternals.recovered input =
      .ok left leftOutput)
    (rightResult : DeriveAttributeInternals.recovered input =
      .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.DeriveAttributeRecoveredParses.result_unique
    (deriveAttributeRecovered_success_ordinaryOutcome_sound leftResult)
    (deriveAttributeRecovered_success_ordinaryOutcome_sound rightResult)

/-- Two rejected recovered-path reflections have the same exact declarative
endpoint. -/
theorem deriveAttributeRecovered_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : DeriveAttributeInternals.recovered input =
      .reject leftFailure leftOutput)
    (rightResult : DeriveAttributeInternals.recovered input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.DeriveAttributeRecoveredRejects.output_unique
    (deriveAttributeRecovered_reject_ordinaryOutcome_sound leftResult)
    (deriveAttributeRecovered_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
