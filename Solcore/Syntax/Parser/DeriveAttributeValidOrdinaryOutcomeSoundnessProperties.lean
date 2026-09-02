import Solcore.Syntax.DeclarativeDeriveAttributeValidExactnessProperties
import Solcore.Syntax.Parser.DeriveAttributeSoundnessProperties
import Solcore.Syntax.Parser.DeriveAttributeValidOrdinaryRejectionSoundnessProperties

/-! Complete broad executable outcomes for the normal derive-attribute path. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export normal-path success reflection under the ordinary-outcome naming
convention. -/
theorem deriveAttributeValid_success_ordinaryOutcome_sound
    {input output : State} {value : DeriveAttribute}
    (result : DeriveAttributeInternals.valid input = .ok value output) :
    DeclarativeGrammar.DeriveAttributeParses input.declarativeRemainder value
      output.declarativeRemainder :=
  deriveAttributeValid_success_sound result

/-- Re-export exact normal-path rejection reflection outside the internal
namespace. -/
theorem deriveAttributeValid_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : DeriveAttributeInternals.valid input =
      .reject failure rejected) :
    DeclarativeGrammar.DeriveAttributeValidRejects
      input.declarativeRemainder rejected.declarativeRemainder :=
  DeriveAttributeInternals.valid_reject_ordinaryOutcome_sound result

/-- Package unconditional success and exact rejection reflection for the
normal derive-attribute path. -/
theorem deriveAttributeValid_ordinaryOutcome_sound :
    (∀ {input output : State} {value : DeriveAttribute},
      DeriveAttributeInternals.valid input = .ok value output →
        DeclarativeGrammar.DeriveAttributeParses input.declarativeRemainder
          value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      DeriveAttributeInternals.valid input = .reject failure rejected →
        DeclarativeGrammar.DeriveAttributeValidRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨deriveAttributeValid_success_ordinaryOutcome_sound,
    deriveAttributeValid_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive normal derive-attribute outcomes. -/
theorem deriveAttributeValid_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.DeriveAttributeParses
      DeclarativeGrammar.DeriveAttributeValidRejects :=
  DeclarativeGrammar.deriveAttributeValidDeterministicOutcomeSpec

/-- Re-export exact normal-path value and rejection-endpoint functionality. -/
theorem deriveAttributeValid_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.DeriveAttributeParses
      DeclarativeGrammar.DeriveAttributeValidRejects :=
  DeclarativeGrammar.deriveAttributeValidExactOutcomeSpec

/-- Two successful normal-path reflections have the same derive attribute and
final declarative remainder. -/
theorem deriveAttributeValid_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : DeriveAttribute}
    (leftResult : DeriveAttributeInternals.valid input =
      .ok left leftOutput)
    (rightResult : DeriveAttributeInternals.valid input =
      .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.DeriveAttributeParses.result_unique
    (deriveAttributeValid_success_ordinaryOutcome_sound leftResult)
    (deriveAttributeValid_success_ordinaryOutcome_sound rightResult)

/-- Two rejected normal-path reflections have the same exact declarative
endpoint. -/
theorem deriveAttributeValid_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : DeriveAttributeInternals.valid input =
      .reject leftFailure leftOutput)
    (rightResult : DeriveAttributeInternals.valid input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.DeriveAttributeValidRejects.output_unique
    (deriveAttributeValid_reject_ordinaryOutcome_sound leftResult)
    (deriveAttributeValid_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
