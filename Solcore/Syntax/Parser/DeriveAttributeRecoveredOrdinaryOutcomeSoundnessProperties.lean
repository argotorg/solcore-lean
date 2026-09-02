import Solcore.Syntax.DeclarativeDeriveAttributeRecoveryOutcomeProperties
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

end Solcore.Syntax.Parser
