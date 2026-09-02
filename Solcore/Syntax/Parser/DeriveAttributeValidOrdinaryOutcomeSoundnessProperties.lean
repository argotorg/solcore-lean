import Solcore.Syntax.DeclarativeDeriveAttributeValidOutcomeProperties
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

end Solcore.Syntax.Parser
