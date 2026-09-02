import Solcore.Syntax.DeclarativeDeriveTargetOutcomeProperties
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

end Solcore.Syntax.Parser
