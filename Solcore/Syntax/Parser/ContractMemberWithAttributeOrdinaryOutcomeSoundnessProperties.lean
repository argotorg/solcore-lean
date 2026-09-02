import Solcore.Syntax.DeclarativeContractMemberWithAttributeOutcomeProperties
import Solcore.Syntax.Parser.ContractMemberWithAttributeOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ContractMemberWithAttributeOrdinarySuccessSoundnessProperties

/-! Complete broad executable outcomes for derive-aware contract members. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Package unconditional executable success and exact selected-stage
rejection for derive-aware contract members. -/
theorem contractMemberWithAttribute_ordinaryOutcome_sound :
    (∀ {input output : State} {member : ContractMember},
      contractMemberWithAttribute input = .ok member output →
        DeclarativeGrammar.ContractMemberOrdinaryParses
          input.declarativeRemainder member output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      contractMemberWithAttribute input = .reject failure rejected →
        DeclarativeGrammar.ContractMemberRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨contractMemberWithAttribute_success_ordinaryOutcome_sound,
    contractMemberWithAttribute_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive derive-aware member outcomes. -/
theorem contractMemberWithAttribute_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberOrdinaryParses
      DeclarativeGrammar.ContractMemberRejects :=
  DeclarativeGrammar.contractMemberDeterministicOutcomeSpec

end Solcore.Syntax.Parser.ContractInternals
