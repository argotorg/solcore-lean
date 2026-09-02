import Solcore.Syntax.DeclarativeContractMemberCoreOutcomeProperties
import Solcore.Syntax.Parser.ContractMemberCoreOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ContractMemberCoreOrdinarySuccessSoundnessProperties

/-! Complete broad executable outcomes for attribute-free contract members. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Package unconditional executable success and exact selected-branch
rejection for attribute-free contract members. -/
theorem contractMemberCore_ordinaryOutcome_sound :
    (∀ {input output : State} {member : ContractMember},
      contractMemberCore input = .ok member output →
        DeclarativeGrammar.ContractMemberCoreOrdinaryParses
          input.declarativeRemainder member output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      contractMemberCore input = .reject failure rejected →
        DeclarativeGrammar.ContractMemberCoreRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨contractMemberCore_success_ordinaryOutcome_sound,
    contractMemberCore_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive attribute-free member outcomes. -/
theorem contractMemberCore_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects :=
  DeclarativeGrammar.contractMemberCoreDeterministicOutcomeSpec

end Solcore.Syntax.Parser.ContractInternals
