import Solcore.Syntax.DeclarativeContractDeclarationOutcomeProperties
import Solcore.Syntax.Parser.ContractDeclarationOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ContractDeclarationOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package executable contract-declaration success and exact four-stage
rejection. -/
theorem contractDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : ContractDecl},
      contractDecl input = .ok declaration output →
        DeclarativeGrammar.ContractDeclOrdinaryParses
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      contractDecl input = .reject failure rejected →
        DeclarativeGrammar.ContractDeclRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨contractDecl_success_ordinaryOutcome_sound,
    contractDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad contract-declaration
outcomes. -/
theorem contractDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ContractDeclOrdinaryParses
      DeclarativeGrammar.ContractDeclRejects :=
  DeclarativeGrammar.contractDeclDeterministicOutcomeSpec

end Solcore.Syntax.Parser
