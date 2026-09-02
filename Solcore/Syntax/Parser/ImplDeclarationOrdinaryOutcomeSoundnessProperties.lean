import Solcore.Syntax.DeclarativeImplDeclarationOutcomeProperties
import Solcore.Syntax.Parser.ImplBodyOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ImplDeclarationOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ImplDeclarationOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for implementation declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package executable implementation success and exact six-stage rejection. -/
theorem implDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : ImplDecl},
      implDecl input = .ok declaration output →
        DeclarativeGrammar.ImplDeclOrdinaryParses input.declarativeRemainder
          declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      implDecl input = .reject failure rejected →
        DeclarativeGrammar.ImplDeclRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨implDecl_success_ordinaryOutcome_sound,
    implDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad implementation outcomes. -/
theorem implDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ImplDeclOrdinaryParses
      DeclarativeGrammar.ImplDeclRejects :=
  DeclarativeGrammar.implDeclDeterministicOutcomeSpec

end Solcore.Syntax.Parser
