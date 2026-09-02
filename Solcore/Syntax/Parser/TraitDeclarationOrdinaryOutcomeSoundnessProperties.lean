import Solcore.Syntax.DeclarativeTraitDeclarationOutcomeProperties
import Solcore.Syntax.Parser.TraitDeclarationOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.TraitDeclarationOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for trait declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package executable trait-declaration success and exact five-stage
rejection. -/
theorem traitDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : TraitDecl},
      traitDecl input = .ok declaration output →
        DeclarativeGrammar.TraitDeclOrdinaryParses input.declarativeRemainder
          declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      traitDecl input = .reject failure rejected →
        DeclarativeGrammar.TraitDeclRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨traitDecl_success_ordinaryOutcome_sound,
    traitDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad trait-declaration outcomes. -/
theorem traitDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TraitDeclOrdinaryParses
      DeclarativeGrammar.TraitDeclRejects :=
  DeclarativeGrammar.traitDeclDeterministicOutcomeSpec

end Solcore.Syntax.Parser
