import Solcore.Syntax.DeclarativeConstructorDeclarationOutcomeProperties
import Solcore.Syntax.Parser.ConstructorDeclarationOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ConstructorDeclarationOrdinarySuccessSoundnessProperties

/-! Complete executable ordinary outcomes for canonical constructors. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package exact executable constructor success and rejection. -/
theorem constructorDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : ConstructorDecl},
      constructorDecl input = .ok declaration output →
        DeclarativeGrammar.ConstructorDeclOrdinaryParses
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      constructorDecl input = .reject failure rejected →
        DeclarativeGrammar.ConstructorDeclRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨constructorDecl_success_ordinaryOutcome_sound,
    constructorDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export the parser-independent deterministic constructor contract. -/
theorem constructorDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ConstructorDeclOrdinaryParses
      DeclarativeGrammar.ConstructorDeclRejects :=
  DeclarativeGrammar.constructorDeclDeterministicOutcomeSpec

end Solcore.Syntax.Parser
