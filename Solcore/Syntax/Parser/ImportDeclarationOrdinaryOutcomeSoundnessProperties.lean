import Solcore.Syntax.DeclarativeImportDeclOutcomeProperties
import Solcore.Syntax.Parser.ImportDeclarationOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ImportDeclarationOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for import declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package complete-import success and exact prioritized rejection. -/
theorem importDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : ImportDecl},
      importDecl input = .ok declaration output →
        DeclarativeGrammar.ImportDeclOrdinaryParses
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      importDecl input = .reject failure rejected →
        DeclarativeGrammar.ImportDeclRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨importDecl_success_ordinaryOutcome_sound,
    importDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive complete-import outcomes. -/
theorem importDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ImportDeclOrdinaryParses
      DeclarativeGrammar.ImportDeclRejects :=
  DeclarativeGrammar.importDeclDeterministicOutcomeSpec

end Solcore.Syntax.Parser
