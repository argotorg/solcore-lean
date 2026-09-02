import Solcore.Syntax.DeclarativeExportDeclOutcomeProperties
import Solcore.Syntax.Parser.ExportDeclarationOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ExportDeclSoundnessProperties

/-! Complete executable broad ordinary outcomes for export declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export complete-export success as a broad ordinary outcome. -/
theorem exportDecl_success_ordinaryOutcome_sound
    {input output : State} {declaration : ExportDecl}
    (result : exportDecl input = .ok declaration output) :
    DeclarativeGrammar.ExportDeclOrdinaryParses
      input.declarativeRemainder declaration output.declarativeRemainder :=
  exportDecl_success_sound result

/-- Package complete-export success and exact prioritized rejection. -/
theorem exportDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : ExportDecl},
      exportDecl input = .ok declaration output →
        DeclarativeGrammar.ExportDeclOrdinaryParses
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      exportDecl input = .reject failure rejected →
        DeclarativeGrammar.ExportDeclRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨exportDecl_success_ordinaryOutcome_sound,
    exportDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive complete-export outcomes. -/
theorem exportDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ExportDeclOrdinaryParses
      DeclarativeGrammar.ExportDeclRejects :=
  DeclarativeGrammar.exportDeclDeterministicOutcomeSpec

end Solcore.Syntax.Parser
