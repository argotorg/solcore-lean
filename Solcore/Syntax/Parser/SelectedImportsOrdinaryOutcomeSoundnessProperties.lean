import Solcore.Syntax.DeclarativeSelectedImportsOutcomeProperties
import Solcore.Syntax.Parser.SelectedImportsOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.SelectedImportsOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for selected-import lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package selected-import-list success and exact delimited rejection. -/
theorem selectedImports_ordinaryOutcome_sound :
    (∀ {input output : State}
        {selections : NonemptyDelimitedList SelectedImport},
      ImportInternals.selectedImports input = .ok selections output →
        DeclarativeGrammar.SelectedImportsOrdinaryParses
          input.declarativeRemainder selections output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ImportInternals.selectedImports input = .reject failure rejected →
        DeclarativeGrammar.SelectedImportsRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨selectedImports_success_ordinaryOutcome_sound,
    selectedImports_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive selected-import-list outcomes. -/
theorem selectedImports_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.SelectedImportsOrdinaryParses
      DeclarativeGrammar.SelectedImportsRejects :=
  DeclarativeGrammar.selectedImportsDeterministicOutcomeSpec

end Solcore.Syntax.Parser
