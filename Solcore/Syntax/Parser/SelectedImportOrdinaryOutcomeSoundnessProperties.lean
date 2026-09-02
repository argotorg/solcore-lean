import Solcore.Syntax.DeclarativeSelectedImportOutcomeProperties
import Solcore.Syntax.Parser.SelectedImportOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.SelectedImportOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for one selected import. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package selected-import success and exact sequential rejection. -/
theorem selectedImport_ordinaryOutcome_sound :
    (∀ {input output : State} {selection : SelectedImport},
      selectedImport input = .ok selection output →
        DeclarativeGrammar.SelectedImportOrdinaryParses
          input.declarativeRemainder selection output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      selectedImport input = .reject failure rejected →
        DeclarativeGrammar.SelectedImportRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨selectedImport_success_ordinaryOutcome_sound,
    selectedImport_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive selected-import outcomes. -/
theorem selectedImport_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.SelectedImportOrdinaryParses
      DeclarativeGrammar.SelectedImportRejects :=
  DeclarativeGrammar.selectedImportDeterministicOutcomeSpec

end Solcore.Syntax.Parser
