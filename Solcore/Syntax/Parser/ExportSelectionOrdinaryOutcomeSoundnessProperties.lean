import Solcore.Syntax.DeclarativeExportSelectionOutcomeProperties
import Solcore.Syntax.Parser.ExportSelectionOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ExportSelectionSoundnessProperties

/-! Complete executable broad ordinary outcomes for export selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export export-selection success as a broad ordinary outcome. -/
theorem exportSelection_success_ordinaryOutcome_sound
    {input output : State} {selection : ExportSelection}
    (result : ExportInternals.exportSelection input = .ok selection output) :
    DeclarativeGrammar.ExportSelectionOrdinaryParses
      input.declarativeRemainder selection output.declarativeRemainder :=
  exportSelection_success_sound result

/-- Package export-selection success and exact prioritized rejection. -/
theorem exportSelection_ordinaryOutcome_sound :
    (∀ {input output : State} {selection : ExportSelection},
      ExportInternals.exportSelection input = .ok selection output →
        DeclarativeGrammar.ExportSelectionOrdinaryParses
          input.declarativeRemainder selection output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ExportInternals.exportSelection input = .reject failure rejected →
        DeclarativeGrammar.ExportSelectionRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨exportSelection_success_ordinaryOutcome_sound,
    exportSelection_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive export-selection outcomes. -/
theorem exportSelection_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ExportSelectionOrdinaryParses
      DeclarativeGrammar.ExportSelectionRejects :=
  DeclarativeGrammar.exportSelectionDeterministicOutcomeSpec

end Solcore.Syntax.Parser
