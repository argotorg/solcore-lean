import Solcore.Syntax.DeclarativeExportNameOutcomeProperties
import Solcore.Syntax.Parser.ExportNameOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ExportNameSoundnessProperties

/-! Complete executable broad ordinary outcomes for export names. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export export-name success as a broad ordinary outcome. -/
theorem exportName_success_ordinaryOutcome_sound
    {input output : State} {name : ExportName}
    (result : ExportInternals.exportName input = .ok name output) :
    DeclarativeGrammar.ExportNameOrdinaryParses
      input.declarativeRemainder name output.declarativeRemainder :=
  exportName_success_sound result

/-- Package export-name success and exact prioritized rejection. -/
theorem exportName_ordinaryOutcome_sound :
    (∀ {input output : State} {name : ExportName},
      ExportInternals.exportName input = .ok name output →
        DeclarativeGrammar.ExportNameOrdinaryParses
          input.declarativeRemainder name output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ExportInternals.exportName input = .reject failure rejected →
        DeclarativeGrammar.ExportNameRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨exportName_success_ordinaryOutcome_sound,
    exportName_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive export-name outcomes. -/
theorem exportName_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ExportNameOrdinaryParses
      DeclarativeGrammar.ExportNameRejects :=
  DeclarativeGrammar.exportNameDeterministicOutcomeSpec

end Solcore.Syntax.Parser
