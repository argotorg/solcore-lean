import Solcore.Syntax.DeclarativeLocalExportItemOutcomeProperties
import Solcore.Syntax.Parser.LocalExportItemOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.LocalExportItemSoundnessProperties

/-! Complete executable broad ordinary outcomes for local export items. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export local-export-item success as a broad ordinary outcome. -/
theorem localExportItem_success_ordinaryOutcome_sound
    {input output : State} {item : LocalExportItem}
    (result : ExportInternals.localExportItem input = .ok item output) :
    DeclarativeGrammar.LocalExportItemOrdinaryParses
      input.declarativeRemainder item output.declarativeRemainder :=
  localExportItem_success_sound result

/-- Package local-export-item success and exact prioritized rejection. -/
theorem localExportItem_ordinaryOutcome_sound :
    (∀ {input output : State} {item : LocalExportItem},
      ExportInternals.localExportItem input = .ok item output →
        DeclarativeGrammar.LocalExportItemOrdinaryParses
          input.declarativeRemainder item output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ExportInternals.localExportItem input = .reject failure rejected →
        DeclarativeGrammar.LocalExportItemRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨localExportItem_success_ordinaryOutcome_sound,
    localExportItem_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive local-export-item outcomes. -/
theorem localExportItem_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.LocalExportItemOrdinaryParses
      DeclarativeGrammar.LocalExportItemRejects :=
  DeclarativeGrammar.localExportItemDeterministicOutcomeSpec

end Solcore.Syntax.Parser
