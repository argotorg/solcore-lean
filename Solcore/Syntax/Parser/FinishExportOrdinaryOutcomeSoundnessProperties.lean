import Solcore.Syntax.DeclarativeFinishExportOutcomeProperties
import Solcore.Syntax.Parser.ExportFinishSoundnessProperties
import Solcore.Syntax.Parser.FinishExportOrdinaryRejectionSoundnessProperties

/-! Complete executable broad ordinary outcomes for export termination. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export exact export-finishing success as a broad ordinary outcome. -/
theorem finishExport_success_ordinaryOutcome_sound (start : SourceSpan)
    (value : ExportDeclValue) {input output : State}
    {declaration : ExportDecl}
    (result : ExportInternals.finishExport start value input =
      .ok declaration output) :
    DeclarativeGrammar.FinishExportOrdinaryParses start value
      input.declarativeRemainder declaration output.declarativeRemainder :=
  finishExport_success_sound start value result

/-- Package exact export-finishing success and missing-semicolon rejection. -/
theorem finishExport_ordinaryOutcome_sound (start : SourceSpan)
    (value : ExportDeclValue) :
    (∀ {input output : State} {declaration : ExportDecl},
      ExportInternals.finishExport start value input = .ok declaration output →
        DeclarativeGrammar.FinishExportOrdinaryParses start value
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ExportInternals.finishExport start value input = .reject failure rejected →
        DeclarativeGrammar.FinishExportRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨finishExport_success_ordinaryOutcome_sound start value,
    finishExport_reject_ordinaryOutcome_sound start value⟩

/-- Re-export deterministic and exclusive export-finishing outcomes. -/
theorem finishExport_ordinaryOutcomeSpec (start : SourceSpan)
    (value : ExportDeclValue) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.FinishExportOrdinaryParses start value)
      DeclarativeGrammar.FinishExportRejects :=
  DeclarativeGrammar.finishExportDeterministicOutcomeSpec start value

end Solcore.Syntax.Parser
