import Solcore.Syntax.DeclarativePathExportOutcomeProperties
import Solcore.Syntax.Parser.PathExportOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.PathExportSoundnessProperties

/-! Complete executable broad ordinary outcomes for path export payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export path-export success as a broad ordinary outcome. -/
theorem pathExport_success_ordinaryOutcome_sound (start : SourceSpan)
    {input output : State} {declaration : ExportDecl}
    (result : ExportInternals.pathExport start input =
      .ok declaration output) :
    DeclarativeGrammar.PathExportOrdinaryParses start
      input.declarativeRemainder declaration output.declarativeRemainder :=
  pathExport_success_sound start result

/-- Package path-export success and exact prioritized rejection. -/
theorem pathExport_ordinaryOutcome_sound (start : SourceSpan) :
    (∀ {input output : State} {declaration : ExportDecl},
      ExportInternals.pathExport start input = .ok declaration output →
        DeclarativeGrammar.PathExportOrdinaryParses start
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ExportInternals.pathExport start input = .reject failure rejected →
        DeclarativeGrammar.PathExportRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨pathExport_success_ordinaryOutcome_sound start,
    pathExport_reject_ordinaryOutcome_sound start⟩

/-- Re-export deterministic and exclusive path-export outcomes. -/
theorem pathExport_ordinaryOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.PathExportOrdinaryParses start)
      DeclarativeGrammar.PathExportRejects :=
  DeclarativeGrammar.pathExportDeterministicOutcomeSpec start

end Solcore.Syntax.Parser
