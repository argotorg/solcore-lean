import Solcore.Syntax.DeclarativeLocalExportOutcomeProperties
import Solcore.Syntax.Parser.LocalExportOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.LocalExportSoundnessProperties

/-! Complete executable broad ordinary outcomes for local export payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export local-export success as a broad ordinary outcome. -/
theorem localExport_success_ordinaryOutcome_sound (start : SourceSpan)
    {input output : State} {declaration : ExportDecl}
    (result : ExportInternals.localExport start input =
      .ok declaration output) :
    DeclarativeGrammar.LocalExportOrdinaryParses start
      input.declarativeRemainder declaration output.declarativeRemainder :=
  localExport_success_sound start result

/-- Package local-export success and exact prioritized rejection. -/
theorem localExport_ordinaryOutcome_sound (start : SourceSpan) :
    (∀ {input output : State} {declaration : ExportDecl},
      ExportInternals.localExport start input = .ok declaration output →
        DeclarativeGrammar.LocalExportOrdinaryParses start
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ExportInternals.localExport start input = .reject failure rejected →
        DeclarativeGrammar.LocalExportRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨localExport_success_ordinaryOutcome_sound start,
    localExport_reject_ordinaryOutcome_sound start⟩

/-- Re-export deterministic and exclusive local-export outcomes. -/
theorem localExport_ordinaryOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.LocalExportOrdinaryParses start)
      DeclarativeGrammar.LocalExportRejects :=
  DeclarativeGrammar.localExportDeterministicOutcomeSpec start

end Solcore.Syntax.Parser
