import Solcore.Syntax.DeclarativePathExportExactnessProperties
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

/-- Re-export exact pathExport outcomes with all supplied span data fixed. -/
theorem pathExport_exactOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.PathExportOrdinaryParses start)
      DeclarativeGrammar.PathExportRejects :=
  DeclarativeGrammar.pathExportExactOutcomeSpec start

/-- Two pathExport successes fix the complete AST and declarative remainder. -/
theorem pathExport_success_result_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {left right : ExportDecl}
    (leftResult : ExportInternals.pathExport start input = .ok left leftOutput)
    (rightResult : ExportInternals.pathExport start input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (pathExport_exactOutcomeSpec start).successResultUnique
    (pathExport_success_ordinaryOutcome_sound start leftResult)
    (pathExport_success_ordinaryOutcome_sound start rightResult)

/-- Two pathExport rejections fix their declarative endpoints; diagnostic
payload equality is not asserted. -/
theorem pathExport_reject_output_unique (start : SourceSpan)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : ExportInternals.pathExport start input = .reject leftFailure leftOutput)
    (rightResult : ExportInternals.pathExport start input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (pathExport_exactOutcomeSpec start).rejectOutputUnique
    (pathExport_reject_ordinaryOutcome_sound start leftResult)
    (pathExport_reject_ordinaryOutcome_sound start rightResult)

end Solcore.Syntax.Parser
