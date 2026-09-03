import Solcore.Syntax.DeclarativeFinishExportExactnessProperties
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


/-- Exact values and endpoints for the independent finishExport grammar. -/
theorem finishExport_exactOutcomeSpec (start : SourceSpan) (value : ExportDeclValue) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.FinishExportOrdinaryParses start value) DeclarativeGrammar.FinishExportRejects :=
  DeclarativeGrammar.finishExportExactOutcomeSpec start value

/-- Executable successes agree on their complete value and remainder. -/
theorem finishExport_success_result_unique (start : SourceSpan) (value : ExportDeclValue)
    {input leftOutput rightOutput : State} {left right : ExportDecl}
    (leftResult : ExportInternals.finishExport start value input = .ok left leftOutput)
    (rightResult : ExportInternals.finishExport start value input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (finishExport_exactOutcomeSpec start value).successResultUnique
    (finishExport_success_ordinaryOutcome_sound start value leftResult)
    (finishExport_success_ordinaryOutcome_sound start value rightResult)

/-- Executable rejections agree on their complete declarative endpoint. -/
theorem finishExport_reject_output_unique (start : SourceSpan) (value : ExportDeclValue)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ExportInternals.finishExport start value input = .reject leftFailure leftOutput)
    (rightResult : ExportInternals.finishExport start value input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (finishExport_exactOutcomeSpec start value).rejectOutputUnique
    (finishExport_reject_ordinaryOutcome_sound start value leftResult)
    (finishExport_reject_ordinaryOutcome_sound start value rightResult)

end Solcore.Syntax.Parser
