import Solcore.Syntax.DeclarativeExportPathExactnessProperties
import Solcore.Syntax.DeclarativeExportPathOutcomeProperties
import Solcore.Syntax.Parser.ExportPathOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ExportPathSoundnessProperties

/-! Complete executable broad ordinary outcomes for maximal export paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export maximal export-path success as a broad ordinary outcome. -/
theorem exportPath_success_ordinaryOutcome_sound
    {input output : State} {path : QualifiedName}
    (result : ExportInternals.exportPath input = .ok path output) :
    DeclarativeGrammar.ExportPathOrdinaryParses input.declarativeRemainder
      path output.declarativeRemainder :=
  exportPath_success_sound result

/-- Package maximal export-path success and exact initial rejection. -/
theorem exportPath_ordinaryOutcome_sound :
    (∀ {input output : State} {path : QualifiedName},
      ExportInternals.exportPath input = .ok path output →
        DeclarativeGrammar.ExportPathOrdinaryParses
          input.declarativeRemainder path output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ExportInternals.exportPath input = .reject failure rejected →
        DeclarativeGrammar.ExportPathRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨exportPath_success_ordinaryOutcome_sound,
    exportPath_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive maximal export-path outcomes. -/
theorem exportPath_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ExportPathOrdinaryParses
      DeclarativeGrammar.ExportPathRejects :=
  DeclarativeGrammar.exportPathDeterministicOutcomeSpec


/-- Exact values and endpoints for the independent exportPath grammar. -/
theorem exportPath_exactOutcomeSpec  :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ExportPathOrdinaryParses DeclarativeGrammar.ExportPathRejects :=
  DeclarativeGrammar.exportPathExactOutcomeSpec

/-- Executable successes agree on their complete value and remainder. -/
theorem exportPath_success_result_unique
    {input leftOutput rightOutput : State} {left right : QualifiedName}
    (leftResult : ExportInternals.exportPath input = .ok left leftOutput)
    (rightResult : ExportInternals.exportPath input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (exportPath_exactOutcomeSpec ).successResultUnique
    (exportPath_success_ordinaryOutcome_sound  leftResult)
    (exportPath_success_ordinaryOutcome_sound  rightResult)

/-- Executable rejections agree on their complete declarative endpoint. -/
theorem exportPath_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ExportInternals.exportPath input = .reject leftFailure leftOutput)
    (rightResult : ExportInternals.exportPath input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (exportPath_exactOutcomeSpec ).rejectOutputUnique
    (exportPath_reject_ordinaryOutcome_sound  leftResult)
    (exportPath_reject_ordinaryOutcome_sound  rightResult)

end Solcore.Syntax.Parser
