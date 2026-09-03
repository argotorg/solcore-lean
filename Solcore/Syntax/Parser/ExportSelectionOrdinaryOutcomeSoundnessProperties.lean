import Solcore.Syntax.DeclarativeExportSelectionExactnessProperties
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

/-- Re-export exact exportSelection outcomes with all supplied span data fixed. -/
theorem exportSelection_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ExportSelectionOrdinaryParses
      DeclarativeGrammar.ExportSelectionRejects :=
  DeclarativeGrammar.exportSelectionExactOutcomeSpec

/-- Two exportSelection successes fix the complete AST and declarative remainder. -/
theorem exportSelection_success_result_unique
    {input leftOutput rightOutput : State} {left right : ExportSelection}
    (leftResult : ExportInternals.exportSelection input = .ok left leftOutput)
    (rightResult : ExportInternals.exportSelection input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  exportSelection_exactOutcomeSpec.successResultUnique
    (exportSelection_success_ordinaryOutcome_sound leftResult)
    (exportSelection_success_ordinaryOutcome_sound rightResult)

/-- Two exportSelection rejections fix their declarative endpoints; diagnostic
payload equality is not asserted. -/
theorem exportSelection_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : ExportInternals.exportSelection input = .reject leftFailure leftOutput)
    (rightResult : ExportInternals.exportSelection input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  exportSelection_exactOutcomeSpec.rejectOutputUnique
    (exportSelection_reject_ordinaryOutcome_sound leftResult)
    (exportSelection_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
