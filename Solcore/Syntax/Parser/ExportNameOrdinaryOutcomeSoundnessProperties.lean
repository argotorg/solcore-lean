import Solcore.Syntax.DeclarativeExportNameExactnessProperties
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

/-- Re-export exact exportName outcomes with all supplied span data fixed. -/
theorem exportName_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ExportNameOrdinaryParses
      DeclarativeGrammar.ExportNameRejects :=
  DeclarativeGrammar.exportNameExactOutcomeSpec

/-- Two exportName successes fix the complete AST and declarative remainder. -/
theorem exportName_success_result_unique
    {input leftOutput rightOutput : State} {left right : ExportName}
    (leftResult : ExportInternals.exportName input = .ok left leftOutput)
    (rightResult : ExportInternals.exportName input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  exportName_exactOutcomeSpec.successResultUnique
    (exportName_success_ordinaryOutcome_sound leftResult)
    (exportName_success_ordinaryOutcome_sound rightResult)

/-- Two exportName rejections fix their declarative endpoints; diagnostic
payload equality is not asserted. -/
theorem exportName_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : ExportInternals.exportName input = .reject leftFailure leftOutput)
    (rightResult : ExportInternals.exportName input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  exportName_exactOutcomeSpec.rejectOutputUnique
    (exportName_reject_ordinaryOutcome_sound leftResult)
    (exportName_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
