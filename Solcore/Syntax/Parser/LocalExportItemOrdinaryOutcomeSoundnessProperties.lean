import Solcore.Syntax.DeclarativeLocalExportItemExactnessProperties
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

/-- Re-export exact localExportItem outcomes with all supplied span data fixed. -/
theorem localExportItem_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.LocalExportItemOrdinaryParses
      DeclarativeGrammar.LocalExportItemRejects :=
  DeclarativeGrammar.localExportItemExactOutcomeSpec

/-- Two localExportItem successes fix the complete AST and declarative remainder. -/
theorem localExportItem_success_result_unique
    {input leftOutput rightOutput : State} {left right : LocalExportItem}
    (leftResult : ExportInternals.localExportItem input = .ok left leftOutput)
    (rightResult : ExportInternals.localExportItem input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  localExportItem_exactOutcomeSpec.successResultUnique
    (localExportItem_success_ordinaryOutcome_sound leftResult)
    (localExportItem_success_ordinaryOutcome_sound rightResult)

/-- Two localExportItem rejections fix their declarative endpoints; diagnostic
payload equality is not asserted. -/
theorem localExportItem_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : ExportInternals.localExportItem input = .reject leftFailure leftOutput)
    (rightResult : ExportInternals.localExportItem input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  localExportItem_exactOutcomeSpec.rejectOutputUnique
    (localExportItem_reject_ordinaryOutcome_sound leftResult)
    (localExportItem_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
