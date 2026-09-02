import Solcore.Syntax.DeclarativeExportSelectionOutcomeGrammar
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.ExportNameOrdinaryOutcomeSoundnessProperties

/-! Exact executable rejection reflection for export selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable export-selection rejection is the exact braced-list
failure reached after the prioritized wildcard guard is absent. -/
theorem exportSelection_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : ExportInternals.exportSelection input =
      .reject failure rejected) :
    DeclarativeGrammar.ExportSelectionRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ExportInternals.exportSelection at result
  by_cases starPresent : isSymbol input .star = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .star .exportDecl starPresent with
      ⟨marker, markerResult⟩
    simp [starPresent, markerResult] at result
  · have starAbsent : isSymbol input .star = false :=
      Bool.eq_false_iff.mpr starPresent
    simp only [starAbsent, Bool.false_eq_true, if_false] at result
    have starMissing := symbolAbsentAt_of_isSymbol_eq_false .star starAbsent
    cases itemsResult : delimited .leftBrace .rightBrace true
        ExportInternals.exportName .exportDecl .topLevel input with
    | invariant error => simp [itemsResult] at result
    | ok items afterItems => simp [itemsResult] at result
    | reject itemsFailure itemsRejected =>
        simp only [itemsResult] at result
        cases result
        exact .selectedRejected starMissing
          (delimited_reject_sound .leftBrace .rightBrace true
            ExportInternals.exportName
            DeclarativeGrammar.ExportNameOrdinaryParses
            DeclarativeGrammar.ExportNameRejects .exportDecl .topLevel
            exportName_success_ordinaryOutcome_sound
            exportName_reject_ordinaryOutcome_sound itemsResult)

end Solcore.Syntax.Parser
