import Solcore.Syntax.DeclarativeLocalExportOutcomeGrammar
import Solcore.Syntax.Parser.DelimitedAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.FinishExportOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.LocalExportItemOrdinaryOutcomeSoundnessProperties

/-! Exact executable rejection reflection for local export payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable local-export rejection occurs either in the prioritized
braced item list or at the exact non-recovering semicolon finish. -/
theorem localExport_reject_ordinaryOutcome_sound (start : SourceSpan)
    {input rejected : State} {failure : Failure}
    (result : ExportInternals.localExport start input =
      .reject failure rejected) :
    DeclarativeGrammar.LocalExportRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ExportInternals.localExport at result
  cases itemsResult : delimited .leftBrace .rightBrace true
      ExportInternals.localExportItem .exportDecl .topLevel input with
  | invariant error => simp [bind, itemsResult] at result
  | reject itemsFailure itemsRejected =>
      simp only [bind, itemsResult] at result
      cases result
      exact .itemsRejected
        (delimited_reject_sound .leftBrace .rightBrace true
          ExportInternals.localExportItem
          DeclarativeGrammar.LocalExportItemOrdinaryParses
          DeclarativeGrammar.LocalExportItemRejects .exportDecl .topLevel
          localExportItem_success_ordinaryOutcome_sound
          localExportItem_reject_ordinaryOutcome_sound itemsResult)
  | ok items afterItems =>
      have itemsParsed := delimited_allowEmpty_trailing_success_sound
        .leftBrace .rightBrace ExportInternals.localExportItem
        DeclarativeGrammar.LocalExportItemOrdinaryParses .exportDecl .topLevel
        localExportItem_success_ordinaryOutcome_sound
        localExportItem_preservesTokenWindow itemsResult
      simp only [bind, itemsResult] at result
      exact .finishRejected itemsParsed
        (finishExport_reject_ordinaryOutcome_sound start (.local items) result)

end Solcore.Syntax.Parser
