import Solcore.Syntax.Parser.DelimitedAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.ExportFinishSoundnessProperties
import Solcore.Syntax.Parser.LocalExportItemSoundnessProperties

/-! Success soundness of braced local export declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A successful local-export helper follows its complete tail grammar. -/
theorem localExport_success_sound (start : SourceSpan)
    {input next : State} {declaration : ExportDecl}
    (result : ExportInternals.localExport start input =
      .ok declaration next) :
    DeclarativeGrammar.LocalExportTailParses start
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold ExportInternals.localExport at result
  cases itemsResult : delimited .leftBrace .rightBrace true
      ExportInternals.localExportItem .exportDecl .topLevel input with
  | invariant error => simp [bind, itemsResult] at result
  | reject failure rejected => simp [bind, itemsResult] at result
  | ok items afterItems =>
      have itemsGrammar := delimited_allowEmpty_trailing_success_sound
        .leftBrace .rightBrace ExportInternals.localExportItem
        DeclarativeGrammar.LocalExportItemParses .exportDecl .topLevel
        localExportItem_success_sound localExportItem_preservesTokenWindow
        itemsResult
      simp only [bind, itemsResult] at result
      have finishGrammar := finishExport_success_sound start (.local items)
        result
      unfold DeclarativeGrammar.LocalExportTailParses
      exact ⟨items, afterItems.declarativeRemainder, itemsGrammar,
        finishGrammar⟩

end Solcore.Syntax.Parser
