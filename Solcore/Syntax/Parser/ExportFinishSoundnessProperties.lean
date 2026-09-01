import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.ExportProperties

/-! Exact semicolon soundness for canonical export finishing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Successful export finishing consumes one exact semicolon. -/
theorem finishExport_success_sound (start : SourceSpan)
    (value : ExportDeclValue) {input next : State}
    {declaration : ExportDecl}
    (result : ExportInternals.finishExport start value input =
      .ok declaration next) :
    DeclarativeGrammar.FinishExportParses start value
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold ExportInternals.finishExport at result
  cases semicolonResult : symbol .semicolon .exportDecl input with
  | invariant error => simp [bind, semicolonResult] at result
  | reject failure rejected => simp [bind, semicolonResult] at result
  | ok semicolon afterSemicolon =>
      have semicolonSound := symbol_ok_tokenAt .semicolon .exportDecl
        semicolonResult
      simp only [bind, semicolonResult, pure] at result
      cases result
      unfold DeclarativeGrammar.FinishExportParses
      refine ⟨semicolon.span, semicolonSound.1, ?_, rfl⟩
      rw [semicolonSound.2]
      rfl

end Solcore.Syntax.Parser
