import Solcore.Syntax.DeclarativeFinishExportOutcomeGrammar
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Export

/-! Exact executable rejection reflection for export termination. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable export-finishing rejection is the exact nonconsuming
absence of its required semicolon. -/
theorem finishExport_reject_ordinaryOutcome_sound (start : SourceSpan)
    (value : ExportDeclValue) {input rejected : State} {failure : Failure}
    (result : ExportInternals.finishExport start value input =
      .reject failure rejected) :
    DeclarativeGrammar.FinishExportRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ExportInternals.finishExport at result
  cases semicolonResult : symbol .semicolon .exportDecl input with
  | invariant error => simp [bind, semicolonResult] at result
  | ok semicolon afterSemicolon =>
      simp [bind, semicolonResult, pure] at result
  | reject semicolonFailure semicolonRejected =>
      have rejectedEq := symbol_reject_state_eq .semicolon .exportDecl
        semicolonResult
      simp only [bind, semicolonResult] at result
      cases result
      rw [rejectedEq]
      exact .semicolonMissing
        (symbol_reject_tokenKindAbsentAt .semicolon .exportDecl
          semicolonResult)

end Solcore.Syntax.Parser
