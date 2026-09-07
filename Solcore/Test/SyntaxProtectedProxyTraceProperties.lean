import Solcore.Syntax.DeclarativeProxyExpressionRejectionTraceProperties
import Solcore.Syntax.Parser.ProxyExpressionRejectionTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Proxy normalization inherits exactly the type's protected trace. Marker
failure bypasses the type with unchanged full State and an uncommitted report. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedProxyTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

theorem missing_marker_preserves_every_state_field
    {input : State} {failure : Failure}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .at))
    (reported : RejectAtReports input.file.id input.window.endByte
      { head := .symbol .at, tail := [] } .expression input.declarativeRemainder failure.toDiagnostic) :
    proxyExpression input = .reject failure input := by
  rcases (symbol_reject_reports_iff .at .expression).mp ⟨absent, reported⟩ with
    ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  exact proxyExpression_reject_iff_components.mpr (.inl result)

theorem successful_proxy_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {typeTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat} {input output : Remainder} {value : Expr}
    {trace : List ParseDiagnostic}
    (childProtected : ∀ {input type output trace}, typeTrace source endByte input type output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    (parsed : ProxyExpressionTraceParses typeTrace source endByte input value output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters childProtected)

theorem rejected_proxy_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {typeRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (childProtected : ∀ {input rejected report trace}, typeRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    (rejection : ProxyExpressionTraceRejects typeRejects source endByte input rejected report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical (rejection.cascadeFilters childProtected)

end Solcore.Test.SyntaxProtectedProxyTraceProperties
