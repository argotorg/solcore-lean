import Solcore.Syntax.DeclarativeComptimeTypeRejectionTraceProperties
import Solcore.Syntax.Parser.ComptimeTypeRejectionTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Raw comptime prefix failures bypass every child. Closing failure returns
the exact completed-child state, and protected event suffixes retain every
occurrence without including the separate uncommitted rejection report. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedComptimeTypeTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem missing_marker_bypasses_every_child (nested : Parser TypeExpr)
    {input : State} {failure : Failure}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
      (.identifier ContextualKeyword.comptime.spelling))
    (reported : RejectAtReports input.file.id input.window.endByte { head := .contextual .comptime, tail := [] }
      .typeExpr input.declarativeRemainder failure.toDiagnostic) :
    parseComptimeType nested input = .reject failure input := by
  rcases (contextual_reject_reports_iff .comptime .typeExpr).mp ⟨absent, reported⟩ with
    ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  simp only [parseComptimeType, bind, result]

theorem missing_opening_bypasses_every_child (nested : Parser TypeExpr)
    {input afterMarker : State} {marker : Token} {failure : Failure}
    (markerResult : contextual .comptime .typeExpr input = .ok marker afterMarker)
    (absent : TokenKindAbsentAt afterMarker.tokens afterMarker.window.endIndex afterMarker.cursor (.symbol .less))
    (reported : RejectAtReports afterMarker.file.id afterMarker.window.endByte
      { head := .symbol .less, tail := [] } .typeExpr afterMarker.declarativeRemainder failure.toDiagnostic) :
    parseComptimeType nested input = .reject failure afterMarker := by
  rcases (symbol_reject_reports_iff .less .typeExpr).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  simp only [parseComptimeType, bind, markerResult, result]

theorem missing_closing_keeps_complete_child_state (nested : Parser TypeExpr)
    {input afterMarker afterOpening afterInner : State}
    {marker opening : Token} {inner : TypeExpr} {failure : Failure}
    (markerResult : contextual .comptime .typeExpr input = .ok marker afterMarker)
    (openingResult : symbol .less .typeExpr afterMarker = .ok opening afterOpening)
    (childResult : nested afterOpening = .ok inner afterInner)
    (absent : TokenKindAbsentAt afterInner.tokens afterInner.window.endIndex afterInner.cursor (.symbol .greater))
    (reported : RejectAtReports afterInner.file.id afterInner.window.endByte
      { head := .symbol .greater, tail := [] } .typeExpr afterInner.declarativeRemainder failure.toDiagnostic) :
    parseComptimeType nested input = .reject failure afterInner := by
  rcases (symbol_reject_reports_iff .greater .typeExpr).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  simp only [parseComptimeType, bind, markerResult, openingResult, childResult, result]

variable
  {elementTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem success_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {value : TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ComptimeTypeTraceParses elementTrace source endByte input value output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters childProtected))

theorem rejection_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    (rejectProtected : ∀ {input output report trace}, elementRejects source endByte input output report trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeTypeTraceRejects elementTrace elementRejects source endByte input output report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (rejection.cascadeFilters childProtected rejectProtected))

end Solcore.Test.SyntaxProtectedComptimeTypeTraceProperties
