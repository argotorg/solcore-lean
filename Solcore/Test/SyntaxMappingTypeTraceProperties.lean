import Solcore.Syntax.Parser.MappingTypeTraceProperties
import Solcore.Syntax.Parser.MappingTypeRejectionTraceCorrespondenceProperties
import Solcore.Syntax.DeclarativeMappingTypeRejectionTraceProtectionProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Raw prefix failures bypass all children, while a missing closing delimiter
preserves both completed children and their exact state. The protected suffix
includes all repeated events, but not the separate uncommitted failure report. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxMappingTypeTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem missing_marker_bypasses_every_child (nested : Parser TypeExpr)
    {input : State} {failure : Failure}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
      (.identifier ContextualKeyword.mapping.spelling))
    (reported : RejectAtReports input.file.id input.window.endByte { head := .contextual .mapping, tail := [] }
      .typeExpr input.declarativeRemainder failure.toDiagnostic) :
    parseMappingType nested input = .reject failure input := by
  rcases (contextual_reject_reports_iff .mapping .typeExpr).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  simp only [parseMappingType, bind, result]

theorem missing_opening_bypasses_every_child (nested : Parser TypeExpr)
    {input afterMarker : State} {marker : Token} {failure : Failure}
    (markerResult : contextual .mapping .typeExpr input = .ok marker afterMarker)
    (absent : TokenKindAbsentAt afterMarker.tokens afterMarker.window.endIndex afterMarker.cursor (.symbol .leftParen))
    (reported : RejectAtReports afterMarker.file.id afterMarker.window.endByte
      { head := .symbol .leftParen, tail := [] } .typeExpr afterMarker.declarativeRemainder failure.toDiagnostic) :
    parseMappingType nested input = .reject failure afterMarker := by
  rcases (symbol_reject_reports_iff .leftParen .typeExpr).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  simp only [parseMappingType, bind, markerResult, result]

theorem missing_closing_keeps_both_child_states_and_events (nested : Parser TypeExpr)
    {input afterMarker afterOpening afterKey afterArrow afterValue : State}
    {marker opening arrow : Token} {key value : TypeExpr} {failure : Failure}
    {keyEvents valueEvents : List ParseDiagnostic}
    (markerResult : contextual .mapping .typeExpr input = .ok marker afterMarker)
    (openingResult : symbol .leftParen .typeExpr afterMarker = .ok opening afterOpening)
    (keyResult : nested afterOpening = .ok key afterKey)
    (arrowResult : symbol .fatArrow .typeExpr afterKey = .ok arrow afterArrow)
    (valueResult : nested afterArrow = .ok value afterValue)
    (absent : TokenKindAbsentAt afterValue.tokens afterValue.window.endIndex afterValue.cursor (.symbol .rightParen))
    (reported : RejectAtReports afterValue.file.id afterValue.window.endByte
      { head := .symbol .rightParen, tail := [] } .typeExpr afterValue.declarativeRemainder failure.toDiagnostic)
    (keyEq : afterKey.diagnostics = input.diagnostics ++ keyEvents)
    (valueEq : afterValue.diagnostics = afterKey.diagnostics ++ valueEvents) :
    parseMappingType nested input = .reject failure afterValue ∧
      afterValue.diagnostics = input.diagnostics ++ keyEvents ++ valueEvents := by
  rcases (symbol_reject_reports_iff .rightParen .typeExpr).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  refine ⟨?_, by rw [valueEq, keyEq]⟩
  simp only [parseMappingType, bind, markerResult, openingResult, keyResult, arrowResult, valueResult, result]

variable
  {elementTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem successful_mapping_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {value : TypeExpr} {trace : List ParseDiagnostic}
    (parsed : MappingTypeTraceParses elementTrace source endByte input value output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters childProtected))

theorem rejected_mapping_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    (rejectedProtected : ∀ {input output report trace}, elementRejects source endByte input output report trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : MappingTypeTraceRejects elementTrace elementRejects source endByte input output report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (rejection.cascadeFilters childProtected rejectedProtected))

end Solcore.Test.SyntaxMappingTypeTraceProperties
