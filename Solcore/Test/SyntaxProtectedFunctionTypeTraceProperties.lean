import Solcore.Syntax.DeclarativeFunctionTypeRejectionTraceProperties
import Solcore.Syntax.Parser.FunctionTypeRejectionTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Raw function types preserve absent-return states and parameter end spans.
Protected parameter/return suffixes retain duplicates and order, excluding the
separate terminal report on rejection. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedFunctionTypeTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.TypeFunctionInternals

theorem missing_keyword_bypasses_every_child (nested : Parser TypeExpr)
    {input : State} {failure : Failure}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.keyword .functionKw))
    (reported : RejectAtReports input.file.id input.window.endByte
      { head := .keyword .functionKw, tail := [] } .typeExpr input.declarativeRemainder failure.toDiagnostic) :
    parseFunctionType nested input = .reject failure input := by
  rcases (keyword_reject_reports_iff .functionKw .typeExpr).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  exact parseFunctionType_reject_iff_components.mpr (.inl result)

theorem absent_returns_keeps_parameter_span_and_state (nested : Parser TypeExpr)
    {input afterKeyword afterParameters : State} {marker : Token} {parameters : DelimitedList TypeExpr}
    (keywordResult : keyword .functionKw .typeExpr input = .ok marker afterKeyword)
    (parameterResult : delimited .leftParen .rightParen true nested .typeExpr .typeExpr afterKeyword =
      .ok parameters afterParameters)
    (absent : TokenKindAbsentAt afterParameters.tokens afterParameters.window.endIndex afterParameters.cursor
      (.identifier ContextualKeyword.returns.spelling)) :
    parseFunctionType nested input = .ok {
      span := SourceSpan.cover marker.span parameters.span
      value := .function marker.span parameters none
    } afterParameters :=
  parseFunctionType_success_iff_components.mpr
    ⟨_, _, _, _, _, keywordResult, parameterResult, parseFunctionReturns_eq_none_of_absent nested absent, rfl⟩

variable
  {elementTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem success_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {value : TypeExpr} {trace : List ParseDiagnostic}
    (parsed : FunctionTypeTraceParses elementTrace source endByte input value output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters childProtected))

theorem rejection_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (successProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    (rejectProtected : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (rejection.cascadeFilters successProtected rejectProtected))

end Solcore.Test.SyntaxProtectedFunctionTypeTraceProperties
