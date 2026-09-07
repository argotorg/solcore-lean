import Solcore.Syntax.DeclarativeLambdaParameterRecoveryTraceGrammar
import Solcore.Syntax.DeclarativeParameterRecoveryTraceProperties

/-! Standalone lambda recovery has exact error values, remainders, reports,
and event suffixes. Its recovered event is conditionally retained or dropped,
not unconditionally protected against lexical cascade suppression. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem LambdaParameterRecoveryTraceParses.ordinary
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : LambdaParameterRecoveryTraceParses source endByte input value output trace) :
    LambdaParameterRecoveryParses input value output := by
  cases parsed with
  | recovered recovery => exact .recovered recovery.1

theorem LambdaParameterRecoveryTraceParses.error_value
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : LambdaParameterRecoveryTraceParses source endByte input value output trace) :
    value.value = .error := by cases parsed; rfl

theorem LambdaParameterRecoveryTraceParses.trace_eq
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : LambdaParameterRecoveryTraceParses source endByte input value output trace) :
    trace = [parameterRecoveryTraceEvent value.span] := by
  cases parsed with
  | recovered recovery => exact recovery.2

theorem LambdaParameterRecoveryTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.LambdaParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : LambdaParameterRecoveryTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : LambdaParameterRecoveryTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | recovered leftRecovery =>
      cases rightParsed with
      | recovered rightRecovery =>
          rcases leftRecovery.result_unique rightRecovery with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem LambdaParameterRecoveryTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : LambdaParameterRecoveryTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : LambdaParameterRecoveryTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace :=
  FunctionParameterRecoveryTraceRejects.result_unique leftRejected rightRejected

theorem LambdaParameterRecoveryTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : LambdaParameterRecoveryTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, LambdaParameterRecoveryTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed with
  | recovered recovery => exact FunctionParameterRecoveryTraceRejects.disjoint_success rejection ⟨_, _, _, recovery⟩

theorem LambdaParameterRecoveryTraceParses.cascade_kept
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : LambdaParameterRecoveryTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan)
    (retained : ¬ LexicalCascadeSuppresses text lexical value.span) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | recovered recovery => exact recovery.cascade_kept text lexical retained

theorem LambdaParameterRecoveryTraceParses.cascade_dropped
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : LambdaParameterRecoveryTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan)
    (suppressed : LexicalCascadeSuppresses text lexical value.span) :
    ParseDiagnosticCascadeFilters text lexical trace [] := by
  cases parsed with
  | recovered recovery => exact recovery.cascade_dropped text lexical suppressed

theorem LambdaParameterRecoveryTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : LambdaParameterRecoveryTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace :=
  FunctionParameterRecoveryTraceRejects.cascadeFilters rejection text lexical

theorem lambdaParameterRecoveryTraceExactOutcomeSpec :
    TraceExactOutcomeSpec LambdaParameterRecoveryTraceParses LambdaParameterRecoveryTraceRejects source endByte where
  successResultUnique := LambdaParameterRecoveryTraceParses.result_unique
  rejectResultUnique := LambdaParameterRecoveryTraceRejects.result_unique
  successRejectDisjoint := LambdaParameterRecoveryTraceRejects.disjoint_success

end Solcore.Syntax.DeclarativeGrammar
