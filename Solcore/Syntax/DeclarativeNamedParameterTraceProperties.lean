import Solcore.Syntax.DeclarativeNamedParameterTraceGrammar
import Solcore.Syntax.DeclarativeNamedParameterCoreTraceProperties
import Solcore.Syntax.DeclarativeParameterRecoveryTraceProperties

/-! Public exactness compares the core first, then the boundary or standalone
recovery. No carrier frame is silently substituted for the actual rewind.
Committed unexpected reports and recovered events may be cascade-suppressed,
so only explicit component filtering is composed for mixed recovery traces. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem parameterTraceRewind_fields (input failed : Remainder) :
    (parameterTraceRewind input failed).tokens = failed.tokens ∧
    (parameterTraceRewind input failed).endIndex = failed.endIndex ∧
    (parameterTraceRewind input failed).cursor = input.cursor := ⟨rfl, rfl, rfl⟩

theorem parameterTraceRewind_eq_input_of_carrier {input failed : Remainder}
    (tokens : failed.tokens = input.tokens) (endIndex : failed.endIndex = input.endIndex) :
    parameterTraceRewind input failed = input := by
  cases input
  simp only [parameterTraceRewind, tokens, endIndex]

theorem NamedParameterTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.FunctionParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : NamedParameterTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : NamedParameterTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore => exact leftCore.result_unique rightCore
      | recovered rejected _ _ => exact False.elim (rejected.disjoint_success ⟨_, _, _, leftCore⟩)
  | recovered leftCore _ leftRecovery =>
      cases rightParsed with
      | core rightCore => exact False.elim (leftCore.disjoint_success ⟨_, _, _, rightCore⟩)
      | recovered rightCore _ rightRecovery =>
          rcases leftCore.result_unique rightCore with ⟨rfl, rfl, rfl⟩
          rcases leftRecovery.result_unique rightRecovery with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem NamedParameterTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : NamedParameterTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : NamedParameterTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | boundary leftCore stops =>
      cases rightRejected with
      | boundary rightCore _ =>
          rcases leftCore.result_unique rightCore with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩
      | recovery rightCore continues _ =>
          rcases leftCore.result_unique rightCore with ⟨rfl, rfl, rfl⟩
          exact False.elim (continues stops)
  | recovery leftCore continues leftRecovery =>
      cases rightRejected with
      | boundary rightCore stops =>
          rcases leftCore.result_unique rightCore with ⟨rfl, rfl, rfl⟩
          exact False.elim (continues stops)
      | recovery rightCore _ rightRecovery =>
          rcases leftCore.result_unique rightCore with ⟨rfl, rfl, rfl⟩
          rcases leftRecovery.result_unique rightRecovery with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem NamedParameterTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedParameterTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, NamedParameterTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases rejection with
  | boundary rejectedCore stops =>
      cases parsed with
      | core parsedCore => exact rejectedCore.disjoint_success ⟨_, _, _, parsedCore⟩
      | recovered otherCore continues _ =>
          rcases rejectedCore.result_unique otherCore with ⟨rfl, rfl, rfl⟩
          exact continues stops
  | recovery rejectedCore _ rejectedRecovery =>
      cases parsed with
      | core parsedCore => exact rejectedCore.disjoint_success ⟨_, _, _, parsedCore⟩
      | recovered otherCore _ parsedRecovery =>
          rcases rejectedCore.result_unique otherCore with ⟨rfl, rfl, rfl⟩
          exact rejectedRecovery.disjoint_success ⟨_, _, _, parsedRecovery⟩

theorem namedParameterTraceExactOutcomeSpec :
    TraceExactOutcomeSpec NamedParameterTraceParses NamedParameterTraceRejects source endByte where
  successResultUnique := NamedParameterTraceParses.result_unique
  rejectResultUnique := NamedParameterTraceRejects.result_unique
  successRejectDisjoint := NamedParameterTraceRejects.disjoint_success

/-- Inside the non-boundary branch, a failed mandatory recovery token is
necessarily absent from the backing carrier. The new report is not emitted. -/
theorem functionParameterRecoveryTraceRejects_missingToken_of_nonboundary
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (continues : ¬ FunctionParameterBoundaryStops input)
    (rejection : FunctionParameterRecoveryTraceRejects source endByte input rejected report trace) :
    rejected = input ∧ input.cursor < input.endIndex ∧ input.tokens[input.cursor]? = none ∧ trace = [] := by
  rcases rejection with ⟨recovery, _, traceEq⟩
  cases recovery with
  | windowEnd ended => exact False.elim (continues (.windowEnd ended))
  | missingToken inside missing => exact ⟨rfl, inside, missing, traceEq⟩

/-- The core suffix is protected, but the committed report and subsequent
recovery events are filtered explicitly, preserving order and multiplicity. -/
theorem namedParameterRecoveryTrace_cascadeFilters
    {input failed : Remainder} {coreReport : ParseDiagnostic} {coreTrace : List ParseDiagnostic}
    (coreRejected : NamedParameterCoreTraceRejects source endByte input failed coreReport coreTrace)
    (text : String) (lexical : List SourceSpan)
    {recoveryTrace keptReport keptRecovery : List ParseDiagnostic}
    (reportFiltered : ParseDiagnosticCascadeFilters text lexical [coreReport] keptReport)
    (recoveryFiltered : ParseDiagnosticCascadeFilters text lexical recoveryTrace keptRecovery) :
    ParseDiagnosticCascadeFilters text lexical ((coreTrace ++ [coreReport]) ++ recoveryTrace)
      ((coreTrace ++ keptReport) ++ keptRecovery) :=
  ((coreRejected.cascadeFilters text lexical).append reportFiltered).append recoveryFiltered

end Solcore.Syntax.DeclarativeGrammar
