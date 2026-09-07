import Solcore.Syntax.DeclarativeExpressionAtomTraceGrammar
import Solcore.Syntax.DeclarativeExpressionAtomRecoveryTraceProperties

/-! Conditional exactness first compares arbitrary core outcomes, then the
boundary or standalone recovery. Rewind never replaces a failed carrier with
the input carrier. Exactness gives uniqueness and disjointness, not existence.
All mixed trace components have explicit filtering premises: arbitrary core
events, committed reports, and recovery events are not uniformly protected. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {coreTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {coreRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem expressionAtomTraceRewind_fields (input failed : Remainder) :
    (expressionAtomTraceRewind input failed).tokens = failed.tokens ∧
    (expressionAtomTraceRewind input failed).endIndex = failed.endIndex ∧
    (expressionAtomTraceRewind input failed).cursor = input.cursor := ⟨rfl, rfl, rfl⟩

theorem expressionAtomTraceRewind_eq_input_of_carrier {input failed : Remainder}
    (tokens : failed.tokens = input.tokens) (endIndex : failed.endIndex = input.endIndex) :
    expressionAtomTraceRewind input failed = input := by
  cases input
  simp only [expressionAtomTraceRewind, tokens, endIndex]

theorem ExpressionAtomTraceParses.result_unique
    (core : TraceExactOutcomeSpec coreTrace coreRejects source endByte)
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ExpressionAtomTraceParses coreTrace coreRejects source endByte input left afterLeft leftTrace)
    (rightParsed : ExpressionAtomTraceParses coreTrace coreRejects source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore => exact core.successResultUnique leftCore rightCore
      | recovered rejected _ _ => exact False.elim (core.successRejectDisjoint rejected ⟨_, _, _, leftCore⟩)
  | recovered leftCore _ leftRecovery =>
      cases rightParsed with
      | core rightCore => exact False.elim (core.successRejectDisjoint leftCore ⟨_, _, _, rightCore⟩)
      | recovered rightCore _ rightRecovery =>
          rcases core.rejectResultUnique leftCore rightCore with ⟨rfl, rfl, rfl⟩
          rcases leftRecovery.result_unique rightRecovery with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ExpressionAtomTraceRejects.result_unique
    (core : TraceExactOutcomeSpec coreTrace coreRejects source endByte)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : ExpressionAtomTraceRejects coreRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : ExpressionAtomTraceRejects coreRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | boundary leftCore stops =>
      cases rightRejected with
      | boundary rightCore _ =>
          rcases core.rejectResultUnique leftCore rightCore with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩
      | recovery rightCore continues _ =>
          rcases core.rejectResultUnique leftCore rightCore with ⟨rfl, rfl, rfl⟩
          exact False.elim (continues stops)
  | recovery leftCore continues leftRecovery =>
      cases rightRejected with
      | boundary rightCore stops =>
          rcases core.rejectResultUnique leftCore rightCore with ⟨rfl, rfl, rfl⟩
          exact False.elim (continues stops)
      | recovery rightCore _ rightRecovery =>
          rcases core.rejectResultUnique leftCore rightCore with ⟨rfl, rfl, rfl⟩
          rcases leftRecovery.result_unique rightRecovery with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ExpressionAtomTraceRejects.disjoint_success
    (core : TraceExactOutcomeSpec coreTrace coreRejects source endByte)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionAtomTraceRejects coreRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, ExpressionAtomTraceParses coreTrace coreRejects source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases rejection with
  | boundary rejectedCore stops =>
      cases parsed with
      | core parsedCore => exact core.successRejectDisjoint rejectedCore ⟨_, _, _, parsedCore⟩
      | recovered otherCore continues _ =>
          rcases core.rejectResultUnique rejectedCore otherCore with ⟨rfl, rfl, rfl⟩
          exact continues stops
  | recovery rejectedCore _ rejectedRecovery =>
      cases parsed with
      | core parsedCore => exact core.successRejectDisjoint rejectedCore ⟨_, _, _, parsedCore⟩
      | recovered otherCore _ parsedRecovery =>
          rcases core.rejectResultUnique rejectedCore otherCore with ⟨rfl, rfl, rfl⟩
          exact rejectedRecovery.disjoint_success ⟨_, _, _, parsedRecovery⟩

theorem expressionAtomTraceExactOutcomeSpec
    (core : TraceExactOutcomeSpec coreTrace coreRejects source endByte) :
    TraceExactOutcomeSpec (ExpressionAtomTraceParses coreTrace coreRejects)
      (ExpressionAtomTraceRejects coreRejects) source endByte where
  successResultUnique := ExpressionAtomTraceParses.result_unique core
  rejectResultUnique := ExpressionAtomTraceRejects.result_unique core
  successRejectDisjoint := ExpressionAtomTraceRejects.disjoint_success core

/-- An unavailable mandatory token inside the public non-boundary branch is a
missing backing slot, never merely a window end. Its report is still terminal. -/
theorem expressionAtomRecoveryTraceRejects_missingToken_of_nonboundary
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (continues : ¬ ExpressionAtomBoundaryStops input)
    (rejection : ExpressionAtomRecoveryTraceRejects source endByte input rejected report trace) :
    rejected = input ∧ input.cursor < input.endIndex ∧ input.tokens[input.cursor]? = none ∧ trace = [] := by
  rcases rejection with ⟨recovery, _, traceEq⟩
  cases recovery with
  | windowEnd ended => exact False.elim (continues (.windowEnd ended))
  | missingToken inside missing => exact ⟨rfl, inside, missing, traceEq⟩

theorem expressionAtomRecoveryTrace_cascadeFilters
    (text : String) (lexical : List SourceSpan)
    {coreTrace recoveryTrace keptCore keptReport keptRecovery : List ParseDiagnostic} {coreReport : ParseDiagnostic}
    (coreFiltered : ParseDiagnosticCascadeFilters text lexical coreTrace keptCore)
    (reportFiltered : ParseDiagnosticCascadeFilters text lexical [coreReport] keptReport)
    (recoveryFiltered : ParseDiagnosticCascadeFilters text lexical recoveryTrace keptRecovery) :
    ParseDiagnosticCascadeFilters text lexical ((coreTrace ++ [coreReport]) ++ recoveryTrace)
      ((keptCore ++ keptReport) ++ keptRecovery) :=
  (coreFiltered.append reportFiltered).append recoveryFiltered

end Solcore.Syntax.DeclarativeGrammar
