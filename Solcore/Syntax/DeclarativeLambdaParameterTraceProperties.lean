import Solcore.Syntax.DeclarativeLambdaParameterTraceGrammar
import Solcore.Syntax.DeclarativeLambdaParameterCoreTraceProperties
import Solcore.Syntax.DeclarativeLambdaParameterRecoveryTraceProperties

/-! Public lambda exactness compares the selected core and then the actual
rewound recovery remainder. Carrier preservation is not substituted implicitly.
The joint specification is uniqueness/disjointness, not existence. Core events
are protected, while committed reports and recovery events are filtered explicitly. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem LambdaParameterTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.LambdaParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : LambdaParameterTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : LambdaParameterTraceParses source endByte input right afterRight rightTrace) :
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

theorem LambdaParameterTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : LambdaParameterTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : LambdaParameterTraceRejects source endByte input afterRight rightReport rightTrace) :
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
          rcases LambdaParameterRecoveryTraceRejects.result_unique leftRecovery rightRecovery with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem LambdaParameterTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : LambdaParameterTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, LambdaParameterTraceParses source endByte input value output events := by
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
          exact LambdaParameterRecoveryTraceRejects.disjoint_success rejectedRecovery ⟨_, _, _, parsedRecovery⟩

theorem lambdaParameterTraceExactOutcomeSpec :
    TraceExactOutcomeSpec LambdaParameterTraceParses LambdaParameterTraceRejects source endByte where
  successResultUnique := LambdaParameterTraceParses.result_unique
  rejectResultUnique := LambdaParameterTraceRejects.result_unique
  successRejectDisjoint := LambdaParameterTraceRejects.disjoint_success

/-- The protected core prefix is preserved, but both cascade-candidate suffixes
need their own explicit filters. Their order and multiplicity are unchanged. -/
theorem lambdaParameterRecoveryTrace_cascadeFilters
    {input failed : Remainder} {coreReport : ParseDiagnostic} {coreTrace : List ParseDiagnostic}
    (coreRejected : LambdaParameterCoreTraceRejects source endByte input failed coreReport coreTrace)
    (text : String) (lexical : List SourceSpan)
    {recoveryTrace keptReport keptRecovery : List ParseDiagnostic}
    (reportFiltered : ParseDiagnosticCascadeFilters text lexical [coreReport] keptReport)
    (recoveryFiltered : ParseDiagnosticCascadeFilters text lexical recoveryTrace keptRecovery) :
    ParseDiagnosticCascadeFilters text lexical ((coreTrace ++ [coreReport]) ++ recoveryTrace)
      ((coreTrace ++ keptReport) ++ keptRecovery) :=
  ((coreRejected.cascadeFilters text lexical).append reportFiltered).append recoveryFiltered

end Solcore.Syntax.DeclarativeGrammar
