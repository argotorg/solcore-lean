import Solcore.Syntax.DeclarativeParameterRecoveryTraceGrammar
import Solcore.Syntax.DeclarativeFunctionParameterRecoveryExactnessProperties
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties
import Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties
import Solcore.Syntax.DeclarativeTraceOutcomeSpec

/-! Exact standalone recovery values, remainders, reports, and event suffixes.
Earlier committed reports belong to the caller, not to this one-event scan.
The joint specification asserts uniqueness and disjointness, not existence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem FunctionParameterRecoveryTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.FunctionParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : FunctionParameterRecoveryTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : FunctionParameterRecoveryTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  rcases leftParsed.1.result_unique rightParsed.1 with ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, leftParsed.2.trans rightParsed.2.symm⟩

theorem FunctionParameterRecoveryTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : FunctionParameterRecoveryTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : FunctionParameterRecoveryTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace :=
  ⟨leftRejected.1.output_unique rightRejected.1,
    leftRejected.2.1.diagnostic_unique rightRejected.2.1, leftRejected.2.2.trans rightRejected.2.2.symm⟩

theorem FunctionParameterRecoveryTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionParameterRecoveryTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, FunctionParameterRecoveryTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  exact rejection.1.disjointParses ⟨value, output, parsed.1⟩

theorem FunctionParameterRecoveryTraceParses.cascade_kept
    {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
    (parsed : FunctionParameterRecoveryTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan)
    (retained : ¬ LexicalCascadeSuppresses text lexical value.span) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  rw [parsed.2]
  exact .keep (fun suppressed => retained suppressed.2) .nil

theorem FunctionParameterRecoveryTraceParses.cascade_dropped
    {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
    (parsed : FunctionParameterRecoveryTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan)
    (suppressed : LexicalCascadeSuppresses text lexical value.span) :
    ParseDiagnosticCascadeFilters text lexical trace [] := by
  rw [parsed.2]
  exact .drop ⟨by trivial, suppressed⟩ .nil

theorem FunctionParameterRecoveryTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionParameterRecoveryTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  rw [rejection.2.2]
  exact .nil

theorem functionParameterRecoveryTraceExactOutcomeSpec :
    TraceExactOutcomeSpec FunctionParameterRecoveryTraceParses FunctionParameterRecoveryTraceRejects source endByte where
  successResultUnique := FunctionParameterRecoveryTraceParses.result_unique
  rejectResultUnique := FunctionParameterRecoveryTraceRejects.result_unique
  successRejectDisjoint := FunctionParameterRecoveryTraceRejects.disjoint_success

end Solcore.Syntax.DeclarativeGrammar
