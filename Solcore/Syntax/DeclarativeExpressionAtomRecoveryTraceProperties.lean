import Solcore.Syntax.DeclarativeExpressionAtomRecoveryTraceGrammar
import Solcore.Syntax.DeclarativeCoreExpressionAtomRecoveryExactnessProperties
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties
import Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties
import Solcore.Syntax.DeclarativeTraceOutcomeSpec

/-! Exact standalone recovery keeps its complete error AST, token remainder,
and singleton event distinct from the terminal report. The recovered event is
only conditionally kept or dropped by lexical cascade filtering. Independent
outcome exactness is not an existence claim about complete expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

private theorem scan_fields {first last : SourceSpan} {input output : Remainder} {value : Syntax.Expr}
    (parsed : ExpressionAtomRecoveryScanParses first last input value output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex ∧
      input.cursor ≤ output.cursor ∧ value.value = .error := by
  induction parsed with
  | stop => exact ⟨rfl, rfl, Nat.le_refl _, rfl⟩
  | next _ _ _ ih => exact ⟨ih.1, ih.2.1, Nat.le_trans (Nat.le_succ _) ih.2.2.1, ih.2.2.2⟩

theorem ExpressionAtomRecoveryTraceParses.ordinary
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ExpressionAtomRecoveryTraceParses source endByte input value output trace) :
    ExpressionAtomRecoveryParses input value output := parsed.1

theorem ExpressionAtomRecoveryTraceParses.error_value
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ExpressionAtomRecoveryTraceParses source endByte input value output trace) :
    value.value = .error := by
  cases parsed.1 with
  | recovered _ scan => exact (scan_fields scan).2.2.2

theorem ExpressionAtomRecoveryTraceParses.output_window
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ExpressionAtomRecoveryTraceParses source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed.1 with
  | recovered _ scan => exact ⟨(scan_fields scan).1, (scan_fields scan).2.1⟩

theorem ExpressionAtomRecoveryTraceParses.cursor_lt
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ExpressionAtomRecoveryTraceParses source endByte input value output trace) :
    input.cursor < output.cursor := by
  cases parsed.1 with
  | recovered _ scan => have progress := (scan_fields scan).2.2.1; exact progress

theorem ExpressionAtomRecoveryTraceParses.trace_eq
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ExpressionAtomRecoveryTraceParses source endByte input value output trace) :
    trace = [expressionAtomRecoveryTraceEvent value.span] := parsed.2

theorem ExpressionAtomRecoveryTraceRejects.ordinary
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionAtomRecoveryTraceRejects source endByte input rejected report trace) :
    ExpressionAtomRecoveryRejects input rejected := rejection.1

theorem ExpressionAtomRecoveryTraceRejects.output_eq
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionAtomRecoveryTraceRejects source endByte input rejected report trace) :
    rejected = input := rejection.1.output_eq

theorem ExpressionAtomRecoveryTraceRejects.trace_eq
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionAtomRecoveryTraceRejects source endByte input rejected report trace) : trace = [] :=
  rejection.2.2

theorem ExpressionAtomRecoveryTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ExpressionAtomRecoveryTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : ExpressionAtomRecoveryTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  have sameValue := leftParsed.1.value_unique rightParsed.1
  have sameOutput := leftParsed.1.output_unique rightParsed.1
  cases sameValue
  exact ⟨rfl, sameOutput, leftParsed.2.trans rightParsed.2.symm⟩

theorem ExpressionAtomRecoveryTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : ExpressionAtomRecoveryTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : ExpressionAtomRecoveryTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace :=
  ⟨leftRejected.1.output_eq.trans rightRejected.1.output_eq.symm,
    leftRejected.2.1.diagnostic_unique rightRejected.2.1, leftRejected.2.2.trans rightRejected.2.2.symm⟩

theorem ExpressionAtomRecoveryTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionAtomRecoveryTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, ExpressionAtomRecoveryTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  exact rejection.1.disjointParses ⟨value, output, parsed.1⟩

theorem ExpressionAtomRecoveryTraceParses.cascade_kept
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ExpressionAtomRecoveryTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan)
    (retained : ¬ LexicalCascadeSuppresses text lexical value.span) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  rw [parsed.2]
  exact .keep (fun suppressed => retained suppressed.2) .nil

theorem ExpressionAtomRecoveryTraceParses.cascade_dropped
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ExpressionAtomRecoveryTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan)
    (suppressed : LexicalCascadeSuppresses text lexical value.span) :
    ParseDiagnosticCascadeFilters text lexical trace [] := by
  rw [parsed.2]
  exact .drop ⟨by trivial, suppressed⟩ .nil

theorem ExpressionAtomRecoveryTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionAtomRecoveryTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  rw [rejection.2.2]
  exact .nil

theorem expressionAtomRecoveryTraceExactOutcomeSpec :
    TraceExactOutcomeSpec ExpressionAtomRecoveryTraceParses ExpressionAtomRecoveryTraceRejects source endByte where
  successResultUnique := ExpressionAtomRecoveryTraceParses.result_unique
  rejectResultUnique := ExpressionAtomRecoveryTraceRejects.result_unique
  successRejectDisjoint := ExpressionAtomRecoveryTraceRejects.disjoint_success

end Solcore.Syntax.DeclarativeGrammar
