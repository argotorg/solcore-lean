import Solcore.Syntax.DeclarativeTypeDispatchTraceGrammar
import Solcore.Syntax.DeclarativeTypeDispatchSelectionProperties
import Solcore.Syntax.DeclarativeTraceOutcomeSpec
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties

/-! Selection uniqueness lifts exact raw outcomes to the prioritized layer.
These laws establish uniqueness and disjointness only, not outcome existence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem TypeDispatchFinalTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : TypeDispatchFinalTraceRejects source endByte input afterLeft leftReport leftTrace)
    (right : TypeDispatchFinalTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | rejected report =>
      cases right with
      | rejected other => exact ⟨rfl, report.diagnostic_unique other, rfl⟩

theorem TypeDispatchTraceParses.raw_of_selected
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    {branch : TypeDispatchBranch} (selection : TypeDispatchSelects input branch)
    (parsed : TypeDispatchTraceParses elementTrace source endByte input value output trace) :
    TypeDispatchRawTraceParses elementTrace branch source endByte input value output trace := by
  cases parsed with
  | selected actual actualSelection raw =>
      cases selection.branch_unique actualSelection
      exact raw

theorem TypeDispatchTraceRejects.raw_of_selected
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    {branch : TypeDispatchBranch} (selection : TypeDispatchSelects input branch)
    (rejection : TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    TypeDispatchRawTraceRejects elementTrace elementRejects branch source endByte input rejected report trace := by
  cases rejection with
  | selected actual actualSelection raw =>
      cases selection.branch_unique actualSelection
      exact raw

theorem TypeDispatchTraceParses.not_final
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (selection : TypeDispatchSelects input .final)
    (parsed : TypeDispatchTraceParses elementTrace source endByte input value output trace) : False :=
  parsed.raw_of_selected selection

theorem TypeDispatchTraceRejects.final_iff
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (selection : TypeDispatchSelects input .final) :
    TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace ↔
      rejected = input ∧
      RejectAtReports source endByte { head := .typeExpr, tail := [] } .typeExpr input report ∧ trace = [] := by
  constructor
  · intro rejection
    have raw := rejection.raw_of_selected selection
    cases raw with
    | rejected reported => exact ⟨rfl, reported, rfl⟩
  · rintro ⟨rfl, reported, rfl⟩
    exact .selected .final selection (.rejected reported)

variable (rawExact : ∀ branch,
  TraceExactOutcomeSpec (TypeDispatchRawTraceParses elementTrace branch)
    (TypeDispatchRawTraceRejects elementTrace elementRejects branch) source endByte)

include rawExact

theorem TypeDispatchTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.TypeExpr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : TypeDispatchTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : TypeDispatchTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | selected branch selection raw =>
      exact (rawExact branch).successResultUnique raw (rightParsed.raw_of_selected selection)

theorem TypeDispatchTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : TypeDispatchTraceRejects elementTrace elementRejects source endByte input afterLeft leftReport leftTrace)
    (right : TypeDispatchTraceRejects elementTrace elementRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | selected branch selection raw =>
      exact (rawExact branch).rejectResultUnique raw (right.raw_of_selected selection)

theorem TypeDispatchTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, TypeDispatchTraceParses elementTrace source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases rejection with
  | selected branch selection raw =>
      exact (rawExact branch).successRejectDisjoint raw ⟨value, output, events, parsed.raw_of_selected selection⟩

theorem typeDispatchTraceExactOutcomeSpec_of_raw :
    TraceExactOutcomeSpec (TypeDispatchTraceParses elementTrace)
      (TypeDispatchTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := TypeDispatchTraceParses.result_unique rawExact
  rejectResultUnique := TypeDispatchTraceRejects.result_unique rawExact
  successRejectDisjoint := TypeDispatchTraceRejects.disjoint_success rawExact

end Solcore.Syntax.DeclarativeGrammar
