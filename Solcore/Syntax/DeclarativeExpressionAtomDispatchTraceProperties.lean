import Solcore.Syntax.DeclarativeExpressionAtomDispatchTraceGrammar
import Solcore.Syntax.DeclarativeExpressionAtomDispatchSelectionProperties
import Solcore.Syntax.DeclarativeLiteralExpressionTraceExactnessProperties
import Solcore.Syntax.DeclarativeExpressionNameTraceProperties
import Solcore.Syntax.DeclarativeDotConstructorTraceOutcomeProperties
import Solcore.Syntax.DeclarativeParenthesizedTraceOutcomeProperties
import Solcore.Syntax.DeclarativeArrayLiteralTraceProperties
import Solcore.Syntax.DeclarativeProxyExpressionRejectionTraceProperties
import Solcore.Syntax.DeclarativeLambdaExpressionTraceProperties

/-! Concrete raw leaf/type exactness and explicit nested-expression/block
exactness lift through one prioritized atom layer. Values, full remainders,
terminal reports, and ordered event sequences are preserved. Neither child
existence nor recursive expression execution follows from this joint bundle. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {blockTrace : SourceId → Nat → Remainder → Syntax.Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem ExpressionAtomDispatchFinalTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : ExpressionAtomDispatchFinalTraceRejects source endByte input afterLeft leftReport leftTrace)
    (right : ExpressionAtomDispatchFinalTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | rejected report =>
      cases right with
      | rejected other => exact ⟨rfl, report.diagnostic_unique other, rfl⟩

theorem ExpressionAtomDispatchTraceParses.raw_of_selected
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    {branch : ExpressionAtomDispatchBranch} (selection : ExpressionAtomDispatchSelects input branch)
    (parsed : ExpressionAtomDispatchTraceParses nestedTrace blockTrace source endByte input value output trace) :
    ExpressionAtomDispatchRawTraceParses nestedTrace blockTrace branch source endByte input value output trace := by
  cases parsed with
  | selected actual actualSelection raw =>
      cases selection.branch_unique actualSelection
      exact raw

theorem ExpressionAtomDispatchTraceRejects.raw_of_selected
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    {branch : ExpressionAtomDispatchBranch} (selection : ExpressionAtomDispatchSelects input branch)
    (rejection : ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects
      source endByte input rejected report trace) :
    ExpressionAtomDispatchRawTraceRejects nestedTrace nestedRejects blockRejects branch
      source endByte input rejected report trace := by
  cases rejection with
  | selected actual actualSelection raw =>
      cases selection.branch_unique actualSelection
      exact raw

theorem ExpressionAtomDispatchTraceParses.not_final
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (selection : ExpressionAtomDispatchSelects input .final)
    (parsed : ExpressionAtomDispatchTraceParses nestedTrace blockTrace source endByte input value output trace) : False :=
  parsed.raw_of_selected selection

theorem ExpressionAtomDispatchTraceRejects.final_iff
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (selection : ExpressionAtomDispatchSelects input .final) :
    ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects source endByte input rejected report trace ↔
      rejected = input ∧
      RejectAtReports source endByte { head := .expression, tail := [] } .expression input report ∧ trace = [] := by
  constructor
  · intro rejection
    have raw := rejection.raw_of_selected selection
    cases raw with
    | rejected reported => exact ⟨rfl, reported, rfl⟩
  · rintro ⟨rfl, reported, rfl⟩
    exact .selected .final selection (.rejected reported)

/-- Raw forms need only independent nested/body uniqueness and disjointness.
All literal, name, type, parameter, and return-type laws are concrete. -/
theorem expressionAtomDispatchRawTraceExactOutcomeSpec
    (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
    (blocks : TraceExactOutcomeSpec blockTrace blockRejects source endByte)
    (branch : ExpressionAtomDispatchBranch) :
    TraceExactOutcomeSpec (ExpressionAtomDispatchRawTraceParses nestedTrace blockTrace branch)
      (ExpressionAtomDispatchRawTraceRejects nestedTrace nestedRejects blockRejects branch) source endByte := by
  cases branch with
  | literal => exact (literalExpressionTraceExactOutcomeSpec source endByte).toTraceExactOutcomeSpec
  | name => exact (identifierExpressionTrace_exactOutcomeSpec source endByte).toTraceExactOutcomeSpec
  | dotConstructor => exact (dotConstructorTraceExactOutcomeSpec nested.toExpressionTraceExactOutcomeSpec).toTraceExactOutcomeSpec
  | proxy => exact (proxyExpressionTraceExactOutcomeSpec typeExprTraceExactOutcomeSpec).toTraceExactOutcomeSpec
  | parenthesized => exact (parenthesizedTraceExactOutcomeSpec nested.toExpressionTraceExactOutcomeSpec).toTraceExactOutcomeSpec
  | array => exact (arrayLiteralTraceExactOutcomeSpec nested.toExpressionTraceExactOutcomeSpec).toTraceExactOutcomeSpec
  | lambda => exact lambdaExpressionTraceExactOutcomeSpec blocks
  | final =>
      refine {
        successResultUnique := ?_
        rejectResultUnique := ExpressionAtomDispatchFinalTraceRejects.result_unique
        successRejectDisjoint := ?_ }
      · intro _ _ _ _ _ _ _ impossible _
        exact False.elim impossible
      · rintro _ _ _ _ _ ⟨_, _, _, impossible⟩
        exact impossible

variable (nested : TraceExactOutcomeSpec nestedTrace nestedRejects source endByte)
  (blocks : TraceExactOutcomeSpec blockTrace blockRejects source endByte)

include nested blocks

theorem ExpressionAtomDispatchTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.Expr} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ExpressionAtomDispatchTraceParses nestedTrace blockTrace source endByte input left afterLeft leftTrace)
    (rightParsed : ExpressionAtomDispatchTraceParses nestedTrace blockTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | selected branch selection raw =>
      exact (expressionAtomDispatchRawTraceExactOutcomeSpec nested blocks branch).successResultUnique
        raw (rightParsed.raw_of_selected selection)

theorem ExpressionAtomDispatchTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects
      source endByte input afterLeft leftReport leftTrace)
    (right : ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects
      source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | selected branch selection raw =>
      exact (expressionAtomDispatchRawTraceExactOutcomeSpec nested blocks branch).rejectResultUnique
        raw (right.raw_of_selected selection)

theorem ExpressionAtomDispatchTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects
      source endByte input rejected report trace) :
    ¬ ∃ value output events, ExpressionAtomDispatchTraceParses nestedTrace blockTrace source endByte
      input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases rejection with
  | selected branch selection raw =>
      exact (expressionAtomDispatchRawTraceExactOutcomeSpec nested blocks branch).successRejectDisjoint
        raw ⟨value, output, events, parsed.raw_of_selected selection⟩

theorem expressionAtomDispatchTraceExactOutcomeSpec :
    TraceExactOutcomeSpec (ExpressionAtomDispatchTraceParses nestedTrace blockTrace)
      (ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects) source endByte where
  successResultUnique := ExpressionAtomDispatchTraceParses.result_unique nested blocks
  rejectResultUnique := ExpressionAtomDispatchTraceRejects.result_unique nested blocks
  successRejectDisjoint := ExpressionAtomDispatchTraceRejects.disjoint_success nested blocks

end Solcore.Syntax.DeclarativeGrammar
