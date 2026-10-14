import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedSourceInversion

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchSourceInversion
open Frontend SourceInference
open Solcore.SourceSemantics.Dynamic
open SelectedCompilationStageScopedLiftBounds

/-- A view of the actual ordinary match trace, including allocated hidden and
pattern cells. Every child keeps its original execution grade. -/
inductive PlainMatch (program : Program) : Nat →
      Staging.Recursive.Scope → Context → Dynamic.Environment → Dynamic.Heap → MatchResolution → Dynamic.ControlOutcome → Dynamic.Heap → Prop where
    | scrutineeFault {size : Nat} {scope context environment before after resolution failure}
        (scrutinee : SourceExecutionSize.ExpressionFaults program size context scope.evidence scope.source environment before resolution.scrutinee failure after) :
        PlainMatch program (SourceExecutionSize.stepSize [size]) scope context environment before resolution (.fault failure) after
    | patternFault {size : Nat} {scope context environment before middle hidden resolution node value location}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before resolution.scrutinee value middle)
        (allocated : Heap.Allocates middle node.type (some value) location hidden)
        (invalid : MatchCasesPatternFault context value resolution.cases) :
        PlainMatch program (SourceExecutionSize.stepSize [size]) scope context environment before resolution (.fault .invalidPattern) hidden
    | arm {size bodySize : Nat} {scope context armContext finalContext environment armEnvironment before middle hidden bound after
          resolution node value location statements bindings outcome}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before resolution.scrutinee value middle)
        (hiddenAllocated : Heap.Allocates middle node.type (some value) location hidden)
        (selected : MatchCasesSelect context value resolution.cases resolution.defaultBody (.arm statements bindings))
        (extended : BindersExtend scope.source.owner context (bindings.map Prod.fst) armContext)
        (allocated : BindersAllocate environment hidden (bindings.map Prod.fst) (bindings.map Prod.snd) armEnvironment bound)
        (body : PlainStatements program false bodySize scope armContext armEnvironment bound statements finalContext outcome after) :
        PlainMatch program (SourceExecutionSize.stepSize [size, bodySize]) scope context environment before resolution (Dynamic.restoreControl environment outcome) after
    | default {size bodySize : Nat} {scope context finalContext environment before middle hidden after resolution node value location statements outcome}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before resolution.scrutinee value middle)
        (hiddenAllocated : Heap.Allocates middle node.type (some value) location hidden)
        (selected : MatchCasesSelect context value resolution.cases resolution.defaultBody (.default statements))
        (body : PlainStatements program false bodySize scope context environment hidden statements finalContext outcome after) :
        PlainMatch program (SourceExecutionSize.stepSize [size, bodySize]) scope context environment before resolution (Dynamic.restoreControl environment outcome) after
    | noBranch {size : Nat} {scope context environment before middle hidden resolution node value location}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before resolution.scrutinee value middle)
        (hiddenAllocated : Heap.Allocates middle node.type (some value) location hidden)
        (selected : MatchCasesSelect context value resolution.cases resolution.defaultBody .noBranch) :
        PlainMatch program (SourceExecutionSize.stepSize [size]) scope context environment before resolution (.fallthrough environment) hidden



/-- Ordinary completion restores the outer context after the selected arm. -/
theorem control
    {program : Program} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode}
    {resolution : MatchResolution} {size : Nat}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.StatementExecutes program size context invocation.evidence invocation.source
      environment before id finalContext outcome after) :
    finalContext = context ∧ PlainMatch program size invocation context environment before resolution outcome after := by
  have sameNode : ∀ {other}, ContainsStatement invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case matchArm same contains evaluated hidden selected bindersEq valuesEq extended allocated actual body =>
    cases sameNode actual
    rw [form] at same
    cases same
    subst_vars
    exact ⟨rfl, .arm (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (.control (by assumption))⟩
  case matchDefault same contains evaluated hidden selected actual body =>
    cases sameNode actual
    rw [form] at same
    cases same
    exact ⟨rfl, .default (by assumption) (by assumption) (by assumption) (by assumption) (.control (by assumption))⟩
  case matchNoBranch same contains evaluated hidden actual selected =>
    cases sameNode actual
    rw [form] at same
    cases same
    exact ⟨rfl, .noBranch (by assumption) (by assumption) (by assumption) (by assumption)⟩
  all_goals
    have same := sameNode (by assumption)
    subst_vars
    simp_all

/-- Ordinary failure retains scrutinee, pattern and selected-body failures. -/
theorem fault
    {program : Program} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode}
    {resolution : MatchResolution} {size : Nat}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.StatementFaults program size context invocation.evidence invocation.source
      environment before id reason after) :
    PlainMatch program size invocation context environment before resolution (.fault reason) after := by
  have sameNode : ∀ {other}, ContainsStatement invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  case matchScrutinee same actual failed =>
    cases sameNode actual
    rw [form] at same
    cases same
    exact .scrutineeFault failed
  case matchPattern same contains evaluated hidden actual failed =>
    cases sameNode actual
    rw [form] at same
    cases same
    exact .patternFault (by assumption) (by assumption) (by assumption) (by assumption)
  case matchArmBody same contains evaluated hidden selected bindersEq valuesEq extended allocated actual body =>
    cases sameNode actual
    rw [form] at same
    cases same
    subst_vars
    exact .arm (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (.fault (by assumption))
  case matchDefaultBody same contains evaluated hidden selected actual body =>
    cases sameNode actual
    rw [form] at same
    cases same
    exact .default (by assumption) (by assumption) (by assumption) (by assumption) (.fault (by assumption))
  all_goals
    have same := sameNode (by assumption)
    subst_vars
    simp_all

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchSourceInversion
