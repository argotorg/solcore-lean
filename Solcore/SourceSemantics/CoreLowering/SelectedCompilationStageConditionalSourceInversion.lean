import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedSourceInversion

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageConditionalSourceInversion
open Frontend SourceInference

/-- The ordinary conditional retains the chosen arm, restored outer context
and two strictly smaller traces. An absent else arm is the empty scoped body. -/
theorem control {program : Program} {source : TypedSource}
    {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {condition : ExpressionId}
    {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    {size : Nat} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source
      environment before id finalContext outcome after) :
    ∃ testSize branchSize truth middle innerContext innerOutcome,
      testSize < size ∧ branchSize < size ∧ finalContext = context ∧
      outcome = Dynamic.restoreControl environment innerOutcome ∧
      SourceExecutionSize.ExpressionEvaluates program testSize context evidence source environment before
        condition (.bool truth) middle ∧
      SourceExecutionSize.StatementsExecute program branchSize context evidence source environment middle
        (if truth then thenBody else elseBody.getD []) innerContext innerOutcome after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case ifTrue same test actual branch =>
    cases sameNode actual
    rw [form] at same
    cases same
    refine ⟨_, _, true, _, _, _, ?_, ?_, rfl, rfl, test, branch⟩
    · exact SourceExecutionSize.child_lt_stepSize (by simp)
    · exact SourceExecutionSize.child_lt_stepSize (by simp)
  case ifFalseWithElse same test actual branch =>
    cases sameNode actual
    rw [form] at same
    cases same
    refine ⟨_, _, false, _, _, _, ?_, ?_, rfl, rfl, test, branch⟩
    · exact SourceExecutionSize.child_lt_stepSize (by simp)
    · exact SourceExecutionSize.child_lt_stepSize (by simp)
  case ifFalseWithoutElse same actual test =>
    cases sameNode actual
    rw [form] at same
    cases same
    refine ⟨_, SourceExecutionSize.stepSize [], false, _, context, .fallthrough environment,
      ?_, ?_, rfl, rfl, test, ?_⟩
    · exact SourceExecutionSize.child_lt_stepSize (by simp)
    · have positive := test.positive
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega
    · exact .nil
  all_goals
    have same := sameNode (by assumption)
    subst_vars
    simp_all

/-- Ordinary faults distinguish failed conditions, non-Boolean values and
faults in the chosen arm. No typing premise hides one of these cases. -/
theorem fault {program : Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {condition : ExpressionId}
    {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    {size : Nat} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source
      environment before id reason after) :
    (∃ testSize, testSize < size ∧
      SourceExecutionSize.ExpressionFaults program testSize context evidence source environment before
        condition reason after) ∨
    (∃ testSize value actual, testSize < size ∧ reason = .typeMismatch .bool actual ∧
      SourceExecutionSize.ExpressionEvaluates program testSize context evidence source environment before
        condition value after ∧ ¬ Dynamic.BooleanValue value ∧ Dynamic.ValueRuntimeType value actual) ∨
    (∃ testSize branchSize truth middle innerContext,
      testSize < size ∧ branchSize < size ∧
      SourceExecutionSize.ExpressionEvaluates program testSize context evidence source environment before
        condition (.bool truth) middle ∧
      SourceExecutionSize.StatementsFault program branchSize context evidence source environment middle
        (if truth then thenBody else elseBody.getD []) innerContext reason after) := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  case ifCondition same actual failed =>
    cases sameNode actual
    rw [form] at same
    cases same
    exact .inl ⟨_, SourceExecutionSize.child_lt_stepSize (by simp), failed⟩
  case ifConditionType same nonboolean typed actual test =>
    cases sameNode actual
    rw [form] at same
    cases same
    exact .inr (.inl ⟨_, _, _, SourceExecutionSize.child_lt_stepSize (by simp), rfl, test, nonboolean, typed⟩)
  case ifTrueBody same test actual failed =>
    cases sameNode actual
    rw [form] at same
    cases same
    refine .inr (.inr ⟨_, _, true, _, _, ?_, ?_, test, failed⟩)
    · exact SourceExecutionSize.child_lt_stepSize (by simp)
    · exact SourceExecutionSize.child_lt_stepSize (by simp)
  case ifFalseBody same test actual failed =>
    cases sameNode actual
    rw [form] at same
    cases same
    refine .inr (.inr ⟨_, _, false, _, _, ?_, ?_, test, failed⟩)
    · exact SourceExecutionSize.child_lt_stepSize (by simp)
    · exact SourceExecutionSize.child_lt_stepSize (by simp)
  all_goals
    have same := sameNode (by assumption)
    subst_vars
    simp_all

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageConditionalSourceInversion
