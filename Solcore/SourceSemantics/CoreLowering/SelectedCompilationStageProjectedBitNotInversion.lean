import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedSourceInversion
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsSourceInversion
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedTargetInversion

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedBitNotInversion
open Frontend SourceInference
open SelectedCompilationStageScopedLiftBounds SelectedCompilationStageForLiftBounds

variable {program : Program} {source : TypedSource}
  {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {assignment : AssignmentResolution}
  {size : Nat}
  {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

theorem statement_value (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    ∃ assignedSize updated, assignedSize < size ∧ finalContext = context ∧ outcome = .fallthrough environment ∧
      SourceExecutionSize.SourcePlaceSnapshotUpdate program assignedSize context evidence source
        Dynamic.BitNotSnapshot environment before assignment.target updated after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all
  refine ⟨_, ?_, _, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

theorem statement_fault (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    ∃ assignedSize, assignedSize < size ∧
      SourceExecutionSize.SourcePlaceBitNotFaults program assignedSize context evidence source environment
        before assignment.target reason after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals have same := sameNode (by assumption)
  all_goals subst_vars
  all_goals simp_all
  refine ⟨_, ?_, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

/-- Retain the genuine assignment derivation and independently measured suffix. -/
theorem child_and_tail {mode : Bool} {invocation : Staging.Recursive.Scope} {rest : List StatementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment)
    (trace : PlainStatements program mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ assignedSize reason, assignedSize < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      SourceExecutionSize.SourcePlaceBitNotFaults program assignedSize context invocation.evidence invocation.source
        environment before assignment.target reason after) ∨
    (∃ assignedSize tailSize updated written, assignedSize < size ∧ tailSize < size ∧
      SourceExecutionSize.SourcePlaceSnapshotUpdate program assignedSize context invocation.evidence invocation.source
        Dynamic.BitNotSnapshot environment before assignment.target updated written ∧
      PlainStatements program mode tailSize invocation context environment written rest finalContext outcome after) := by
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨_, reason, strict, equalContext, equalOutcome, failed⟩ | ⟨_, strict, stopped, head⟩ |
    ⟨_, tailSize, middleContext, nextEnvironment, middle, strict, tailStrict, head, tail⟩
  · obtain ⟨assignedSize, childStrict, failed⟩ := statement_fault unique found form failed
    exact .inl ⟨assignedSize, reason, Nat.lt_trans childStrict strict, equalContext, equalOutcome, failed⟩
  · obtain ⟨assignedSize, updated, childStrict, equalContext, equalOutcome, assigned⟩ :=
      statement_value unique found form head
    subst finalContext
    subst outcome
    rcases stopped with impossible | rfl
    · cases impossible
    · refine .inr ⟨assignedSize, SourceExecutionSize.stepSize [], updated, after,
        Nat.lt_trans childStrict strict, ?_, assigned, ?_⟩
      · simp only [SourceExecutionSize.stepSize, List.sum_nil]; omega
      · cases mode <;> exact .control .nil
  · obtain ⟨assignedSize, updated, childStrict, equalContext, equalOutcome, assigned⟩ :=
      statement_value unique found form head
    subst middleContext
    cases equalOutcome
    exact .inr ⟨assignedSize, tailSize, updated, middle,
      Nat.lt_trans childStrict strict, tailStrict, assigned, tail⟩

theorem item_value {nextEnvironment : Dynamic.Environment}
    (trace : SourceExecutionSize.ForItemExecutes program size context evidence source environment
      before (.assignBitNot assignment) finalContext nextEnvironment after) :
    ∃ assignedSize updated, assignedSize < size ∧ finalContext = context ∧ nextEnvironment = environment ∧
      SourceExecutionSize.SourcePlaceSnapshotUpdate program assignedSize context evidence source
        Dynamic.BitNotSnapshot environment before assignment.target updated after := by
  cases trace with
  | assignBitNot assigned => exact ⟨_, _, SourceExecutionSize.child_lt_stepSize (by simp), rfl, rfl, assigned⟩

theorem item_fault
    (trace : SourceExecutionSize.ForItemFaults program size context evidence source environment
      before (.assignBitNot assignment) reason after) :
    ∃ assignedSize, assignedSize < size ∧
      SourceExecutionSize.SourcePlaceBitNotFaults program assignedSize context evidence source environment
        before assignment.target reason after := by
  cases trace with
  | assignBitNot failed => exact ⟨_, SourceExecutionSize.child_lt_stepSize (by simp), failed⟩

theorem item_and_tail {invocation : Staging.Recursive.Scope} {rest : List ForItemForm}
    (trace : PlainItems program size invocation context environment before
      (.assignBitNot assignment :: rest) finalContext outcome after) :
    (∃ assignedSize reason, assignedSize < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      SourceExecutionSize.SourcePlaceBitNotFaults program assignedSize context invocation.evidence invocation.source
        environment before assignment.target reason after) ∨
    (∃ assignedSize tailSize updated written, assignedSize < size ∧ tailSize < size ∧
      SourceExecutionSize.SourcePlaceSnapshotUpdate program assignedSize context invocation.evidence invocation.source
        Dynamic.BitNotSnapshot environment before assignment.target updated written ∧
      PlainItems program tailSize invocation context environment written rest finalContext outcome after) := by
  cases trace with
  | done trace =>
      cases trace with
      | cons head tail =>
          obtain ⟨assignedSize, updated, strict, rfl, rfl, assigned⟩ := item_value head
          exact .inr ⟨assignedSize, _, updated, _,
            Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
            SourceExecutionSize.child_lt_stepSize (by simp), assigned, .done tail⟩
  | fault trace =>
      cases trace with
      | head failed =>
          obtain ⟨assignedSize, strict, failed⟩ := item_fault failed
          exact .inl ⟨assignedSize, _, Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)), rfl, rfl, failed⟩
      | tail head failed =>
          obtain ⟨assignedSize, updated, strict, rfl, rfl, assigned⟩ := item_value head
          exact .inr ⟨assignedSize, _, updated, _,
            Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
            SourceExecutionSize.child_lt_stepSize (by simp), assigned, .fault failed⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedBitNotInversion
