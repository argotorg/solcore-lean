import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedSourceInversion
import Solcore.SourceSemantics.Staging.RecursiveBareBitNotFacts

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBitNotInversion
open Frontend SourceInference
open SelectedCompilationStageScopedLiftBounds
open Staging.Recursive (BareTarget)

variable {program : Program} {source : TypedSource}
  {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {assignment : AssignmentResolution}
  {size : Nat} {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

private theorem statement_value (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
    (bare : assignment.target.projections = [])
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment
      before id finalContext outcome after) :
    ∃ target updated, finalContext = context ∧ outcome = .fallthrough environment ∧
      BareTarget environment before assignment.target target ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        before target updated after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all
  rename_i executed
  obtain ⟨target, snapshot, written⟩ := Staging.Recursive.bitNot_update_iff bare |>.mp executed.sound
  exact ⟨target, snapshot, _, written⟩

private theorem statement_fault (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
    (bare : assignment.target.projections = [])
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment
      before id reason after) :
    after = before ∧ Dynamic.SourcePlaceBitNotFaults program context evidence source environment
      before assignment.target reason before := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals have same := sameNode (by assumption)
  all_goals subst_vars
  all_goals simp_all
  rename_i failed
  exact Staging.Recursive.bitNot_fault_iff bare |>.mp failed.sound

/-- The ordinary bare unary head either fails without changing its incoming
heap, or writes and reaches its strictly smaller suffix. -/
theorem write_and_tail {mode : Bool} {invocation : Staging.Recursive.Scope} {rest : List StatementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment)
    (bare : assignment.target.projections = [])
    (trace : PlainStatements program mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ reason, finalContext = context ∧ outcome = .fault reason ∧ after = before ∧
      Dynamic.SourcePlaceBitNotFaults program context invocation.evidence invocation.source environment
        before assignment.target reason before) ∨
    (∃ tailSize target updated written, tailSize < size ∧
      BareTarget environment before assignment.target target ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        before target updated written ∧
      PlainStatements program mode tailSize invocation context environment written rest finalContext outcome after) := by
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨_, reason, _strict, equalContext, equalOutcome, failed⟩ | ⟨_, strict, stopped, head⟩ |
    ⟨_, tailSize, middleContext, nextEnvironment, middle, _strict, tailStrict, head, tail⟩
  · obtain ⟨sameHeap, failed⟩ := statement_fault unique found form bare failed
    exact .inl ⟨reason, equalContext, equalOutcome, sameHeap, failed⟩
  · obtain ⟨target, updated, equalContext, equalOutcome, snapshot, written⟩ :=
      statement_value unique found form bare head
    subst finalContext
    subst outcome
    rcases stopped with impossible | rfl
    · cases impossible
    · refine .inr ⟨SourceExecutionSize.stepSize [], target, updated, after, ?_, snapshot, written, ?_⟩
      · have positive := head.positive
        simp only [SourceExecutionSize.stepSize, List.sum_nil]
        omega
      · cases mode <;> exact .control .nil
  · obtain ⟨target, updated, equalContext, equalOutcome, snapshot, written⟩ :=
      statement_value unique found form bare head
    subst middleContext
    cases equalOutcome
    exact .inr ⟨tailSize, target, updated, middle, tailStrict, snapshot, written, tail⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBitNotInversion
