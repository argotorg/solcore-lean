import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsSourceInversion
import Solcore.SourceSemantics.Staging.RecursiveBareBitNotFacts

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsBitNotInversion
open Frontend SourceInference
open SelectedCompilationStageForLiftBounds
open Staging.Recursive (BareTarget)

variable {program : Program} {invocation : Staging.Recursive.Scope}
  {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {assignment : AssignmentResolution}
  {size : Nat} {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

theorem item_value {nextEnvironment : Dynamic.Environment}
    (bare : assignment.target.projections = [])
    (trace : SourceExecutionSize.ForItemExecutes program size context invocation.evidence invocation.source environment
      before (.assignBitNot assignment) finalContext nextEnvironment after) :
    ∃ target updated, finalContext = context ∧ nextEnvironment = environment ∧
      BareTarget environment before assignment.target target ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        before target updated after := by
  cases trace with
  | assignBitNot executed =>
    obtain ⟨target, snapshot, written⟩ := (Staging.Recursive.bitNot_update_iff bare).mp executed.sound
    exact ⟨target, _, rfl, rfl, snapshot, written⟩

theorem item_fault (bare : assignment.target.projections = [])
    (trace : SourceExecutionSize.ForItemFaults program size context invocation.evidence invocation.source environment
      before (.assignBitNot assignment) reason after) :
    after = before ∧ Dynamic.SourcePlaceBitNotFaults program context invocation.evidence invocation.source environment
      before assignment.target reason before := by
  cases trace with
  | assignBitNot failed => exact (Staging.Recursive.bitNot_fault_iff bare).mp failed.sound

theorem write_and_tail {rest : List ForItemForm}
    (bare : assignment.target.projections = [])
    (trace : PlainItems program size invocation context environment before
      (.assignBitNot assignment :: rest) finalContext outcome after) :
    (∃ reason, finalContext = context ∧ outcome = .fault reason ∧ after = before ∧
      Dynamic.SourcePlaceBitNotFaults program context invocation.evidence invocation.source environment
        before assignment.target reason before) ∨
    (∃ tailSize target updated written, tailSize < size ∧
      BareTarget environment before assignment.target target ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        before target updated written ∧
      PlainItems program tailSize invocation context environment written rest finalContext outcome after) := by
  cases trace with
  | done trace =>
    cases trace with
    | cons head tail =>
      obtain ⟨target, updated, rfl, rfl, snapshot, written⟩ := item_value bare head
      exact .inr ⟨_, target, updated, _, SourceExecutionSize.child_lt_stepSize (by simp), snapshot, written, .done tail⟩
  | fault trace =>
    cases trace with
    | head failed =>
      obtain ⟨sameHeap, failed⟩ := item_fault bare failed
      exact .inl ⟨_, rfl, rfl, sameHeap, failed⟩
    | tail head failed =>
      obtain ⟨target, updated, rfl, rfl, snapshot, written⟩ := item_value bare head
      exact .inr ⟨_, target, updated, _, SourceExecutionSize.child_lt_stepSize (by simp), snapshot, written, .fault failed⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsBitNotInversion
