import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialInversion
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedBitNotInversion

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialInversion
open Frontend SourceInference
open SelectedCompilationStageForInitialBounds

/-- Preserve the actual assignment grade before the remaining initialization. -/
theorem bitNotProjected {program : Program} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {items post : List ForItemForm} {test : ExpressionId} {body : List StatementId}
    {size : Nat} {outcome : Dynamic.ControlOutcome}
    {assignment : AssignmentResolution}
    (trace : PlainInitial program invocation context environment before
      (.assignBitNot assignment :: items) test post body size outcome after) :
    (∃ assignedSize reason, assignedSize < size ∧ outcome = .fault reason ∧
      SourceExecutionSize.SourcePlaceBitNotFaults program assignedSize context invocation.evidence invocation.source
        environment before assignment.target reason after) ∨
    (∃ assignedSize tailSize updated written, assignedSize < size ∧ tailSize < size ∧
      SourceExecutionSize.SourcePlaceSnapshotUpdate program assignedSize context invocation.evidence invocation.source
        Dynamic.BitNotSnapshot environment before assignment.target updated written ∧
      PlainInitial program invocation context environment written items test post body tailSize outcome after) := by
  rcases head trace with ⟨_, reason, strict, same, failed⟩ |
    ⟨_, _, _, _, _, _, childStrict, tailStrict, same, executed, tail⟩
  · obtain ⟨assignedSize, assignedStrict, failed⟩ := SelectedCompilationStageProjectedBitNotInversion.item_fault failed
    exact .inl ⟨assignedSize, reason, Nat.lt_trans assignedStrict strict, same, failed⟩
  · obtain ⟨assignedSize, updated, assignedStrict, rfl, rfl, assigned⟩ :=
      SelectedCompilationStageProjectedBitNotInversion.item_value executed
    rw [restored tail] at same
    subst outcome
    exact .inr ⟨assignedSize, _, updated, _, Nat.lt_trans assignedStrict childStrict, tailStrict, assigned, tail⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialInversion
