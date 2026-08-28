import Solcore.Semantics.FrameEffectJournal

set_option autoImplicit false

namespace Solcore.Semantics.FrameEffectJournal

universe u v w

@[simp] theorem resolved?_returned
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (checkpoint working : FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    resolved? checkpoint working
      (FrameOutcome.returned (TrapReason := TrapReason) data) = some working := by
  rfl

@[simp] theorem resolved?_reverted
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (checkpoint working : FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    resolved? checkpoint working
      (FrameOutcome.reverted (TrapReason := TrapReason) data) =
        some ⟨checkpoint.rollback, working.trace⟩ := by
  rfl

@[simp] theorem resolved?_trapped
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (checkpoint working : FrameEffectJournal RollbackState TraceState)
    (reason : TrapReason) :
    resolved? checkpoint working (.trapped reason) = none := by
  rfl

theorem resolved?_child_return_parent_revert
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (parentCheckpoint childCheckpoint childWorking :
      FrameEffectJournal RollbackState TraceState)
    (childData parentData : Bytes) :
    (resolved? childCheckpoint childWorking
      (FrameOutcome.returned (TrapReason := TrapReason) childData)).bind
        (fun childResolved => resolved? parentCheckpoint childResolved
          (FrameOutcome.reverted (TrapReason := TrapReason) parentData)) =
      some ⟨parentCheckpoint.rollback, childWorking.trace⟩ := by
  rfl

theorem resolved?_child_revert_parent_revert
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (parentCheckpoint childCheckpoint childWorking :
      FrameEffectJournal RollbackState TraceState)
    (childData parentData : Bytes) :
    (resolved? childCheckpoint childWorking
      (FrameOutcome.reverted (TrapReason := TrapReason) childData)).bind
        (fun childResolved => resolved? parentCheckpoint childResolved
          (FrameOutcome.reverted (TrapReason := TrapReason) parentData)) =
      some ⟨parentCheckpoint.rollback, childWorking.trace⟩ := by
  rfl

end Solcore.Semantics.FrameEffectJournal
