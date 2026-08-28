import Solcore.Semantics.ParentIndexedFrameContinuationConstruction

/-! Projection laws for trace-extension parent-context construction. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

universe u v w

@[simp] theorem stateCheckpoint_fromTraceExtension
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event))
    (workingRollback : RollbackState)
    (extension : FrameTrace.ExtensionFrom parentWorking.2.trace)
    (result : FrameRunResult TrapReason) :
    (fromTraceExtension
      parentWorking workingRollback extension result).stateCheckpoint =
      parentWorking.1 := by
  rfl

@[simp] theorem effectCheckpoint_fromTraceExtension
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event))
    (workingRollback : RollbackState)
    (extension : FrameTrace.ExtensionFrom parentWorking.2.trace)
    (result : FrameRunResult TrapReason) :
    (fromTraceExtension
      parentWorking workingRollback extension result).effectCheckpoint =
      parentWorking.2 := by
  rfl

@[simp] theorem effectWorking_fromTraceExtension
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event))
    (workingRollback : RollbackState)
    (extension : FrameTrace.ExtensionFrom parentWorking.2.trace)
    (result : FrameRunResult TrapReason) :
    (fromTraceExtension
      parentWorking workingRollback extension result).effectWorking =
      ⟨workingRollback, extension.toTrace⟩ := by
  rfl

@[simp] theorem result_fromTraceExtension
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event))
    (workingRollback : RollbackState)
    (extension : FrameTrace.ExtensionFrom parentWorking.2.trace)
    (result : FrameRunResult TrapReason) :
    (fromTraceExtension
      parentWorking workingRollback extension result).result = result := by
  rfl

end Solcore.Semantics.ParentIndexedFrameContinuationContext
