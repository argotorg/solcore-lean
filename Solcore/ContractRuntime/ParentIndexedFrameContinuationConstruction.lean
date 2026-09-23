import Solcore.ContractRuntime.FrameTrace
import Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

/-! Restricted construction of a parent-indexed context from a trace extension. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w

/-- Build the indexed context while deriving its two relationship proofs. -/
def fromTraceExtension
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event))
    (workingRollback : RollbackState)
    (extension : FrameTrace.ExtensionFrom parentWorking.2.trace)
    (result : FrameRunResult TrapReason) :
    ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking :=
  {
    stateCheckpoint := parentWorking.1
    effectCheckpoint := parentWorking.2
    effectWorking := ⟨workingRollback, extension.toTrace⟩
    result := result
    tracePrefix := extension.earlier_isPrefixOf_toTrace
    checkpoint_eq_parentWorking := rfl
  }

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameContinuationConstructionProperties`
-/

/-! Projection laws for trace-extension parent-context construction. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

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

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext
