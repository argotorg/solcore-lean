import Solcore.Semantics.ParentIndexedFrameInitialization
import Solcore.Semantics.FrameTraceExtensionProperties

/-! Canonical observation laws for parent-indexed frame initialization. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedFrameInitialization

universe u v

/-- The initial extension observes the exact indexed parent trace. -/
@[simp] theorem initialTraceExtension_toTrace
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    initialization.initialTraceExtension.toTrace =
      parentWorking.2.trace := by
  exact FrameTrace.ExtensionFrom.toTrace_start parentWorking.2.trace

/-- The derived carrier has the parent checkpoint and supplied initial state. -/
@[simp] theorem toCheckpointedWorkingPair_eq
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    initialization.toCheckpointedWorkingPair =
      ⟨FrameCheckpointSnapshot.fromWorkingPair parentWorking,
        (initialization.initialWorld,
          ⟨initialization.workingRollback, parentWorking.2.trace⟩)⟩ := by
  simp [toCheckpointedWorkingPair]

end Solcore.Semantics.ParentIndexedFrameInitialization
