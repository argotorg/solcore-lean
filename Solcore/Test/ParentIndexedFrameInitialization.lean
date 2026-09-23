import Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-! Compile-only regressions for parent-indexed frame initialization. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

private example
    {RollbackState Event : Type}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    initialization.initialTraceExtension.toTrace =
      parentWorking.2.trace := by
  simp

private example
    {RollbackState Event : Type}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    initialization.toCheckpointedWorkingPair =
      ⟨FrameCheckpointSnapshot.fromWorkingPair parentWorking,
        (initialization.initialWorld,
          ⟨initialization.workingRollback, parentWorking.2.trace⟩)⟩ := by
  simp

private example
    {RollbackState Event Result : Type}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (consume :
      FrameCheckpointedWorkingPair RollbackState (FrameTrace Event) → Result) :
    consume initialization.toCheckpointedWorkingPair =
      consume
        ⟨FrameCheckpointSnapshot.fromWorkingPair parentWorking,
          (initialization.initialWorld,
            ⟨initialization.workingRollback, parentWorking.2.trace⟩)⟩ := by
  simp

end Tests
