import Solcore.Semantics.ParentIndexedSelectedExecutionResult

/-! Lossy compatibility erasure for branch-complete selected execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedSelectedExecutionResult

universe u v w

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/-- Reproduce the legacy three-`Option` observation exactly. -/
def toLegacy : Result RollbackState Event TrapReason parentWorking →
    Option (Option (Option (ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)))
  | .storageAbsent => none
  | .codeAbsent => some none
  | .outOfFuel _ _ => some (some none)
  | .fault _ _ _ => some (some none)
  | .unsupported _ _ _ => some (some none)
  | .completed _ _ _ continuation => some (some (some continuation))

@[simp] theorem toLegacy_storageAbsent :
    (storageAbsent : Result
      RollbackState Event TrapReason parentWorking).toLegacy = none :=
  rfl

@[simp] theorem toLegacy_codeAbsent :
    (codeAbsent : Result
      RollbackState Event TrapReason parentWorking).toLegacy = some none :=
  rfl

@[simp] theorem toLegacy_outOfFuel
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (state : Core.State) :
    (outOfFuel context state : Result
      RollbackState Event TrapReason parentWorking).toLegacy =
      some (some none) :=
  rfl

@[simp] theorem toLegacy_fault
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (error : Core.MachineFault)
    (state : Core.State) :
    (fault context error state : Result
      RollbackState Event TrapReason parentWorking).toLegacy =
      some (some none) :=
  rfl

@[simp] theorem toLegacy_unsupported
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (suspension : Core.HostSuspension)
    (remainingFuel : Nat) :
    (unsupported context suspension remainingFuel : Result
      RollbackState Event TrapReason parentWorking).toLegacy =
      some (some none) :=
  rfl

@[simp] theorem toLegacy_completed
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    (completed context value store continuation : Result
      RollbackState Event TrapReason parentWorking).toLegacy =
      some (some (some continuation)) :=
  rfl

end Solcore.Semantics.ParentIndexedSelectedExecutionResult
