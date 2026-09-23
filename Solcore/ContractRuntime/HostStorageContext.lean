import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-! Mutable context threaded by handled storage execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostStorageDriver

universe u v

abbrev Context
    (RollbackState : Type u) (TraceState : Type v) :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount
    RollbackState TraceState

end Solcore.ContractRuntime.HostStorageDriver
