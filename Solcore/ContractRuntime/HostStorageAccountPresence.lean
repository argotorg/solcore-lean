import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteIsolationProperties
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteProjectionProperties
import Solcore.ContractRuntime.HostStorageContextRebase
import Solcore.ContractRuntime.HostStorageHandler

/-! Presence evidence retained while another selected Account is being handled. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- One exact present Account witness at an arbitrary world-state address. -/
structure PresentAccountAt (world : WorldState) (address : Address) where
  account : Account
  present : world.account? address = some account

namespace HostStorageDriver.Context

universe u v

/-- Every storage context supplies presence at its own selected address. -/
def selectedPresence
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState) :
    PresentAccountAt context.context.values.working.1
      context.context.storageAddress :=
  ⟨context.storageAccount, context.storageAccount_present⟩

/-- Rebase from one arbitrary presence witness at the retained selector. -/
def rebaseFromPresence
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (presence : PresentAccountAt world context.context.storageAddress) :
    HostStorageDriver.Context RollbackState TraceState :=
  context.rebaseWorking world presence.account presence.present

end HostStorageDriver.Context

namespace PresentAccountAt

universe u v

/--
One low-level handled request preserves Account presence at every observed
address, including both the selected address and every different address.
-/
def afterHandleRequest
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (request : Core.HostRequest)
    (address : Address)
    (presence :
      PresentAccountAt context.context.values.working.1 address) :
    PresentAccountAt
      (HostStorageDriver.handleRequest inputs context request).1.context.values.working.1
      address := by
  cases request with
  | storageWrite slot value =>
      by_cases same : address = context.context.storageAddress
      · refine ⟨(context.writeStorage slot value).storageAccount, ?_⟩
        simpa [HostStorageDriver.handleRequest, same] using
          (context.writeStorage slot value).storageAccount_present
      · refine ⟨presence.account, ?_⟩
        simpa [HostStorageDriver.handleRequest] using
          (FrameCheckpointedWorkingPairWithPresentStorageAccount.workingAccount?_writeStorage_other
            context slot value address same).trans presence.present
  | storageRead slot =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | storageAddress =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | codeAddress =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | callValue =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | callerAddress =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | inputDataByte? offset =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | inputDataSize =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | inputDataWordBE? offset =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | currentAddress =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | callContractWord target input =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | callContractWordWithValue target value input =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | createContractWord templateId value input =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | emitLogWord topic payload =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩

end PresentAccountAt

end Solcore.ContractRuntime
