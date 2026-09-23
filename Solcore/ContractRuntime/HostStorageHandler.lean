import Solcore.ContractRuntime.AddressWordBridge
import Solcore.ContractRuntime.ContractCallFailure
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageRead
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWrite
import Solcore.ContractRuntime.HostDriver
import Solcore.ContractRuntime.HostStorageContext
import Solcore.ContractRuntime.HostStorageExecutionInputs

/-! Canonical host handler for storage and immutable execution inputs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostStorageDriver

universe u v

/--
Total response function used by the legacy storage policy. The `emitLogWord`
arm exists only because `HostHandler.handle` is request-total; `handler` marks
that request unsupported, so `HostDriver.run` never invokes the arm. Observable
execution must use `TransactionHostStorageDriver`.
-/
def handleRequest
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (request : Core.HostRequest) :
    Context RollbackState TraceState × request.Response :=
  match request with
  | .storageRead slot => (context, context.readStorage slot)
  | .storageWrite slot value => (context.writeStorage slot value, ())
  | .storageAddress =>
      (context, addressToWord context.context.storageAddress)
  | .codeAddress => (context, addressToWord inputs.codeAddress)
  | .callValue => (context, inputs.callValue)
  | .callerAddress => (context, addressToWord inputs.callerAddress)
  | .inputDataByte? offset => (context, inputs.inputData.byte? offset)
  | .inputDataSize => (context, inputs.inputData.sizeWord)
  | .inputDataWordBE? offset => (context, inputs.inputData.wordBE? offset)
  | .currentAddress => (context, addressToWord inputs.currentAddress)
  | .callContractWord _ _ =>
      (context, ContractCallFailure.depthExceeded.result)
  | .callContractWordWithValue _ _ _ =>
      (context, ContractCallFailure.depthExceeded.result)
  | .createContractWord _ _ _ =>
      (context, ContractCallFailure.depthExceeded.result)
  | .emitLogWord _ _ => (context, ())

/-- Current combined handler indexed by the complete run-fixed input. -/
def handler
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs) :
    HostHandler (Context RollbackState TraceState) where
  supports
    | .emitLogWord _ _ => false
    | _ => true
  handle := handleRequest inputs

/-- Handle one suspension using the complete run-fixed input. -/
def handleSuspension
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    Context RollbackState TraceState × Core.State :=
  (handler inputs).handleSuspension context suspension

end Solcore.ContractRuntime.HostStorageDriver
