import Solcore.Core.HostProgress
import Solcore.ContractRuntime.ContractCallFailure
import Solcore.ContractRuntime.ContractWordCallInput
import Solcore.ContractRuntime.HostStorageHandler

/-! Executable and external checks for the append-only creation host boundary. -/

set_option autoImplicit false

namespace Tests.Adr0148CreateContractWordBoundary

open Solcore.Core
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

example := HostFunction.parameterType_createContractWord
example := HostFunction.resultType_createContractWord
example := HostFunction.index_createContractWord
example := hostContext_createContractWord
example := hostEnvironment_createContractWord
example := HostRequest.responseType_createContractWord
example := HostRequest.responseValue_createContractWord
example := HostSuspension.resume_createContractWord
example := hostAdvance_begin_createContractWord
example := hostAdvance_suspend_createContractWord
example := hostAdvance_invalid_createContractWord_argument
example := @typed_createContractWord_emits
example := ContractCallFailure.code_nonceOverflow
example := ContractCallFailure.code_addressCollision

private def templateId : Word := ⟨0x48, by decide⟩
private def transferredValue : Word := ⟨0x12, by decide⟩
private def input : Word := ⟨0x34, by decide⟩
private def payload : Word := ⟨0x56, by decide⟩

private def creationProgram : Program := {
  resultType := ContractCallWordResult.resultType
  body :=
    .apply
      (.var HostFunction.createContractWord.index)
      (.pair (.word templateId)
        (.pair (.word transferredValue) (.word input)))
}

private theorem creationProgram_checked :
    creationProgram.checkHost = true := by
  decide

private def creationCode : CheckedHostCoreProgram :=
  ⟨creationProgram, creationProgram_checked⟩

private def checkedCreationEmitsAndResumes : Bool :=
  match creationCode.program.runHostStateful 32 with
  | .suspended
      ⟨.createContractWord actualTemplate actualValue actualInput,
        continuation, store⟩
      remainingFuel =>
      actualTemplate == templateId && actualValue == transferredValue &&
        actualInput == input &&
        let suspension : HostSuspension :=
          ⟨.createContractWord actualTemplate actualValue actualInput,
            continuation, store⟩
        match hostRun remainingFuel
            (suspension.resume (.returned payload)) with
        | .done result finalStore =>
            result == (ContractCallWordResult.returned payload).value &&
              finalStore == []
        | _ => false
  | _ => false

private def word (value : Nat) (bound : value < wordModulus := by decide) :
    Word :=
  ⟨value, bound⟩

private def failureCodesExactAndDistinct : Bool :=
  ContractCallFailure.invalidAddress.code == word 0 &&
    ContractCallFailure.unavailable.code == word 1 &&
    ContractCallFailure.depthExceeded.code == word 2 &&
    ContractCallFailure.insufficientBalance.code == word 3 &&
    ContractCallFailure.balanceOverflow.code == word 4 &&
    ContractCallFailure.nonceOverflow.code == word 5 &&
    ContractCallFailure.addressCollision.code == word 6 &&
    decide ([ContractCallFailure.invalidAddress.code,
      ContractCallFailure.unavailable.code,
      ContractCallFailure.depthExceeded.code,
      ContractCallFailure.insufficientBalance.code,
      ContractCallFailure.balanceOverflow.code,
      ContractCallFailure.nonceOverflow.code,
      ContractCallFailure.addressCollision.code].Nodup)

private def storageAddress : Address := ⟨0x20, by decide⟩
private def callerAddress : Address := ⟨0x30, by decide⟩
private def account : Account := Account.empty
private def world : WorldState :=
  WorldState.empty.putAccount storageAddress account

private def context : HostStorageDriver.Context Unit Unit :=
  ⟨⟨storageAddress,
      ⟨⟨world, ⟨(), ()⟩⟩, (world, ⟨(), ()⟩)⟩⟩,
    account,
    by rfl⟩

private def inputs : HostStorageDriver.ExecutionInputs := {
  codeAddress := storageAddress
  callValue := Word.zero
  callerAddress := callerAddress
  inputData := HostStorageDriver.InputData.ofWord input
  currentAddress := storageAddress
}

private def flatHandled :
    HostStorageDriver.Context Unit Unit × ContractCallWordResult :=
  HostStorageDriver.handleRequest inputs context
    (.createContractWord templateId transferredValue input)

private theorem flatHandlerExact :
    flatHandled = (context, ContractCallFailure.depthExceeded.result) := by
  rfl

private theorem compileTimeBoundaryExact :
    checkedCreationEmitsAndResumes && failureCodesExactAndDistinct = true := by
  native_decide

def testAdr0148CreateContractWordBoundary : IO Unit := do
  assertTrue checkedCreationEmitsAndResumes
    "checked creation did not preserve template/value/input order"
  assertTrue failureCodesExactAndDistinct
    "creation failure codes changed or collided with existing codes"
  assertTrue (flatHandled.2 == ContractCallFailure.depthExceeded.result)
    "flat execution unexpectedly handled contract creation"

end Tests.Adr0148CreateContractWordBoundary
