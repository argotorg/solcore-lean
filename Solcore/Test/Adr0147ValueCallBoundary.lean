import Solcore.Core.HostProgress
import Solcore.ContractRuntime.BalanceTransfer
import Solcore.ContractRuntime.HostStorageHandler
import Solcore.ContractRuntime.NestedWordCall

/-! External and executable regressions for the ADR-0147 value-call boundary. -/

set_option autoImplicit false

namespace Tests.Adr0147ValueCallBoundary

open Solcore.Core
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

/-! Public boundary laws remain usable outside their defining namespaces. -/
example := HostFunction.parameterType_callContractWordWithValue
example := HostFunction.resultType_callContractWordWithValue
example := HostFunction.index_callContractWordWithValue
example := hostContext_callContractWordWithValue
example := hostEnvironment_callContractWordWithValue
example := HostRequest.responseType_callContractWordWithValue
example := HostRequest.responseValue_callContractWordWithValue
example := HostSuspension.resume_callContractWordWithValue
example := hostAdvance_begin_callContractWordWithValue
example := hostAdvance_suspend_callContractWordWithValue
example := hostAdvance_invalid_callContractWordWithValue_argument
example := @HostRuntimeValueHasType.wordTriple_shape
example := @typed_callContractWordWithValue_emits

example := ContractCallFailure.code_insufficientBalance
example := ContractCallFailure.code_balanceOverflow
example := BalanceTransferFailure.toContractCallFailure_senderAbsent
example := BalanceTransferFailure.toContractCallFailure_recipientAbsent
example := BalanceTransferFailure.toContractCallFailure_insufficientBalance
example := BalanceTransferFailure.toContractCallFailure_recipientOverflow
example := BalanceTransferFailure.toContractCallResult_code

example := TopLevelInvocation.childWordWithValue_target
example := TopLevelInvocation.childWordWithValue_caller
example := TopLevelInvocation.childWordWithValue_callValue
example := TopLevelInvocation.childWordWithValue_inputBytes
example := TopLevelInvocation.childWordWithValue_executionInputs

private def targetWord : Word := ⟨0x1234, by decide⟩
private def targetAddress : Address := ⟨0x1234, by decide⟩
private def transferredValue : Word := ⟨0x45, by decide⟩
private def input : Word := ⟨0x6789, by decide⟩
private def payload : Word := ⟨0xab, by decide⟩

private def valueCallProgram : Program := {
  resultType := ContractCallWordResult.resultType
  body :=
    .apply
      (.var HostFunction.callContractWordWithValue.index)
      (.pair (.word targetWord)
        (.pair (.word transferredValue) (.word input)))
}

private theorem valueCallProgram_checked :
    valueCallProgram.checkHost = true := by
  decide

private def valueCallCode : CheckedHostCoreProgram :=
  ⟨valueCallProgram, valueCallProgram_checked⟩

/-- The checker-accepted program emits the exact target/value/input request. -/
private def checkedValueCallEmitsAndResumes : Bool :=
  match valueCallCode.program.runHostStateful 32 with
  | .suspended
      ⟨.callContractWordWithValue actualTarget actualValue actualInput,
        continuation, store⟩
      remainingFuel =>
      actualTarget == targetWord && actualValue == transferredValue &&
        actualInput == input &&
        let suspension : HostSuspension :=
          ⟨.callContractWordWithValue actualTarget actualValue actualInput,
            continuation, store⟩
        match hostRun remainingFuel
            (suspension.resume (.returned payload)) with
        | .done result finalStore =>
            result == (ContractCallWordResult.returned payload).value &&
              finalStore == []
        | _ => false
  | _ => false

private theorem compileTimeCheckedValueCall :
    checkedValueCallEmitsAndResumes = true := by
  native_decide

private def insufficientCode : Word := ⟨3, by decide⟩
private def overflowCode : Word := ⟨4, by decide⟩

private def failureMappingExact : Bool :=
  ContractCallFailure.insufficientBalance.code == insufficientCode &&
    ContractCallFailure.balanceOverflow.code == overflowCode &&
    BalanceTransferFailure.insufficientBalance.toContractCallResult ==
      ContractCallWordResult.failed insufficientCode &&
    BalanceTransferFailure.recipientOverflow.toContractCallResult ==
      ContractCallWordResult.failed overflowCode

private theorem compileTimeFailureMapping : failureMappingExact = true := by
  native_decide

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
    (.callContractWordWithValue targetWord transferredValue input)

private theorem compileTimeFlatHandlerExact :
    flatHandled =
      (context, ContractCallFailure.depthExceeded.result) := by
  rfl

private def childInvocationExact : Bool :=
  let child := TopLevelInvocation.childWordWithValue
    inputs targetAddress transferredValue input
  child.target == targetAddress &&
    child.caller == inputs.currentAddress &&
    child.callValue == transferredValue &&
    child.inputData.bytes == encodeWordBytesBE input

private theorem compileTimeChildInvocationExact :
    childInvocationExact = true := by
  native_decide

def testAdr0147ValueCallBoundary : IO Unit := do
  assertTrue checkedValueCallEmitsAndResumes
    "checked value call did not preserve target/value/input order"
  assertTrue failureMappingExact
    "balance transfer failures did not use stable call failure codes"
  assertTrue
    (flatHandled.2 == ContractCallFailure.depthExceeded.result)
    "flat handler changed context or accepted nested value call"
  assertTrue childInvocationExact
    "value-bearing child invocation did not preserve caller or call value"

end Tests.Adr0147ValueCallBoundary
