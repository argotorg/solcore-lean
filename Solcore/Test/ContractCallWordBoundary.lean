import Solcore.Core.ContractCallWordResultProperties
import Solcore.ContractRuntime.ContractCallFailure
import Solcore.ContractRuntime.ContractWordCallInput
import Solcore.ContractRuntime.HostStorageHandler

/-! Focused regressions for the low-level checked contract-word call boundary. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def target : Word := ⟨0x1234, by decide⟩
private def input : Word :=
  ⟨0x0102030405060708090a0b0c0d0e0f10, by decide⟩
private def payload : Word := ⟨0xa5, by decide⟩
private def trapReason : Word := ⟨0xb6, by decide⟩
private def failureReason : Word := ⟨0xc7, by decide⟩

private def returned : ContractCallWordResult := .returned payload
private def reverted : ContractCallWordResult := .reverted payload
private def trapped : ContractCallWordResult := .trapped trapReason
private def failed : ContractCallWordResult := .failed failureReason

private def canonicalResponses : List ContractCallWordResult :=
  [returned, reverted, trapped, failed]

private def canonicalRoundTrips : Bool :=
  canonicalResponses.all fun response =>
    ContractCallWordResult.ofValue? response.value == some response

private def canonicalValuesDisjoint : Bool :=
  returned.value != reverted.value &&
    returned.value != trapped.value &&
    returned.value != failed.value &&
    reverted.value != trapped.value &&
    reverted.value != failed.value &&
    trapped.value != failed.value

private theorem compileTimeCanonicalRoundTrips :
    canonicalRoundTrips = true := by
  native_decide

private theorem compileTimeCanonicalValuesDisjoint :
    canonicalValuesDisjoint = true := by
  native_decide

private theorem compileTimeCanonicalValuesTyped :
    returned.value.type = ContractCallWordResult.resultType ∧
      reverted.value.type = ContractCallWordResult.resultType ∧
      trapped.value.type = ContractCallWordResult.resultType ∧
      failed.value.type = ContractCallWordResult.resultType := by
  simp [returned, reverted, trapped, failed]

private def invalidAddressCode : Word := ⟨0, by decide⟩
private def unavailableCode : Word := ⟨1, by decide⟩
private def depthExceededCode : Word := ⟨2, by decide⟩

private def failureCodesExactAndDistinct : Bool :=
  ContractCallFailure.invalidAddress.code == invalidAddressCode &&
    ContractCallFailure.unavailable.code == unavailableCode &&
    ContractCallFailure.depthExceeded.code == depthExceededCode &&
    ContractCallFailure.invalidAddress.code !=
      ContractCallFailure.unavailable.code &&
    ContractCallFailure.invalidAddress.code !=
      ContractCallFailure.depthExceeded.code &&
    ContractCallFailure.unavailable.code !=
      ContractCallFailure.depthExceeded.code

private theorem compileTimeFailureCodes :
    failureCodesExactAndDistinct = true := by
  native_decide

private theorem compileTimeFailureBranches :
    ContractCallFailure.invalidAddress.result = .failed invalidAddressCode ∧
      ContractCallFailure.unavailable.result = .failed unavailableCode ∧
      ContractCallFailure.depthExceeded.result = .failed depthExceededCode := by
  native_decide

private def canonicalInput : HostStorageDriver.InputData :=
  HostStorageDriver.InputData.ofWord input

private def canonicalInputExact : Bool :=
  canonicalInput.bytes.size == 32 &&
    canonicalInput.bytes == encodeWordBytesBE input &&
    canonicalInput.sizeWord.val == 32 &&
    canonicalInput.wordBE? Word.zero == some input

private theorem compileTimeCanonicalInputExact :
    canonicalInputExact = true := by
  native_decide

private theorem compileTimeCanonicalInputWordBE :
    canonicalInput.wordBE? Word.zero = some input := by
  exact HostStorageDriver.InputData.ofWord_wordBE?_zero input

/-- A checker-accepted Core program that emits the new typed host request. -/
private def callProgram : Program := {
  resultType := ContractCallWordResult.resultType
  body :=
    .apply
      (.var HostFunction.callContractWord.index)
      (.pair (.word target) (.word input))
}

private theorem callProgramHostChecked :
    callProgram.checkHost = true := by
  decide

private def callCode : CheckedHostCoreProgram :=
  ⟨callProgram, callProgramHostChecked⟩

/-- Observe emission and feed a request-indexed response back to Core. -/
private def checkedCallEmitsAndResumes : Bool :=
  match callCode.program.runHostStateful 32 with
  | .suspended
      ⟨.callContractWord actualTarget actualInput, continuation, store⟩
      remainingFuel =>
      actualTarget == target && actualInput == input &&
        let suspension : HostSuspension :=
          ⟨.callContractWord actualTarget actualInput, continuation, store⟩
        match hostRun remainingFuel
            (suspension.resume (ContractCallWordResult.returned payload)) with
        | .done value finalStore =>
            value == returned.value && finalStore == []
        | _ => false
  | _ => false

private theorem compileTimeCheckedCallEmitsAndResumes :
    checkedCallEmitsAndResumes = true := by
  native_decide

private def storageAddress : Address := ⟨0x20, by decide⟩
private def callerAddress : Address := ⟨0x30, by decide⟩
private def storageSlot : Word := ⟨0x40, by decide⟩
private def storageValue : Word := ⟨0x50, by decide⟩

private def storageAccount : Account :=
  Account.empty.storageWrite storageSlot storageValue

private def world : WorldState :=
  WorldState.empty.putAccount storageAddress storageAccount

private def context : HostStorageDriver.Context Nat (List Nat) :=
  ⟨⟨storageAddress,
      ⟨⟨world, ⟨7, [8]⟩⟩, (world, ⟨9, [10, 11]⟩)⟩⟩,
    storageAccount,
    by rfl⟩

private def executionInputs : HostStorageDriver.ExecutionInputs := {
  codeAddress := storageAddress
  callValue := Word.zero
  callerAddress := callerAddress
  inputData := canonicalInput
  currentAddress := storageAddress
}

private def flatHandled :
    HostStorageDriver.Context Nat (List Nat) × ContractCallWordResult :=
  HostStorageDriver.handleRequest executionInputs context
    (.callContractWord target input)

private theorem compileTimeFlatHandlerExact :
    flatHandled =
      (context, ContractCallFailure.depthExceeded.result) := by
  rfl

private def storageValueAt?
    (state : WorldState) (address : Address) (slot : Word) : Option Word :=
  (state.account? address).bind fun account => account.storageValue? slot

private def flatHandlerPreservesObservableContext : Bool :=
  flatHandled.2 == ContractCallFailure.depthExceeded.result &&
    flatHandled.1.context.storageAddress == storageAddress &&
    flatHandled.1.storageAccount.storageRead storageSlot == storageValue &&
    storageValueAt? flatHandled.1.context.values.checkpoint.state
      storageAddress storageSlot == some storageValue &&
    storageValueAt? flatHandled.1.context.values.working.1
      storageAddress storageSlot == some storageValue &&
    flatHandled.1.context.values.checkpoint.effects.rollback == 7 &&
    flatHandled.1.context.values.checkpoint.effects.trace == [8] &&
    flatHandled.1.context.values.working.2.rollback == 9 &&
    flatHandled.1.context.values.working.2.trace == [10, 11]

private theorem compileTimeFlatHandlerPreservesContext :
    flatHandlerPreservesObservableContext = true := by
  native_decide

/-- Runtime counterpart to the compile-time boundary assertions above. -/
def testContractCallWordBoundary : IO Unit := do
  assertTrue canonicalRoundTrips
    "contract-call response values did not round-trip canonically"
  assertTrue canonicalValuesDisjoint
    "contract-call response constructors shared a Core value"
  assertTrue failureCodesExactAndDistinct
    "contract-call dispatch failure codes changed or collided"
  assertTrue canonicalInputExact
    "contract-word input was not the exact 32-byte big-endian encoding"
  assertTrue checkedCallEmitsAndResumes
    "checked Core call did not emit and resume with its typed response"
  assertTrue flatHandlerPreservesObservableContext
    "flat handler did not reject recursion without changing its context"

end Tests
