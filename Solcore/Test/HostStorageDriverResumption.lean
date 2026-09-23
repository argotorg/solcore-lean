import Solcore.ContractRuntime.HostStorageDriverFuelProperties

/-! Storage-specialized executable regressions for handled fuel resumption. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def codeAddress : Address := ⟨0x10, by decide⟩
private def storageAddress : Address := ⟨0x20, by decide⟩
private def otherAddress : Address := ⟨0x30, by decide⟩
private def callerAddress : Address := ⟨0x40, by decide⟩

private def targetSlot : Word := ⟨0x51, by decide⟩
private def oldValue : Word := ⟨0x52, by decide⟩
private def writtenValue : Word := ⟨0x53, by decide⟩
private def retainedSlot : Word := ⟨0x54, by decide⟩
private def retainedValue : Word := ⟨0x55, by decide⟩
private def otherSlot : Word := ⟨0x61, by decide⟩
private def otherValue : Word := ⟨0x62, by decide⟩
private def checkpointSlot : Word := ⟨0x71, by decide⟩
private def checkpointValue : Word := ⟨0x72, by decide⟩

private def threeByteInput : HostStorageDriver.InputData := {
  bytes := [0x11, 0x22, 0x33].toByteArray
  size_lt_wordModulus := by decide
}

private def oneByteInput : HostStorageDriver.InputData := {
  bytes := [0x11].toByteArray
  size_lt_wordModulus := by decide
}

private def inputsFor
    (inputData : HostStorageDriver.InputData) :
    HostStorageDriver.ExecutionInputs := {
  codeAddress := codeAddress
  callValue := Word.zero
  callerAddress := callerAddress
  inputData := inputData
  currentAddress := codeAddress
}

private def executionInputs := inputsFor threeByteInput
private def changedInputs := inputsFor oneByteInput

/-- Complete a working-storage write before observing an immutable input. -/
private def writeThenInputSizeProgram : Program := {
  resultType := .word
  body :=
    .letE
      (.apply
        (.var HostFunction.storageWrite.index)
        (.pair (.word targetSlot) (.word writtenValue)))
      (.apply (.var (HostFunction.inputDataSize.index + 1)) .unit)
}

private theorem writeThenInputSizeProgram_host_checked :
    writeThenInputSizeProgram.checkHost = true := by
  decide

private def writeThenInputSizeCode : CheckedHostCoreProgram :=
  ⟨writeThenInputSizeProgram, writeThenInputSizeProgram_host_checked⟩

private def selectedStorageAccount : Account :=
  Account.empty
    |>.storageWrite targetSlot oldValue
    |>.storageWrite retainedSlot retainedValue

private def workingWorld : WorldState :=
  WorldState.empty
    |>.putAccount storageAddress selectedStorageAccount
    |>.putAccount otherAddress
      (Account.empty.storageWrite otherSlot otherValue)

private def checkpointWorld : WorldState :=
  WorldState.empty
    |>.putAccount storageAddress
      (Account.empty.storageWrite checkpointSlot checkpointValue)
    |>.putAccount otherAddress
      (Account.empty.storageWrite otherSlot checkpointValue)

private def baseStorageContext :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨storageAddress,
    ⟨⟨checkpointWorld, ⟨11, [12, 13]⟩⟩,
      (workingWorld, ⟨21, [22, 23]⟩)⟩⟩

private theorem selectedStorageAccount_present :
    baseStorageContext.values.working.1.account?
        baseStorageContext.storageAddress =
      some selectedStorageAccount := by
  rfl

private def baseContext : HostStorageDriver.Context Nat (List Nat) :=
  ⟨baseStorageContext, selectedStorageAccount,
    selectedStorageAccount_present⟩

private def storageValueAt?
    (state : WorldState) (address : Address) (slot : Word) : Option Word :=
  (state.account? address).bind fun account => account.storageValue? slot

private def contextPreserved
    (context : HostStorageDriver.Context Nat (List Nat)) : Bool :=
  let values := context.context.values
  context.context.storageAddress == storageAddress &&
    context.storageAccount.storageValue? retainedSlot == some retainedValue &&
    storageValueAt? values.working.1 otherAddress otherSlot == some otherValue &&
    storageValueAt? values.checkpoint.state storageAddress checkpointSlot ==
      some checkpointValue &&
    storageValueAt? values.checkpoint.state otherAddress otherSlot ==
      some checkpointValue &&
    values.checkpoint.effects.rollback == 11 &&
    values.checkpoint.effects.trace == [12, 13] &&
    values.working.2.rollback == 21 &&
    values.working.2.trace == [22, 23]

private def hasCompletedWrite
    (context : HostStorageDriver.Context Nat (List Nat)) : Bool :=
  context.storageAccount.storageValue? targetSlot == some writtenValue &&
    storageValueAt? context.context.values.working.1
      storageAddress targetSlot == some writtenValue

private def beforeInputSuffix (state : State) : Bool :=
  state.control == .ret .unit &&
    match state.continuation with
    | [.letBody body _] =>
        body ==
          .apply (.var (HostFunction.inputDataSize.index + 1)) .unit
    | _ => false

private def firstFuel : Nat := 10
private def suffixFuel : Nat := 6
private def completionFuel : Nat := 16
private def largerFuel : Nat := 32

private def firstResult :=
  writeThenInputSizeCode.runWithStorage
    baseContext executionInputs firstFuel

private def splitResult :=
  firstResult.resumeWithFuel
    (HostStorageDriver.handler executionInputs) suffixFuel

private def oneShotResult :=
  writeThenInputSizeCode.runWithStorage
    baseContext executionInputs completionFuel

private def largerResult :=
  writeThenInputSizeCode.runWithStorage
    baseContext executionInputs largerFuel

/-- Deliberately outside the same-input theorem: resume with changed input. -/
private def changedInputResume :=
  firstResult.resumeWithFuel
    (HostStorageDriver.handler changedInputs) suffixFuel

private theorem measured_first_exhaustion :
    (match firstResult with
    | { context, outcome := .outOfFuel state } =>
        hasCompletedWrite context &&
          contextPreserved context && beforeInputSuffix state
    | _ => false) = true := by
  native_decide

private theorem measured_one_shot_completion :
    oneShotResult.outcome =
      .done (.word threeByteInput.sizeWord) [] := by
  native_decide

/-- Exact result equality includes context, value, and Core-local Store. -/
private theorem measured_split_one_shot_exact :
    splitResult = oneShotResult := by
  simpa [splitResult, firstResult, oneShotResult, firstFuel,
    suffixFuel, completionFuel] using
    writeThenInputSizeCode.runWithStorage_resumeWithFuel
      baseContext executionInputs firstFuel suffixFuel

private theorem measured_larger_exact :
    largerResult = oneShotResult := by
  have exactOneShot :
      oneShotResult =
        ⟨oneShotResult.context,
          .done (.word threeByteInput.sizeWord) []⟩ := by
    cases resultEq : oneShotResult with
    | mk context outcome =>
        have outcomeEq :
            outcome = .done (.word threeByteInput.sizeWord) [] := by
          simpa [resultEq] using measured_one_shot_completion
        subst outcome
        rfl
  have stable :
      largerResult =
        ⟨oneShotResult.context,
          .done (.word threeByteInput.sizeWord) []⟩ :=
    writeThenInputSizeCode.runWithStorage_done_stable
      (fuel := completionFuel) (largerFuel := largerFuel)
      baseContext executionInputs exactOneShot
      (show completionFuel ≤ largerFuel by decide)
  exact stable.trans exactOneShot.symm

private theorem measured_changed_input_completion :
    changedInputResume.outcome =
      .done (.word oneByteInput.sizeWord) [] := by
  native_decide

/-- A concrete changed-input suffix differs; no general disequality is claimed. -/
private theorem measured_changed_input_changes_suffix :
    changedInputResume.outcome ≠ splitResult.outcome := by
  native_decide

private theorem run_preserves_checkpoint (fuel : Nat) :
    (writeThenInputSizeCode.runWithStorage
      baseContext executionInputs fuel).context.context.values.checkpoint =
        baseContext.context.values.checkpoint := by
  change
    (HostStorageDriver.run baseContext executionInputs fuel
      (State.initial writeThenInputSizeProgram.body hostEnvironment)).context.context.values.checkpoint = _
  exact HostStorageDriver.run_checkpoint baseContext executionInputs fuel _

private theorem run_preserves_working_effects (fuel : Nat) :
    (writeThenInputSizeCode.runWithStorage
      baseContext executionInputs fuel).context.context.values.working.2 =
        baseContext.context.values.working.2 := by
  change
    (HostStorageDriver.run baseContext executionInputs fuel
      (State.initial writeThenInputSizeProgram.body hostEnvironment)).context.context.values.working.2 = _
  exact HostStorageDriver.run_workingEffects
    baseContext executionInputs fuel _

private theorem run_preserves_other_account (fuel : Nat) :
    (writeThenInputSizeCode.runWithStorage
      baseContext executionInputs fuel).context.context.values.working.1.account?
        otherAddress =
      baseContext.context.values.working.1.account? otherAddress := by
  change
    (HostStorageDriver.run baseContext executionInputs fuel
      (State.initial writeThenInputSizeProgram.body hostEnvironment)).context.context.values.working.1.account? otherAddress = _
  exact HostStorageDriver.run_workingAccount?_of_ne_storageAddress
    baseContext executionInputs fuel _ otherAddress (by decide)

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

def testHostStorageDriverResumption : IO Unit := do
  assertTrue writeThenInputSizeProgram.checkHost
    "the host checker rejected write-then-input-size"

  match firstResult with
  | { context, outcome := .outOfFuel state } =>
      assertTrue (hasCompletedWrite context)
        "fuel 10 exhausted before retaining the working-storage write"
      assertTrue (beforeInputSuffix state)
        "fuel 10 did not stop immediately before the input-sensitive suffix"
      assertTrue (contextPreserved context)
        "the first slice changed checkpoint, effects, or unrelated storage"
  | result =>
      throw (IO.userError
        s!"fuel 10 did not produce the measured exhaustion: {reprStr result.outcome}")

  assertTrue
    (splitResult.outcome ==
      .done (.word threeByteInput.sizeWord) [])
    "same-input resumption returned the wrong value or Store"
  assertTrue
    (oneShotResult.outcome == splitResult.outcome &&
      largerResult.outcome == oneShotResult.outcome)
    "split, one-shot, and larger execution outcomes differed"
  assertTrue
    (hasCompletedWrite splitResult.context &&
      hasCompletedWrite oneShotResult.context &&
      hasCompletedWrite largerResult.context)
    "a completed execution lost the pre-exhaustion write"
  assertTrue
    (contextPreserved splitResult.context &&
      contextPreserved oneShotResult.context &&
      contextPreserved largerResult.context)
    "resumption changed checkpoint, effects, or unrelated storage"

  assertTrue
    (changedInputResume.outcome ==
      .done (.word oneByteInput.sizeWord) [])
    "the deliberately changed-input suffix returned the wrong size"
  assertTrue (changedInputResume.outcome != splitResult.outcome)
    "the concrete changed input did not change the input-sensitive suffix"
  assertTrue
    (hasCompletedWrite changedInputResume.context &&
      contextPreserved changedInputResume.context)
    "the changed-input demonstration lost the retained working context"

end Tests
