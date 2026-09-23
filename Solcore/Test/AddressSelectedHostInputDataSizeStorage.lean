import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionPreservationProperties

/-! End-to-end regression for storing and re-observing exact input size. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def codeAddress : Address := ⟨0x10, by decide⟩
private def storageAddress : Address := ⟨0x20, by decide⟩
private def otherAddress : Address := ⟨0x30, by decide⟩
private def callerAddress : Address := ⟨0x40, by decide⟩
private def targetSlot : Word := ⟨0x51, by decide⟩
private def retainedSlot : Word := ⟨0x52, by decide⟩
private def retainedValue : Word := ⟨0x53, by decide⟩
private def oldValue : Word := ⟨0x54, by decide⟩
private def otherSlot : Word := ⟨0x61, by decide⟩
private def otherValue : Word := ⟨0x62, by decide⟩
private def checkpointSlot : Word := ⟨0x71, by decide⟩
private def checkpointValue : Word := ⟨0x72, by decide⟩

private def threeByteInput : HostStorageDriver.InputData := {
  bytes := [0x11, 0x00, 0xff].toByteArray
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
private def alternateInputs := inputsFor oneByteInput

/-- Observe size, write that exact Word, then observe the same size again. -/
private def observeSizeWriteObserveProgram : Program := {
  resultType := .product .word .word
  body :=
    .letE
      (.apply (.var HostFunction.inputDataSize.index) .unit)
      (.letE
        (.apply
          (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word targetSlot) (.var 0)))
        (.letE
          (.apply
            (.var (HostFunction.inputDataSize.index + 2))
            .unit)
          (.pair (.var 2) (.var 0))))
}

private theorem observeSizeWriteObserveProgram_host_checked :
    observeSizeWriteObserveProgram.checkHost = true := by
  decide

private def observeSizeWriteObserveCode : CheckedHostCoreProgram :=
  ⟨observeSizeWriteObserveProgram,
    observeSizeWriteObserveProgram_host_checked⟩

private def selectedStorageAccount : Account :=
  Account.empty
    |>.storageWrite targetSlot oldValue
    |>.storageWrite retainedSlot retainedValue

private def workingWorld : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress
      (Account.empty.withCode observeSizeWriteObserveCode)
    |>.putAccount storageAddress selectedStorageAccount
    |>.putAccount otherAddress
      (Account.empty.storageWrite otherSlot otherValue)

private def checkpointWorld : WorldState :=
  WorldState.empty
    |>.putAccount storageAddress
      (Account.empty.storageWrite checkpointSlot checkpointValue)
    |>.putAccount otherAddress
      (Account.empty.storageWrite otherSlot otherValue)

private def baseContext :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨storageAddress,
    ⟨⟨checkpointWorld, ⟨11, [12, 13]⟩⟩,
      (workingWorld, ⟨21, [22, 23]⟩)⟩⟩

private def storageValueAt?
    (state : WorldState) (address : Address) (slot : Word) : Option Word :=
  (state.account? address).bind fun account => account.storageValue? slot

private def expectedPair (size : Word) : Value :=
  .pair (.word size) (.word size)

private def codeProgramIs (state : WorldState) : Bool :=
  match state.code? codeAddress with
  | none => false
  | some code => code.program == observeSizeWriteObserveProgram

private def preservesUnrelated
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat)) :
    Bool :=
  let values := context.context.values
  context.context.storageAddress == storageAddress &&
    codeProgramIs values.working.1 &&
    context.storageAccount.storageValue? retainedSlot == some retainedValue &&
    storageValueAt? values.working.1 otherAddress otherSlot == some otherValue &&
    storageValueAt? values.checkpoint.state storageAddress checkpointSlot ==
      some checkpointValue &&
    values.checkpoint.effects.rollback == 11 &&
    values.checkpoint.effects.trace == [12, 13] &&
    values.working.2.rollback == 21 &&
    values.working.2.trace == [22, 23]

private def storesSize
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat))
    (size : Word) : Bool :=
  let working := context.context.values.working.1
  context.storageAccount.storageValue? targetSlot == some size &&
    storageValueAt? working storageAddress targetSlot == some size

private def inputDataSizeRequestReady (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension => suspension.request == .inputDataSize
  | _ => false

private def oneStepBeforeResult (size : Word) (state : State) : Bool :=
  match hostAdvance state with
  | .next next => next == State.final (expectedPair size)
  | _ => false

private theorem observeSizeWriteObserve_done_stable
    {context : HostStorageDriver.Context Nat (List Nat)}
    {finalContext : HostStorageDriver.Context Nat (List Nat)}
    (execution :
      context.runCodeWithStorage? executionInputs 30 =
        some ⟨finalContext, .done (expectedPair threeByteInput.sizeWord) []⟩) :
    context.runCodeWithStorage? executionInputs 32 =
      some ⟨finalContext, .done (expectedPair threeByteInput.sizeWord) []⟩ :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
    context executionInputs execution (by decide)

def testAddressSelectedHostInputDataSizeStorage : IO Unit := do
  assertTrue observeSizeWriteObserveProgram.checkHost
    "the host checker rejected size/write/size"
  assertTrue (threeByteInput.sizeWord == ⟨3, by decide⟩)
    "the three-byte fixture did not retain its exact size"
  assertTrue (oneByteInput.sizeWord == ⟨1, by decide⟩)
    "the one-byte fixture did not retain its exact size"

  match baseContext.withPresentStorageAccount? with
  | none => throw (IO.userError "the selected storage Account was absent")
  | some context =>
      match context.runCodeWithStorage? executionInputs 23 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (inputDataSizeRequestReady state)
            "fuel 23 did not stop at the second input-size request"
          assertTrue (storesSize resultContext threeByteInput.sizeWord)
            "fuel 23 lost the size-derived write"
          assertTrue (preservesUnrelated resultContext)
            "fuel 23 changed unrelated frame state"
      | _ => throw (IO.userError "fuel 23 crossed its measured boundary")

      match context.runCodeWithStorage? executionInputs 29 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (oneStepBeforeResult threeByteInput.sizeWord state)
            "fuel 29 did not stop one step before the size pair"
          assertTrue (storesSize resultContext threeByteInput.sizeWord)
            "fuel 29 lost the size-derived write"
          assertTrue (preservesUnrelated resultContext)
            "fuel 29 changed unrelated frame state"
      | _ => throw (IO.userError "fuel 29 crossed its measured boundary")

      match context.runCodeWithStorage? executionInputs 30,
          context.runCodeWithStorage? executionInputs 32 with
      | some result, some largerResult =>
          assertTrue
            (result.outcome ==
              .done (expectedPair threeByteInput.sizeWord) [])
            "fuel 30 did not return two identical exact sizes"
          assertTrue (largerResult.outcome == result.outcome)
            "additional fuel changed the exact size result"
          assertTrue (storesSize result.context threeByteInput.sizeWord)
            "completion lost the size-derived write"
          assertTrue
            (storesSize largerResult.context threeByteInput.sizeWord)
            "larger-fuel completion lost the size-derived write"
          assertTrue
            (preservesUnrelated result.context &&
              preservesUnrelated largerResult.context)
            "completion changed unrelated frame state"
      | _, _ => throw (IO.userError "size/write/size lost selected code")

      match context.runCodeWithStorage? alternateInputs 30 with
      | some result =>
          assertTrue
            (result.outcome == .done (expectedPair oneByteInput.sizeWord) [])
            "changing only input length returned the wrong size"
          assertTrue (storesSize result.context oneByteInput.sizeWord)
            "changing input length did not change the derived write"
          assertTrue (preservesUnrelated result.context)
            "the alternate size changed unrelated frame state"
      | none => throw (IO.userError "alternate input lost selected code")

end Tests
