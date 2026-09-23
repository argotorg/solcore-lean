import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionPreservationProperties

/-! End-to-end regression for a byte-derived selected-storage write. -/

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

private def observedOffset : Word := ⟨1, by decide⟩
private def observedByte : Word := ⟨0x7b, by decide⟩
private def targetSlot : Word := ⟨0x51, by decide⟩
private def retainedSlot : Word := ⟨0x52, by decide⟩
private def retainedValue : Word := ⟨0x53, by decide⟩
private def oldValue : Word := ⟨0x54, by decide⟩
private def otherSlot : Word := ⟨0x61, by decide⟩
private def otherValue : Word := ⟨0x62, by decide⟩
private def checkpointSlot : Word := ⟨0x71, by decide⟩
private def checkpointValue : Word := ⟨0x72, by decide⟩

private def inputData : HostStorageDriver.InputData := {
  bytes := [0x11, 0x7b, 0x00].toByteArray
  size_lt_wordModulus := by decide
}

private def zeroInputData : HostStorageDriver.InputData := {
  bytes := [0x11, 0x00].toByteArray
  size_lt_wordModulus := by decide
}

private def absentInputData : HostStorageDriver.InputData := {
  bytes := [0x11].toByteArray
  size_lt_wordModulus := by decide
}

private def inputsFor
    (data : HostStorageDriver.InputData) :
    HostStorageDriver.ExecutionInputs := {
  codeAddress := codeAddress
  callValue := Word.zero
  callerAddress := callerAddress
  inputData := data
  currentAddress := codeAddress
}

private def executionInputs : HostStorageDriver.ExecutionInputs :=
  inputsFor inputData

private def zeroExecutionInputs : HostStorageDriver.ExecutionInputs :=
  inputsFor zeroInputData

private def absentExecutionInputs : HostStorageDriver.ExecutionInputs :=
  inputsFor absentInputData

/--
Observe one optional byte. Absence returns the left sentinel. Presence writes the
exact widened byte, observes the same offset again, and returns both values.
-/
private def observeCaseWriteObserveProgram : Program := {
  resultType := .sum .unit (.product .word .word)
  body :=
    .caseE
      (.apply
        (.var HostFunction.inputDataByte?.index)
        (.word observedOffset))
      (.inLeft (.product .word .word) .unit)
      (.letE
        (.apply
          (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word targetSlot) (.var 0)))
        (.caseE
          (.apply
            (.var (HostFunction.inputDataByte?.index + 2))
            (.word observedOffset))
          (.inLeft (.product .word .word) .unit)
          (.inRight .unit (.pair (.var 2) (.var 0)))))
}

private theorem observeCaseWriteObserveProgram_host_checked :
    observeCaseWriteObserveProgram.checkHost = true := by
  decide

private def observeCaseWriteObserveCode : CheckedHostCoreProgram :=
  ⟨observeCaseWriteObserveProgram,
    observeCaseWriteObserveProgram_host_checked⟩

private def selectedStorageAccount : Account :=
  Account.empty
    |>.storageWrite targetSlot oldValue
    |>.storageWrite retainedSlot retainedValue

private def workingWorld : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress
      (Account.empty.withCode observeCaseWriteObserveCode)
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

private def expectedResult (byte : Word) : Value :=
  .inRight .unit (.pair (.word byte) (.word byte))

private def expectedAbsence : Value :=
  .inLeft (.product .word .word) .unit

private def codeProgramIs (state : WorldState) : Bool :=
  match state.code? codeAddress with
  | none => false
  | some code => code.program == observeCaseWriteObserveProgram

private def preservesUnrelated
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat)) :
    Bool :=
  let values := context.context.values
  context.context.storageAddress == storageAddress &&
    codeProgramIs values.working.1 &&
    context.storageAccount.storageValue? retainedSlot == some retainedValue &&
    storageValueAt? values.working.1 storageAddress retainedSlot ==
      some retainedValue &&
    storageValueAt? values.working.1 otherAddress otherSlot == some otherValue &&
    storageValueAt? values.checkpoint.state storageAddress checkpointSlot ==
      some checkpointValue &&
    storageValueAt? values.checkpoint.state otherAddress otherSlot ==
      some otherValue &&
    values.checkpoint.effects.rollback == 11 &&
    values.checkpoint.effects.trace == [12, 13] &&
    values.working.2.rollback == 21 &&
    values.working.2.trace == [22, 23]

private def storesNonzeroByte
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat))
    (byte : Word) : Bool :=
  let working := context.context.values.working.1
  context.storageAccount.storageValue? targetSlot == some byte &&
    storageValueAt? working storageAddress targetSlot == some byte

private def inputDataByteRequestReady (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension =>
      suspension.request == .inputDataByte? observedOffset
  | _ => false

private def oneStepBeforeResult (byte : Word) (state : State) : Bool :=
  match hostAdvance state with
  | .next next => next == State.final (expectedResult byte)
  | _ => false

private theorem observeCaseWriteObserve_done_stable
    {context : HostStorageDriver.Context Nat (List Nat)}
    {finalContext : HostStorageDriver.Context Nat (List Nat)}
    (execution :
      context.runCodeWithStorage? executionInputs 32 =
        some ⟨finalContext, .done (expectedResult observedByte) []⟩) :
    context.runCodeWithStorage? executionInputs 64 =
      some ⟨finalContext, .done (expectedResult observedByte) []⟩ :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
    context executionInputs execution (by decide)

def testAddressSelectedHostInputDataStorage : IO Unit := do
  assertTrue observeCaseWriteObserveProgram.checkHost
    "the host checker rejected observe/case/write/observe"
  assertTrue (inputData.byte? observedOffset == some observedByte)
    "the fixture byte did not widen exactly"

  match baseContext.withPresentStorageAccount? with
  | none =>
      throw (IO.userError "the selected storage Account was absent")
  | some context =>
      match context.runCodeWithStorage? executionInputs 23 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (inputDataByteRequestReady state)
            "fuel 23 did not stop at the second byte observation"
          assertTrue (storesNonzeroByte resultContext observedByte)
            "fuel 23 lost the byte-derived write"
          assertTrue (preservesUnrelated resultContext)
            "fuel 23 changed unrelated context state"
      | some result =>
          throw (IO.userError
            s!"fuel 23 crossed the second observation: {reprStr result.outcome}")
      | none =>
          throw (IO.userError "fuel 23 lost the selected code")

      match context.runCodeWithStorage? executionInputs 31 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (oneStepBeforeResult observedByte state)
            "fuel 31 did not stop one step before the successful pair"
          assertTrue (storesNonzeroByte resultContext observedByte)
            "fuel 31 lost the byte-derived write"
          assertTrue (preservesUnrelated resultContext)
            "fuel 31 changed unrelated context state"
      | some result =>
          throw (IO.userError
            s!"fuel 31 crossed the completion boundary: {reprStr result.outcome}")
      | none =>
          throw (IO.userError "fuel 31 lost the selected code")

      match context.runCodeWithStorage? executionInputs 32,
          context.runCodeWithStorage? executionInputs 64 with
      | some result, some largerResult =>
          assertTrue
            (result.outcome == .done (expectedResult observedByte) [])
            "fuel 32 did not return both equal successful observations"
          assertTrue (largerResult.outcome == result.outcome)
            "additional fuel changed the exact successful result"
          assertTrue (storesNonzeroByte result.context observedByte)
            "completion did not store the widened byte"
          assertTrue (storesNonzeroByte largerResult.context observedByte)
            "larger-fuel completion lost the widened byte"
          assertTrue
            (preservesUnrelated result.context &&
              preservesUnrelated largerResult.context)
            "completion changed unrelated storage or frame fields"
      | none, _ =>
          throw (IO.userError "fuel 32 lost the selected code")
      | _, none =>
          throw (IO.userError "additional fuel lost the selected code")

      match context.runCodeWithStorage? zeroExecutionInputs 32 with
      | some result =>
          assertTrue
            (result.outcome == .done (expectedResult Word.zero) [])
            "a present zero byte followed the absence sentinel branch"
          assertTrue
            ((result.context.storageAccount.storageValue? targetSlot).isNone &&
              result.context.storageAccount.storageRead targetSlot == Word.zero)
            "the present zero byte did not perform the sparse zero write"
          assertTrue (preservesUnrelated result.context)
            "the present-zero run changed unrelated context state"
      | none =>
          throw (IO.userError "the present-zero run lost the selected code")

      match context.runCodeWithStorage? absentExecutionInputs 32 with
      | some result =>
          assertTrue (result.outcome == .done expectedAbsence [])
            "an absent byte did not follow the typed left sentinel branch"
          assertTrue (result.context.storageAccount.storageRead targetSlot == oldValue)
            "the absence branch performed a storage write"
          assertTrue (preservesUnrelated result.context)
            "the absence branch changed unrelated context state"
      | none =>
          throw (IO.userError "the absence run lost the selected code")

end Tests
