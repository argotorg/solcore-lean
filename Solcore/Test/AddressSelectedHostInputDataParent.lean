import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeFrameContinuation
import Solcore.ContractRuntime.ParentIndexedFrameInitialization
import Solcore.ContractRuntime.ParentIndexedFrameResolutionFold

/-! Parent-indexed completion of byte-derived selected-storage execution. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def codeAddress : Address := ⟨0x10, by decide⟩
private def storageAddress : Address := ⟨0x20, by decide⟩
private def callerAddress : Address := ⟨0x40, by decide⟩
private def targetSlot : Word := ⟨0x42, by decide⟩
private def oldValue : Word := ⟨0x51, by decide⟩
private def observedOffset : Word := ⟨0, by decide⟩
private def expectedByte : Word := ⟨0x12, by decide⟩
private def missingSentinel : Word := ⟨0x100, by decide⟩

private def inputData : HostStorageDriver.InputData := {
  bytes := [0x12, 0x00, 0xff].toByteArray
  size_lt_wordModulus := by decide
}

private def executionInputs : HostStorageDriver.ExecutionInputs := {
  codeAddress := codeAddress
  callValue := ⟨0x73, by decide⟩
  callerAddress := callerAddress
  inputData := inputData
  currentAddress := codeAddress
}

/-- Read, case-unpack, write, read again, and retain both exact bytes. -/
private def observeCaseWriteObserveProgram : Program := {
  resultType := .product .word .word
  body :=
    .caseE
      (.apply
        (.var HostFunction.inputDataByte?.index)
        (.word observedOffset))
      (.pair (.word missingSentinel) (.word missingSentinel))
      (.letE
        (.apply
          (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word targetSlot) (.var 0)))
        (.caseE
          (.apply
            (.var (HostFunction.inputDataByte?.index + 2))
            (.word observedOffset))
          (.pair (.var 2) (.word missingSentinel))
          (.pair (.var 2) (.var 0))))
}

private theorem observeCaseWriteObserveProgram_host_checked :
    observeCaseWriteObserveProgram.checkHost = true := by
  decide

private def observeCaseWriteObserveCode : CheckedHostCoreProgram :=
  ⟨observeCaseWriteObserveProgram,
    observeCaseWriteObserveProgram_host_checked⟩

private def storageAccount : Account :=
  Account.empty.storageWrite targetSlot oldValue

private def workingWorld : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress
      (Account.empty.withCode observeCaseWriteObserveCode)
    |>.putAccount storageAddress storageAccount

private def checkpointWorld : WorldState :=
  WorldState.empty.putAccount storageAddress Account.empty

private def parentWorking :
    WorldState × FrameEffectJournal Nat (FrameTrace Nat) :=
  (checkpointWorld, ⟨101, FrameTrace.empty⟩)

private def initialization :
    ParentIndexedFrameInitialization Nat Nat parentWorking := {
  initialWorld := workingWorld
  workingRollback := 201
}

private def missingStorageInitialization :
    ParentIndexedFrameInitialization Nat Nat parentWorking := {
  initialWorld := WorldState.empty.putAccount codeAddress
    (Account.empty.withCode observeCaseWriteObserveCode)
  workingRollback := 201
}

private def missingCodeInitialization :
    ParentIndexedFrameInitialization Nat Nat parentWorking := {
  initialWorld := WorldState.empty.putAccount storageAddress storageAccount
  workingRollback := 201
}

private inductive TrapReason where
  | invalidDoneInputs
  deriving Repr, BEq, DecidableEq

private def terminalBytes : Bytes := [0xa3, 0xb4].toByteArray

private def doneOutcome
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (value : Value)
    (store : Store) : FrameOutcome TrapReason :=
  match value, store with
  | .pair (.word first) (.word second), [] =>
      if first = expectedByte ∧ second = expectedByte ∧
          context.readStorage targetSlot = expectedByte then
        .returned terminalBytes
      else
        .trapped .invalidDoneInputs
  | _, _ => .trapped .invalidDoneInputs

private def storageValueAt?
    (state : WorldState) (address : Address) (slot : Word) : Option Word :=
  (state.account? address).bind fun account => account.storageValue? slot

private def foldResult
    (continuation :
      ParentIndexedFrameContinuationContext
        Nat Nat TrapReason parentWorking) : Option Word × Bytes :=
  continuation.foldResolutionWithTrapRollback
    (fun values data =>
      (storageValueAt? values.1 storageAddress targetSlot, data))
    (fun _ data => (none, data))
    (fun _ _ => (none, ByteArray.empty))

private def inputDataByteRequestReady (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension =>
      suspension.request == .inputDataByte? observedOffset
  | _ => false

private def oneStepBeforeResult (state : State) : Bool :=
  match hostAdvance state with
  | .next next =>
      next == State.final
        (.pair (.word expectedByte) (.word expectedByte))
  | _ => false

/-- The exact parent continuation at fuel 30 survives fuel 32. -/
private theorem parentCompletion_done_stable
    {continuation :
      ParentIndexedFrameContinuationContext
        Nat Nat TrapReason parentWorking}
    (completed :
      initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress executionInputs 30 doneOutcome =
        some (some (some continuation))) :
    initialization.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress executionInputs 32 doneOutcome =
      some (some (some continuation)) :=
  initialization.runCodeWithStorageParentIndexedContinuationContext?_some_some_some_stable
    storageAddress executionInputs doneOutcome completed (by decide)

def testAddressSelectedHostInputDataParent : IO Unit := do
  assertTrue observeCaseWriteObserveProgram.checkHost
    "the host checker rejected the parent input-byte consumer"
  assertTrue (inputData.byte? observedOffset == some expectedByte)
    "the parent fixture did not expose the expected byte"

  match missingStorageInitialization
      |>.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress executionInputs 30 doneOutcome with
  | none => pure ()
  | _ => throw (IO.userError "missing storage crossed the outer Option")

  match missingCodeInitialization
      |>.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress executionInputs 30 doneOutcome with
  | some none => pure ()
  | _ => throw (IO.userError "missing code crossed the middle Option")

  match initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress with
  | none => throw (IO.userError "the parent storage Account was absent")
  | some context =>
      match context.runCodeWithStorage? executionInputs 23 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (inputDataByteRequestReady state)
            "fuel 23 did not stop at the second input-byte request"
          assertTrue
            (resultContext.readStorage targetSlot == expectedByte)
            "fuel 23 lost the byte-derived storage write"
      | _ => throw (IO.userError "fuel 23 crossed its measured boundary")

      match context.runCodeWithStorage? executionInputs 29 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (oneStepBeforeResult state)
            "fuel 29 did not stop one step before the byte pair"
          assertTrue
            (resultContext.readStorage targetSlot == expectedByte)
            "fuel 29 lost the byte-derived storage write"
      | _ => throw (IO.userError "fuel 29 crossed its measured boundary")

  match initialization
      |>.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress executionInputs 29 doneOutcome with
  | some (some none) => pure ()
  | _ => throw (IO.userError "fuel 29 crossed the inner Option")

  match
      initialization.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress executionInputs 30 doneOutcome,
      initialization.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress executionInputs 32 doneOutcome with
  | some (some (some continuation)),
      some (some (some largerContinuation)) =>
      assertTrue
        (foldResult continuation == (some expectedByte, terminalBytes))
        "the parent fold lost byte-derived storage or terminal bytes"
      assertTrue (foldResult largerContinuation == foldResult continuation)
        "fuel 32 changed the exact parent fold result"
      assertTrue
        (largerContinuation.result.outcome == continuation.result.outcome)
        "fuel 32 changed the completed parent outcome"
  | _, _ =>
      throw (IO.userError "input-byte execution did not complete its parent")

end Tests
