import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeFrameContinuation
import Solcore.ContractRuntime.ParentIndexedFrameInitialization
import Solcore.ContractRuntime.ParentIndexedFrameResolutionFold

/-! End-to-end regressions for address-selected storage read/write execution. -/

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
private def alternateCallerAddress : Address := ⟨0x45, by decide⟩
private def maximumAddress : Address := ⟨addressModulus - 1, by decide⟩
private def suppliedCallValue : Word := ⟨0x73, by decide⟩
private def inputData : HostStorageDriver.InputData := {
  bytes := [0x12, 0x00, 0xff].toByteArray
  size_lt_wordModulus := by decide
}

private def inputsFor
    (address : Address) : HostStorageDriver.ExecutionInputs := {
  codeAddress := address
  callValue := suppliedCallValue
  callerAddress := callerAddress
  inputData := inputData
  currentAddress := address
}

private def executionInputs : HostStorageDriver.ExecutionInputs :=
  inputsFor codeAddress

private def alternateCallerInputs : HostStorageDriver.ExecutionInputs :=
  { executionInputs with callerAddress := alternateCallerAddress }

private def expectedStorageAddressWord : Word := ⟨0x20, by decide⟩
private def expectedCodeAddressWord : Word := ⟨0x10, by decide⟩
private def expectedCallerAddressWord : Word := ⟨0x40, by decide⟩
private def expectedAlternateCallerAddressWord : Word := ⟨0x45, by decide⟩
private def expectedMaximumAddressWord : Word :=
  ⟨addressModulus - 1, by decide⟩

private def selectorSlot : Word := ⟨0x41, by decide⟩
private def targetSlot : Word := ⟨0x42, by decide⟩
private def retainedSlot : Word := ⟨0x43, by decide⟩
private def oldValue : Word := ⟨0x51, by decide⟩
private def intermediateValue : Word := ⟨0x54, by decide⟩
private def newValue : Word := ⟨0x52, by decide⟩
private def retainedValue : Word := ⟨0x53, by decide⟩

private def codeSlot : Word := ⟨0x61, by decide⟩
private def codeValue : Word := ⟨0x62, by decide⟩
private def otherSlot : Word := ⟨0x71, by decide⟩
private def otherValue : Word := ⟨0x72, by decide⟩

private def checkpointCodeSlot : Word := ⟨0x81, by decide⟩
private def checkpointCodeValue : Word := ⟨0x82, by decide⟩
private def checkpointStorageSlot : Word := ⟨0x83, by decide⟩
private def checkpointStorageValue : Word := ⟨0x84, by decide⟩
private def checkpointOtherSlot : Word := ⟨0x85, by decide⟩
private def checkpointOtherValue : Word := ⟨0x86, by decide⟩

/--
Allocate a Core-local cell, select a slot through storage, write that slot,
then read the just-written value through the same public host path.
-/
private def storageRoundTripProgram (writtenValue : Word) : Program := {
  resultType := .word
  body :=
    .letE
      (.newCell .bool (.bool true))
      (.letE
        (.apply
          (.var (HostFunction.storageRead.index + 1))
          (.word selectorSlot))
        (.letE
          (.apply
            (.var (HostFunction.storageWrite.index + 2))
            (.pair (.var 0) (.word writtenValue)))
          (.apply
            (.var (HostFunction.storageRead.index + 3))
            (.var 1))))
}

private def updateProgram : Program := storageRoundTripProgram newValue

private theorem updateProgram_host_checked :
    updateProgram.checkHost = true := by
  decide

private def updateCode : CheckedHostCoreProgram :=
  ⟨updateProgram, updateProgram_host_checked⟩

/-- Repeated writes share the one budget and the latest value wins. -/
private def repeatedWriteProgram : Program := {
  resultType := .word
  body :=
    .letE
      (.apply (.var HostFunction.storageRead.index) (.word selectorSlot))
      (.letE
        (.apply
          (.var (HostFunction.storageWrite.index + 1))
          (.pair (.var 0) (.word intermediateValue)))
        (.letE
          (.apply
            (.var (HostFunction.storageWrite.index + 2))
            (.pair (.var 1) (.word newValue)))
          (.apply
            (.var (HostFunction.storageRead.index + 3))
            (.var 2))))
}

private theorem repeatedWriteProgram_host_checked :
    repeatedWriteProgram.checkHost = true := by
  decide

private def repeatedWriteCode : CheckedHostCoreProgram :=
  ⟨repeatedWriteProgram, repeatedWriteProgram_host_checked⟩

private def zeroWriteProgram : Program :=
  {
    resultType := .word
    body :=
      .letE
        (.apply
          (.var HostFunction.storageWrite.index)
          (.pair (.word targetSlot) (.word Word.zero)))
        (.apply
          (.var (HostFunction.storageRead.index + 1))
          (.word targetSlot))
  }

private theorem zeroWriteProgram_host_checked :
    zeroWriteProgram.checkHost = true := by
  decide

private def zeroWriteCode : CheckedHostCoreProgram :=
  ⟨zeroWriteProgram, zeroWriteProgram_host_checked⟩

private def storageAddressProgram : Program := {
  resultType := .word
  body :=
    .apply (.var HostFunction.storageAddress.index) .unit
}

private theorem storageAddressProgram_host_checked :
    storageAddressProgram.checkHost = true := by
  decide

private def storageAddressCode : CheckedHostCoreProgram :=
  ⟨storageAddressProgram, storageAddressProgram_host_checked⟩

private def codeAddressProgram : Program := {
  resultType := .word
  body :=
    .apply (.var HostFunction.codeAddress.index) .unit
}

private theorem codeAddressProgram_host_checked :
    codeAddressProgram.checkHost = true := by
  decide

private def codeAddressCode : CheckedHostCoreProgram :=
  ⟨codeAddressProgram, codeAddressProgram_host_checked⟩

private def callValueProgram : Program := {
  resultType := .word
  body :=
    .apply (.var HostFunction.callValue.index) .unit
}

private theorem callValueProgram_host_checked :
    callValueProgram.checkHost = true := by
  decide

private def callValueCode : CheckedHostCoreProgram :=
  ⟨callValueProgram, callValueProgram_host_checked⟩

private def callerAddressProgram : Program := {
  resultType := .word
  body := .apply (.var HostFunction.callerAddress.index) .unit
}

private theorem callerAddressProgram_host_checked :
    callerAddressProgram.checkHost = true := by
  decide

private def callerAddressCode : CheckedHostCoreProgram :=
  ⟨callerAddressProgram, callerAddressProgram_host_checked⟩

/-- Observe the selector, write its storage, then observe it again. -/
private def observeWriteObserveProgram : Program := {
  resultType := .product .word .word
  body :=
    .letE
      (.apply (.var HostFunction.storageAddress.index) .unit)
      (.letE
        (.apply
          (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word targetSlot) (.word newValue)))
        (.letE
          (.apply
            (.var (HostFunction.storageAddress.index + 2))
            .unit)
          (.pair (.var 2) (.var 0))))
}

private theorem observeWriteObserveProgram_host_checked :
    observeWriteObserveProgram.checkHost = true := by
  decide

private def observeWriteObserveCode : CheckedHostCoreProgram :=
  ⟨observeWriteObserveProgram, observeWriteObserveProgram_host_checked⟩

private def expectedStorageAddressPair : Value :=
  .pair (.word expectedStorageAddressWord) (.word expectedStorageAddressWord)

/-- Observe the code selector, write storage, then observe it again. -/
private def observeCodeWriteObserveCodeProgram : Program := {
  resultType := .product .word .word
  body :=
    .letE
      (.apply (.var HostFunction.codeAddress.index) .unit)
      (.letE
        (.apply
          (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word targetSlot) (.word newValue)))
        (.letE
          (.apply
            (.var (HostFunction.codeAddress.index + 2))
            .unit)
          (.pair (.var 2) (.var 0))))
}

private theorem observeCodeWriteObserveCodeProgram_host_checked :
    observeCodeWriteObserveCodeProgram.checkHost = true := by
  decide

private def observeCodeWriteObserveCode : CheckedHostCoreProgram :=
  ⟨observeCodeWriteObserveCodeProgram,
    observeCodeWriteObserveCodeProgram_host_checked⟩

private def expectedCodeAddressPair : Value :=
  .pair (.word expectedCodeAddressWord) (.word expectedCodeAddressWord)

/-- Observe call value, write that exact Word, then observe it again. -/
private def observeCallValueWriteObserveProgram : Program := {
  resultType := .product .word .word
  body :=
    .letE
      (.apply (.var HostFunction.callValue.index) .unit)
      (.letE
        (.apply
          (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word targetSlot) (.var 0)))
        (.letE
          (.apply
            (.var (HostFunction.callValue.index + 2))
            .unit)
          (.pair (.var 2) (.var 0))))
}

private theorem observeCallValueWriteObserveProgram_host_checked :
    observeCallValueWriteObserveProgram.checkHost = true := by
  decide

private def observeCallValueWriteObserveCode : CheckedHostCoreProgram :=
  ⟨observeCallValueWriteObserveProgram,
    observeCallValueWriteObserveProgram_host_checked⟩

private def expectedCallValuePair : Value :=
  .pair (.word suppliedCallValue) (.word suppliedCallValue)

/-- Observe the caller, write its widened Word, then observe it again. -/
private def observeCallerWriteObserveProgram : Program := {
  resultType := .product .word .word
  body :=
    .letE
      (.apply (.var HostFunction.callerAddress.index) .unit)
      (.letE
        (.apply
          (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word targetSlot) (.var 0)))
        (.letE
          (.apply
            (.var (HostFunction.callerAddress.index + 2))
            .unit)
          (.pair (.var 2) (.var 0))))
}

private theorem observeCallerWriteObserveProgram_host_checked :
    observeCallerWriteObserveProgram.checkHost = true := by
  decide

private def observeCallerWriteObserveCode : CheckedHostCoreProgram :=
  ⟨observeCallerWriteObserveProgram,
    observeCallerWriteObserveProgram_host_checked⟩

private def expectedCallerAddressPair : Value :=
  .pair (.word expectedCallerAddressWord) (.word expectedCallerAddressWord)

private def callValueFrameData : Bytes := [0xd5, 0xe6].toByteArray
private def callerFrameData : Bytes := [0xd7, 0xe8].toByteArray

private def codeAccountFor (code : CheckedHostCoreProgram) : Account :=
  Account.empty
    |>.storageWrite codeSlot codeValue
    |>.withCode code

private def selectedStorageAccount : Account :=
  Account.empty
    |>.storageWrite selectorSlot targetSlot
    |>.storageWrite targetSlot oldValue
    |>.storageWrite retainedSlot retainedValue

private def otherWorkingAccount : Account :=
  Account.empty.storageWrite otherSlot otherValue

private def workingWorldFor (code : CheckedHostCoreProgram) : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress (codeAccountFor code)
    |>.putAccount storageAddress selectedStorageAccount
    |>.putAccount otherAddress otherWorkingAccount

private def checkpointWorld : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress
      (Account.empty.storageWrite checkpointCodeSlot checkpointCodeValue)
    |>.putAccount storageAddress
      (Account.empty.storageWrite
        checkpointStorageSlot checkpointStorageValue)
    |>.putAccount otherAddress
      (Account.empty.storageWrite checkpointOtherSlot checkpointOtherValue)

private def checkpointEffects : FrameEffectJournal Nat (List Nat) :=
  ⟨101, [102, 103]⟩

private def workingEffects : FrameEffectJournal Nat (List Nat) :=
  ⟨201, [202, 203]⟩

private inductive FrameAdapterTrapReason where
  | invalidDoneInputs
  | policyTrap
  deriving Repr, BEq, DecidableEq

private def frameReturnData : Bytes := [0xa1, 0xb2].toByteArray
private def frameRevertData : Bytes := [0xc1, 0xd2].toByteArray

/--
Classify completion as a return only when the terminal handler context, Core
value, and Core-local store are all the measured post-write values.
-/
private def returnedDoneOutcome
    (context : HostStorageDriver.Context Nat (List Nat))
    (value : Value)
    (store : Store) : FrameOutcome FrameAdapterTrapReason :=
  match value, store with
  | .word returned, [.bool true] =>
      if returned = newValue ∧ context.readStorage targetSlot = newValue then
        .returned frameReturnData
      else
        .trapped .invalidDoneInputs
  | _, _ => .trapped .invalidDoneInputs

private def revertedDoneOutcome
    (_ : HostStorageDriver.Context Nat (List Nat))
    (_ : Value)
    (_ : Store) : FrameOutcome FrameAdapterTrapReason :=
  .reverted frameRevertData

private def trappedDoneOutcome
    (_ : HostStorageDriver.Context Nat (List Nat))
    (_ : Value)
    (_ : Store) : FrameOutcome FrameAdapterTrapReason :=
  .trapped .policyTrap

private def baseContextFor (code : CheckedHostCoreProgram) :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨storageAddress,
    ⟨⟨checkpointWorld, checkpointEffects⟩,
      (workingWorldFor code, workingEffects)⟩⟩

private def storageValueAt?
    (state : WorldState) (address : Address) (slot : Word) : Option Word :=
  (state.account? address).bind fun account => account.storageValue? slot

private def callValueParentWorking :
    WorldState × FrameEffectJournal Nat (FrameTrace Nat) :=
  (checkpointWorld, ⟨101, FrameTrace.empty⟩)

private def callValueInitialization :
    ParentIndexedFrameInitialization Nat Nat callValueParentWorking := {
  initialWorld := workingWorldFor observeCallValueWriteObserveCode
  workingRollback := 201
}

private def callValueDoneOutcome
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (value : Value)
    (store : Store) : FrameOutcome FrameAdapterTrapReason :=
  match value, store with
  | .pair (.word first) (.word second), [] =>
      if first = suppliedCallValue ∧ second = suppliedCallValue ∧
          context.readStorage targetSlot = suppliedCallValue then
        .returned callValueFrameData
      else
        .trapped .invalidDoneInputs
  | _, _ => .trapped .invalidDoneInputs

private def callValueFoldResult
    (continuation :
      ParentIndexedFrameContinuationContext
        Nat Nat FrameAdapterTrapReason callValueParentWorking) :
    Option Word × Bytes :=
  continuation.foldResolutionWithTrapRollback
    (fun values data =>
      (storageValueAt? values.1 storageAddress targetSlot, data))
    (fun _ data => (none, data))
    (fun _ _ => (none, ByteArray.empty))

private def callerParentWorking :
    WorldState × FrameEffectJournal Nat (FrameTrace Nat) :=
  (checkpointWorld, ⟨101, FrameTrace.empty⟩)

private def callerInitialization :
    ParentIndexedFrameInitialization Nat Nat callerParentWorking := {
  initialWorld := workingWorldFor observeCallerWriteObserveCode
  workingRollback := 201
}

private def callerDoneOutcome
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (value : Value)
    (store : Store) : FrameOutcome FrameAdapterTrapReason :=
  match value, store with
  | .pair (.word first) (.word second), [] =>
      if first = expectedCallerAddressWord ∧
          second = expectedCallerAddressWord ∧
          context.readStorage targetSlot = expectedCallerAddressWord then
        .returned callerFrameData
      else
        .trapped .invalidDoneInputs
  | _, _ => .trapped .invalidDoneInputs

private def callerFoldResult
    (continuation :
      ParentIndexedFrameContinuationContext
        Nat Nat FrameAdapterTrapReason callerParentWorking) :
    Option Word × Bytes :=
  continuation.foldResolutionWithTrapRollback
    (fun values data =>
      (storageValueAt? values.1 storageAddress targetSlot, data))
    (fun _ data => (none, data))
    (fun _ _ => (none, ByteArray.empty))

private def codeProgramIs
    (state : WorldState) (address : Address) (program : Program) : Bool :=
  match state.code? address with
  | none => false
  | some code => code.program == program

private def preservedOutsideSelectedStorage
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat))
    (program : Program) : Bool :=
  let values := context.context.values
  context.context.storageAddress == storageAddress &&
    codeProgramIs values.working.1 codeAddress program &&
    storageValueAt? values.working.1 codeAddress codeSlot == some codeValue &&
    storageValueAt? values.working.1 otherAddress otherSlot ==
      some otherValue &&
    storageValueAt? values.checkpoint.state codeAddress checkpointCodeSlot ==
      some checkpointCodeValue &&
    storageValueAt? values.checkpoint.state
      storageAddress checkpointStorageSlot == some checkpointStorageValue &&
    storageValueAt? values.checkpoint.state otherAddress checkpointOtherSlot ==
      some checkpointOtherValue &&
    values.checkpoint.effects.rollback == 101 &&
    values.checkpoint.effects.trace == [102, 103] &&
    values.working.2.rollback == 201 &&
    values.working.2.trace == [202, 203]

private def selectedStorageHas
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat))
    (value : Word) : Bool :=
  let working := context.context.values.working.1
  context.storageAccount.storageValue? targetSlot == some value &&
    storageValueAt? working storageAddress targetSlot == some value &&
    context.storageAccount.storageRead selectorSlot == targetSlot &&
    context.storageAccount.storageRead retainedSlot == retainedValue &&
    storageValueAt? working storageAddress retainedSlot == some retainedValue

private def selectedTargetMissing
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat)) :
    Bool :=
  let working := context.context.values.working.1
  (working.account? storageAddress).isSome &&
    (context.storageAccount.storageValue? targetSlot).isNone &&
    (storageValueAt? working storageAddress targetSlot).isNone &&
    context.storageAccount.storageRead targetSlot == Word.zero &&
    context.storageAccount.storageRead selectorSlot == targetSlot &&
    context.storageAccount.storageRead retainedSlot == retainedValue

private def accountAbsentAt
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat))
    (address : Address) : Bool :=
  (context.context.values.working.1.account? address).isNone &&
    (context.context.values.checkpoint.state.account? address).isNone

private def storageAddressRequestReady (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension => suspension.request == .storageAddress
  | _ => false

private def codeAddressRequestReady (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension => suspension.request == .codeAddress
  | _ => false

private def callValueRequestReady (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension => suspension.request == .callValue
  | _ => false

private def callerAddressRequestReady (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension => suspension.request == .callerAddress
  | _ => false

private def oneStepBeforeStorageAddressPair (state : State) : Bool :=
  match hostAdvance state with
  | .next next => next == State.final expectedStorageAddressPair
  | _ => false

private def oneStepBeforeCodeAddressPair (state : State) : Bool :=
  match hostAdvance state with
  | .next next => next == State.final expectedCodeAddressPair
  | _ => false

private def oneStepBeforeCallValuePair (state : State) : Bool :=
  match hostAdvance state with
  | .next next => next == State.final expectedCallValuePair
  | _ => false

private def oneStepBeforeCallerAddressPair (state : State) : Bool :=
  match hostAdvance state with
  | .next next => next == State.final expectedCallerAddressPair
  | _ => false

private def assertFixtureContext
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat))
    (program : Program)
    (targetValue : Word)
    (label : String) : IO Unit := do
  assertTrue (selectedStorageHas context targetValue)
    s!"{label} changed the selected storage unexpectedly"
  assertTrue (preservedOutsideSelectedStorage context program)
    s!"{label} changed a retained frame observation"

private def completionFuel : Nat := 28
private def zeroCompletionFuel : Nat := 16
private def storageAddressCompletionFuel : Nat := 5
private def codeAddressCompletionFuel : Nat := 5
private def callValueCompletionFuel : Nat := 5
private def observeWriteObserveSecondRequestFuel : Nat := 23
private def observeWriteObserveCompletionFuel : Nat := 30

private inductive MixedBoundary where
  | beforeWrite
  | afterWrite
  | beforeFinalRead

private def atMixedBoundary (boundary : MixedBoundary) (state : State) : Bool :=
  match boundary with
  | .beforeWrite =>
      match hostAdvance state with
      | .suspended suspension =>
          suspension.request == .storageWrite targetSlot newValue
      | _ => false
  | .afterWrite => state.control == .ret .unit
  | .beforeFinalRead =>
      match hostAdvance state with
      | .suspended suspension =>
          suspension.request == .storageRead targetSlot
      | _ => false

private def assertMixedOutOfFuelAt
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat))
    (fuel : Nat)
    (expectedValue : Word)
    (boundary : MixedBoundary) : IO Unit := do
  match context.runCodeWithStorage? executionInputs fuel with
  | none =>
      throw (IO.userError s!"fuel {fuel} lost the selected code")
  | some { context := resultContext, outcome := .outOfFuel state } =>
      assertTrue (selectedStorageHas resultContext expectedValue)
        s!"fuel {fuel} returned the wrong selected storage context"
      assertTrue (atMixedBoundary boundary state)
        s!"fuel {fuel} stopped at the wrong Core boundary"
      assertTrue
        (preservedOutsideSelectedStorage resultContext updateProgram)
        s!"fuel {fuel} changed retained frame data"
  | some result =>
      throw (IO.userError
        s!"fuel {fuel} crossed the measured boundary: {reprStr result.outcome}")

private def assertReturnedFrameResolution
    (continuation :
      FrameContinuationContext Nat (List Nat) FrameAdapterTrapReason)
    (label : String) : IO Unit := do
  match continuation.resolve with
  | .returned state effects data =>
      assertTrue
        (storageValueAt? state storageAddress targetSlot == some newValue)
        s!"{label} did not resolve the post-write working state"
      assertTrue (effects.rollback == workingEffects.rollback)
        s!"{label} did not retain the working rollback value"
      assertTrue (effects.trace == workingEffects.trace)
        s!"{label} did not retain the working trace"
      assertTrue (data == frameReturnData)
        s!"{label} returned the wrong frame data"
  | _ =>
      throw (IO.userError
        s!"{label} did not resolve as a returned frame")

private def assertRevertedFrameResolution
    (continuation :
      FrameContinuationContext Nat (List Nat) FrameAdapterTrapReason) :
    IO Unit := do
  match continuation.resolve with
  | .reverted state effects data =>
      assertTrue
        (storageValueAt? state storageAddress checkpointStorageSlot ==
          some checkpointStorageValue)
        "revert did not resolve the checkpoint WorldState"
      assertTrue
        (storageValueAt? state storageAddress targetSlot).isNone
        "revert leaked the speculative working-storage write"
      assertTrue (effects.rollback == checkpointEffects.rollback)
        "revert did not restore the checkpoint rollback value"
      assertTrue (effects.trace == workingEffects.trace)
        "revert did not retain the working trace"
      assertTrue (data == frameRevertData)
        "revert resolved the wrong frame data"
  | _ =>
      throw (IO.userError "the revert policy did not resolve as reverted")

private def assertTrappedFrameResolution
    (continuation :
      FrameContinuationContext Nat (List Nat) FrameAdapterTrapReason) :
    IO Unit := do
  match continuation.resolve with
  | .trapped .policyTrap => pure ()
  | _ =>
      throw (IO.userError "the trap policy did not retain its exact reason")

/-- Exercise all three optional layers without duplicating the storage fixture. -/
private def assertFrameContinuationAdapter
    (context : HostStorageDriver.Context Nat (List Nat)) : IO Unit := do
  match context.runCodeWithStorageContinuationContext?
      (inputsFor maximumAddress) completionFuel returnedDoneOutcome with
  | none => pure ()
  | some _ =>
      throw (IO.userError
        "missing code did not remain an outer continuation failure")

  match context.runCodeWithStorageContinuationContext?
      executionInputs 22 returnedDoneOutcome with
  | some none => pure ()
  | none =>
      throw (IO.userError
        "fuel 22 confused selected exhaustion with missing code")
  | some (some _) =>
      throw (IO.userError
        "fuel 22 constructed a continuation before completion")

  match context.runCodeWithStorageContinuationContext?
        executionInputs completionFuel returnedDoneOutcome,
      context.runCodeWithStorageContinuationContext?
        executionInputs completionFuel revertedDoneOutcome,
      context.runCodeWithStorageContinuationContext?
        executionInputs completionFuel trappedDoneOutcome,
      context.runCodeWithStorageContinuationContext?
        executionInputs 64 returnedDoneOutcome with
  | some (some returned), some (some reverted), some (some trapped),
      some (some largerReturned) =>
      assertReturnedFrameResolution returned "fuel 28 frame adapter"
      assertRevertedFrameResolution reverted
      assertTrappedFrameResolution trapped
      assertReturnedFrameResolution largerReturned "fuel 64 frame adapter"
  | _, _, _, _ =>
      throw (IO.userError
        "completed selected execution did not construct every continuation")

private def assertCompletedWriteResult
    (result :
      HostDriverResult
        (FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat)))
    (program : Program)
    (localStore : Store)
    (label : String) : IO Unit := do
  assertTrue (result.outcome == .done (.word newValue) localStore)
    s!"{label} lost the latest value or Core-local store"
  assertTrue (selectedStorageHas result.context newValue)
    s!"{label} did not retain the latest selected-storage write"
  assertTrue (preservedOutsideSelectedStorage result.context program)
    s!"{label} changed a retained frame observation"

/--
The public selected-run stability theorem applies to the concrete
read/write/read fixture and retains its exact post-write context.
-/
private theorem updateProgram_done_stable
    {context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat)}
    (selected :
      (baseContextFor updateCode).withPresentStorageAccount? = some context)
    {finalContext :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat)}
    (execution :
      context.runCodeWithStorage? executionInputs completionFuel =
        some ⟨finalContext,
          .done (.word newValue) [.bool true]⟩)
    (written : finalContext.storageAccount.storageRead targetSlot = newValue) :
    (baseContextFor updateCode).withPresentStorageAccount? = some context ∧
      context.runCodeWithStorage? executionInputs 64 =
        some ⟨finalContext,
          .done (.word newValue) [.bool true]⟩ ∧
      finalContext.storageAccount.storageRead targetSlot = newValue := by
  exact ⟨selected,
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
      context executionInputs execution (by decide),
    written⟩

/-- The exact nested continuation produced at fuel 28 survives fuel 64. -/
private theorem updateProgram_frameContinuation_done_stable
    {context : HostStorageDriver.Context Nat (List Nat)}
    {continuation :
      FrameContinuationContext Nat (List Nat) FrameAdapterTrapReason}
    (completed :
      context.runCodeWithStorageContinuationContext?
        executionInputs completionFuel returnedDoneOutcome =
          some (some continuation)) :
    context.runCodeWithStorageContinuationContext?
      executionInputs 64 returnedDoneOutcome = some (some continuation) := by
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_some_some_stable
      context executionInputs returnedDoneOutcome completed (by decide)

/-- The selected public stability theorem applies to the mixed fixture. -/
private theorem observeWriteObserveProgram_done_stable
    {context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat)}
    (selected :
      (baseContextFor observeWriteObserveCode).withPresentStorageAccount? =
        some context)
    {finalContext :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat)}
    (execution :
      context.runCodeWithStorage? executionInputs
          observeWriteObserveCompletionFuel =
        some ⟨finalContext, .done expectedStorageAddressPair []⟩) :
    (baseContextFor observeWriteObserveCode).withPresentStorageAccount? =
        some context ∧
      context.runCodeWithStorage? executionInputs 64 =
        some ⟨finalContext, .done expectedStorageAddressPair []⟩ := by
  exact ⟨selected,
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
      context executionInputs execution (by decide)⟩

/-- The selected code observation retains its exact result with more fuel. -/
private theorem codeAddressProgram_done_stable
    {context : HostStorageDriver.Context Nat (List Nat)}
    (selected :
      (baseContextFor codeAddressCode).withPresentStorageAccount? =
        some context)
    {finalContext : HostStorageDriver.Context Nat (List Nat)}
    (execution :
      context.runCodeWithStorage? executionInputs
          codeAddressCompletionFuel =
        some ⟨finalContext, .done (.word expectedCodeAddressWord) []⟩) :
    (baseContextFor codeAddressCode).withPresentStorageAccount? =
        some context ∧
      context.runCodeWithStorage? executionInputs 32 =
        some ⟨finalContext, .done (.word expectedCodeAddressWord) []⟩ := by
  exact ⟨selected,
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
      context executionInputs execution (by decide)⟩

/-- The supplied call value and exact terminal context survive larger fuel. -/
private theorem callValueProgram_done_stable
    {context : HostStorageDriver.Context Nat (List Nat)}
    (selected :
      (baseContextFor callValueCode).withPresentStorageAccount? =
        some context)
    {finalContext : HostStorageDriver.Context Nat (List Nat)}
    (execution :
      context.runCodeWithStorage? executionInputs callValueCompletionFuel =
        some ⟨finalContext, .done (.word suppliedCallValue) []⟩) :
    (baseContextFor callValueCode).withPresentStorageAccount? =
        some context ∧
      context.runCodeWithStorage? executionInputs 32 =
        some ⟨finalContext, .done (.word suppliedCallValue) []⟩ := by
  exact ⟨selected,
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
      context executionInputs execution (by decide)⟩

/-- The widened caller and terminal context survive larger fuel. -/
private theorem callerAddressProgram_done_stable
    {context : HostStorageDriver.Context Nat (List Nat)}
    (selected :
      (baseContextFor callerAddressCode).withPresentStorageAccount? =
        some context)
    {finalContext : HostStorageDriver.Context Nat (List Nat)}
    (execution :
      context.runCodeWithStorage? executionInputs 5 =
        some ⟨finalContext, .done (.word expectedCallerAddressWord) []⟩) :
    (baseContextFor callerAddressCode).withPresentStorageAccount? =
        some context ∧
      context.runCodeWithStorage? executionInputs 32 =
        some ⟨finalContext, .done (.word expectedCallerAddressWord) []⟩ := by
  exact ⟨selected,
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
      context executionInputs execution (by decide)⟩

/-- Caller variation changes the response but preserves the exact host context. -/
private theorem callerAddress_handling_context_independent
    (context : HostStorageDriver.Context Nat (List Nat))
    (continuation : List Frame) (store : Store) :
    (HostStorageDriver.handleSuspension executionInputs context
        ⟨.callerAddress, continuation, store⟩).1 =
      (HostStorageDriver.handleSuspension alternateCallerInputs context
        ⟨.callerAddress, continuation, store⟩).1 := by
  simp

private theorem callerAddress_runWithStorage_preserves_context
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs) :
    (callerAddressCode.runWithStorage context inputs 5).context = context := by
  unfold CheckedHostCoreProgram.runWithStorage
  change
    (HostStorageDriver.run context inputs 5
      (State.initial callerAddressProgram.body hostEnvironment)).context = context
  have suspended :
      hostRun 5 (State.initial callerAddressProgram.body hostEnvironment) =
        .suspended ⟨.callerAddress, [], []⟩ 0 := by
    decide
  rw [HostStorageDriver.run_of_suspended_callerAddress
    context inputs 5 0 _ [] [] suspended]
  change
    (HostStorageDriver.run context inputs 0
      (State.final (.word (addressToWord inputs.callerAddress)))).context = context
  have completed :
      hostRun 0
          (State.final (.word (addressToWord inputs.callerAddress))) =
        .done (.word (addressToWord inputs.callerAddress)) [] := by
    rfl
  rw [HostStorageDriver.run_of_done context inputs 0
    (State.final (.word (addressToWord inputs.callerAddress)))
    (.word (addressToWord inputs.callerAddress)) [] completed]

/-- Changing only the caller changes no part of the completed driver context. -/
private theorem callerAddress_run_context_independent
    (context : HostStorageDriver.Context Nat (List Nat)) :
    (callerAddressCode.runWithStorage context executionInputs 5).context =
      (callerAddressCode.runWithStorage context alternateCallerInputs 5).context :=
  (callerAddress_runWithStorage_preserves_context context executionInputs).trans
    (callerAddress_runWithStorage_preserves_context
      context alternateCallerInputs).symm

/-- The value-derived write and both observations survive larger fuel. -/
private theorem observeCallValueWriteObserveProgram_done_stable
    {context : HostStorageDriver.Context Nat (List Nat)}
    (selected :
      (baseContextFor observeCallValueWriteObserveCode).withPresentStorageAccount? =
        some context)
    {finalContext : HostStorageDriver.Context Nat (List Nat)}
    (execution :
      context.runCodeWithStorage? executionInputs
          observeWriteObserveCompletionFuel =
        some ⟨finalContext, .done expectedCallValuePair []⟩) :
    (baseContextFor observeCallValueWriteObserveCode).withPresentStorageAccount? =
        some context ∧
      context.runCodeWithStorage? executionInputs 32 =
        some ⟨finalContext, .done expectedCallValuePair []⟩ := by
  exact ⟨selected,
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
      context executionInputs execution (by decide)⟩

/-- The caller-derived write and both observations survive larger fuel. -/
private theorem observeCallerWriteObserveProgram_done_stable
    {context : HostStorageDriver.Context Nat (List Nat)}
    (selected :
      (baseContextFor observeCallerWriteObserveCode).withPresentStorageAccount? =
        some context)
    {finalContext : HostStorageDriver.Context Nat (List Nat)}
    (execution :
      context.runCodeWithStorage? executionInputs 30 =
        some ⟨finalContext, .done expectedCallerAddressPair []⟩) :
    (baseContextFor observeCallerWriteObserveCode).withPresentStorageAccount? =
        some context ∧
      context.runCodeWithStorage? executionInputs 32 =
        some ⟨finalContext, .done expectedCallerAddressPair []⟩ := by
  exact ⟨selected,
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
      context executionInputs execution (by decide)⟩

/-- Parent-indexed completion retains the exact context at fuel 32. -/
private theorem callValueParentCompletion_done_stable
    {continuation :
      ParentIndexedFrameContinuationContext
        Nat Nat FrameAdapterTrapReason callValueParentWorking}
    (completed :
      callValueInitialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress executionInputs observeWriteObserveCompletionFuel
          callValueDoneOutcome =
        some (some (some continuation))) :
    callValueInitialization.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress executionInputs 32 callValueDoneOutcome =
      some (some (some continuation)) :=
  callValueInitialization.runCodeWithStorageParentIndexedContinuationContext?_some_some_some_stable
    storageAddress executionInputs callValueDoneOutcome completed (by decide)

/-- Caller-derived parent completion retains its exact context at fuel 32. -/
private theorem callerParentCompletion_done_stable
    {continuation :
      ParentIndexedFrameContinuationContext
        Nat Nat FrameAdapterTrapReason callerParentWorking}
    (completed :
      callerInitialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress executionInputs 30 callerDoneOutcome =
        some (some (some continuation))) :
    callerInitialization.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress executionInputs 32 callerDoneOutcome =
      some (some (some continuation)) :=
  callerInitialization.runCodeWithStorageParentIndexedContinuationContext?_some_some_some_stable
    storageAddress executionInputs callerDoneOutcome completed (by decide)

def testAddressSelectedHostStorage : IO Unit := do
  assertTrue updateProgram.checkHost
    "the host checker rejected the read/write/read program"
  assertTrue repeatedWriteProgram.checkHost
    "the host checker rejected repeated writes"
  assertTrue zeroWriteProgram.checkHost
    "the host checker rejected the sparse-zero program"
  assertTrue storageAddressProgram.checkHost
    "the host checker rejected the storage-address program"
  assertTrue codeAddressProgram.checkHost
    "the host checker rejected the code-address program"
  assertTrue callValueProgram.checkHost
    "the host checker rejected the call-value program"
  assertTrue callerAddressProgram.checkHost
    "the host checker rejected the caller-address program"
  assertTrue observeWriteObserveProgram.checkHost
    "the host checker rejected observe/write/observe"
  assertTrue observeCodeWriteObserveCodeProgram.checkHost
    "the host checker rejected code-observe/write/code-observe"
  assertTrue observeCallValueWriteObserveProgram.checkHost
    "the host checker rejected call-value/write/call-value"
  assertTrue observeCallerWriteObserveProgram.checkHost
    "the host checker rejected caller/write/caller"
  assertTrue (codeAddress != storageAddress)
    "the address fixture did not separate code and storage"
  assertTrue
    (suppliedCallValue != expectedCodeAddressWord &&
      suppliedCallValue != expectedStorageAddressWord)
    "the call-value fixture did not separate all three observations"
  assertTrue
    (expectedCallerAddressWord != expectedCodeAddressWord &&
      expectedCallerAddressWord != expectedStorageAddressWord &&
      expectedCallerAddressWord != suppliedCallValue)
    "the caller fixture did not separate every runtime role"
  assertTrue (addressToWord callerAddress == expectedCallerAddressWord)
    "the caller Address did not widen exactly"
  assertTrue (wordToAddress? expectedCallerAddressWord == some callerAddress)
    "the widened caller Address did not narrow exactly"
  assertTrue (addressToWord storageAddress == expectedStorageAddressWord)
    "the retained nontrivial Address did not widen exactly"
  assertTrue (addressToWord codeAddress == expectedCodeAddressWord)
    "the selected code Address did not widen exactly"
  assertTrue (wordToAddress? expectedCodeAddressWord == some codeAddress)
    "the selected code Address did not survive strict narrowing"
  assertTrue
    (wordToAddress? expectedStorageAddressWord == some storageAddress)
    "the retained nontrivial Address did not survive strict narrowing"
  assertTrue (addressToWord maximumAddress == expectedMaximumAddressWord)
    "the maximum Address did not widen exactly"
  assertTrue (wordToAddress? expectedMaximumAddressWord == some maximumAddress)
    "the maximum Address did not survive strict narrowing"

  match (baseContextFor storageAddressCode).withPresentStorageAccount? with
  | none =>
      throw (IO.userError "the storage-address Account was absent")
  | some context =>
      match context.runCodeWithStorage? executionInputs 4 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (storageAddressRequestReady state)
            "fuel 4 did not stop at the storage-address request"
          assertFixtureContext resultContext storageAddressProgram oldValue
            "fuel 4 storage-address observation"
      | some result =>
          throw (IO.userError
            s!"fuel 4 crossed the address boundary: {reprStr result.outcome}")
      | none =>
          throw (IO.userError "fuel 4 lost the storage-address code")

      match context.runCodeWithStorage?
          executionInputs storageAddressCompletionFuel,
          context.runCodeWithStorage? executionInputs 32 with
      | some result, some largerResult =>
          assertTrue
            (result.outcome == .done (.word expectedStorageAddressWord) [])
            "fuel 5 returned the wrong storage Address"
          assertTrue
            (result.outcome != .done (.word (addressToWord codeAddress)) [])
            "storage-address observation returned the code Address"
          assertTrue (largerResult.outcome == result.outcome)
            "additional fuel changed storage-address observation"
          assertFixtureContext result.context storageAddressProgram oldValue
            "fuel 5 storage-address observation"
          assertFixtureContext largerResult.context storageAddressProgram oldValue
            "fuel 32 storage-address observation"
      | none, _ =>
          throw (IO.userError "fuel 5 lost the storage-address code")
      | _, none =>
          throw (IO.userError "additional fuel lost the storage-address code")

  match (baseContextFor codeAddressCode).withPresentStorageAccount? with
  | none =>
      throw (IO.userError "the code-address storage Account was absent")
  | some context =>
      match context.runCodeWithStorage? executionInputs 4 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (codeAddressRequestReady state)
            "fuel 4 did not stop at the code-address request"
          assertFixtureContext resultContext codeAddressProgram oldValue
            "fuel 4 code-address observation"
      | some result =>
          throw (IO.userError
            s!"fuel 4 crossed the code-address boundary: {reprStr result.outcome}")
      | none =>
          throw (IO.userError "fuel 4 lost the code-address code")

      match context.runCodeWithStorage?
          executionInputs codeAddressCompletionFuel,
          context.runCodeWithStorage? executionInputs 32 with
      | some result, some largerResult =>
          assertTrue
            (result.outcome == .done (.word expectedCodeAddressWord) [])
            "fuel 5 returned the wrong code Address"
          assertTrue
            (result.outcome != .done (.word expectedStorageAddressWord) [])
            "code-address observation returned the storage Address"
          assertTrue (largerResult.outcome == result.outcome)
            "additional fuel changed code-address observation"
          assertFixtureContext result.context codeAddressProgram oldValue
            "fuel 5 code-address observation"
          assertFixtureContext largerResult.context codeAddressProgram oldValue
            "fuel 32 code-address observation"
      | none, _ =>
          throw (IO.userError "fuel 5 lost the code-address code")
      | _, none =>
          throw (IO.userError "additional fuel lost the code-address code")

  match (baseContextFor callValueCode).withPresentStorageAccount? with
  | none =>
      throw (IO.userError "the call-value storage Account was absent")
  | some context =>
      match context.runCodeWithStorage? executionInputs 4 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (callValueRequestReady state)
            "fuel 4 did not stop at the call-value request"
          assertFixtureContext resultContext callValueProgram oldValue
            "fuel 4 call-value observation"
      | some result =>
          throw (IO.userError
            s!"fuel 4 crossed the call-value boundary: {reprStr result.outcome}")
      | none =>
          throw (IO.userError "fuel 4 lost the call-value code")

      match context.runCodeWithStorage?
          executionInputs callValueCompletionFuel,
          context.runCodeWithStorage? executionInputs 32 with
      | some result, some largerResult =>
          assertTrue
            (result.outcome == .done (.word suppliedCallValue) [])
            "fuel 5 returned the wrong call value"
          assertTrue (largerResult.outcome == result.outcome)
            "additional fuel changed call-value observation"
          assertFixtureContext result.context callValueProgram oldValue
            "fuel 5 call-value observation"
          assertFixtureContext largerResult.context callValueProgram oldValue
            "fuel 32 call-value observation"
      | none, _ =>
          throw (IO.userError "fuel 5 lost the call-value code")
      | _, none =>
          throw (IO.userError "fuel 32 lost the call-value code")

  match (baseContextFor callerAddressCode).withPresentStorageAccount? with
  | none =>
      throw (IO.userError "the caller-address storage Account was absent")
  | some context =>
      assertTrue (accountAbsentAt context callerAddress)
        "the caller unexpectedly required an Account"
      match context.runCodeWithStorage? executionInputs 4 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (callerAddressRequestReady state)
            "fuel 4 did not stop at the caller-address request"
          assertFixtureContext resultContext callerAddressProgram oldValue
            "fuel 4 caller-address observation"
      | some result =>
          throw (IO.userError
            s!"fuel 4 crossed the caller boundary: {reprStr result.outcome}")
      | none => throw (IO.userError "fuel 4 lost the caller-address code")

      match context.runCodeWithStorage? executionInputs 5,
          context.runCodeWithStorage? executionInputs 32,
          context.runCodeWithStorage? alternateCallerInputs 5 with
      | some result, some largerResult, some alternateResult =>
          assertTrue
            (result.outcome == .done (.word expectedCallerAddressWord) [])
            "fuel 5 returned the wrong caller Address"
          assertTrue (largerResult.outcome == result.outcome)
            "additional fuel changed caller-address observation"
          assertTrue
            (alternateResult.outcome ==
              .done (.word expectedAlternateCallerAddressWord) [])
            "varying only callerAddress returned the wrong result"
          assertTrue (alternateResult.outcome != result.outcome)
            "varying callerAddress did not change the result"
          assertFixtureContext result.context callerAddressProgram oldValue
            "fuel 5 caller-address observation"
          assertFixtureContext largerResult.context callerAddressProgram oldValue
            "fuel 32 caller-address observation"
          assertFixtureContext alternateResult.context callerAddressProgram oldValue
            "alternate caller-address observation"
          assertTrue
            (accountAbsentAt result.context callerAddress &&
              accountAbsentAt alternateResult.context alternateCallerAddress)
            "caller observation created an Account"
      | none, _, _ => throw (IO.userError "fuel 5 lost caller-address code")
      | _, none, _ => throw (IO.userError "fuel 32 lost caller-address code")
      | _, _, none => throw (IO.userError "alternate caller lost code")

  match
      (baseContextFor observeCodeWriteObserveCode).withPresentStorageAccount?
      with
  | none =>
      throw (IO.userError
        "the code-observe/write/code-observe storage Account was absent")
  | some context =>
      match context.runCodeWithStorage? executionInputs
          observeWriteObserveSecondRequestFuel with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (codeAddressRequestReady state)
            "fuel 23 did not stop at the second code-address request"
          assertFixtureContext resultContext
            observeCodeWriteObserveCodeProgram newValue
            "fuel 23 code-observe/write/code-observe"
      | some result =>
          throw (IO.userError
            s!"fuel 23 crossed the second code request: {reprStr result.outcome}")
      | none =>
          throw (IO.userError
            "fuel 23 lost code-observe/write/code-observe code")

      match context.runCodeWithStorage? executionInputs 29 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (oneStepBeforeCodeAddressPair state)
            "fuel 29 did not stop one step before the code-address pair"
          assertFixtureContext resultContext
            observeCodeWriteObserveCodeProgram newValue
            "fuel 29 code-observe/write/code-observe"
      | some result =>
          throw (IO.userError
            s!"fuel 29 crossed code completion: {reprStr result.outcome}")
      | none =>
          throw (IO.userError
            "fuel 29 lost code-observe/write/code-observe code")

      match context.runCodeWithStorage? executionInputs
          observeWriteObserveCompletionFuel,
          context.runCodeWithStorage? executionInputs 64 with
      | some result, some largerResult =>
          assertTrue (result.outcome == .done expectedCodeAddressPair [])
            "fuel 30 returned unequal code selectors"
          assertTrue (largerResult.outcome == result.outcome)
            "additional fuel changed code-observe/write/code-observe"
          assertFixtureContext result.context
            observeCodeWriteObserveCodeProgram newValue
            "fuel 30 code-observe/write/code-observe"
          assertFixtureContext largerResult.context
            observeCodeWriteObserveCodeProgram newValue
            "fuel 64 code-observe/write/code-observe"
      | none, _ =>
          throw (IO.userError
            "fuel 30 lost code-observe/write/code-observe code")
      | _, none =>
          throw (IO.userError
            "additional fuel lost code-observe/write/code-observe code")

  match (baseContextFor observeCallValueWriteObserveCode).withPresentStorageAccount? with
  | none =>
      throw (IO.userError
        "the call-value/write/call-value storage Account was absent")
  | some context =>
      match context.runCodeWithStorage? executionInputs
          observeWriteObserveSecondRequestFuel with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (callValueRequestReady state)
            "fuel 23 did not stop at the second call-value request"
          assertFixtureContext resultContext
            observeCallValueWriteObserveProgram suppliedCallValue
            "fuel 23 call-value/write/call-value"
      | some result =>
          throw (IO.userError
            s!"fuel 23 crossed the second call-value request: {reprStr result.outcome}")
      | none =>
          throw (IO.userError "fuel 23 lost call-value/write/call-value code")

      match context.runCodeWithStorage? executionInputs 29 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (oneStepBeforeCallValuePair state)
            "fuel 29 did not stop one step before the call-value pair"
          assertFixtureContext resultContext
            observeCallValueWriteObserveProgram suppliedCallValue
            "fuel 29 call-value/write/call-value"
      | some result =>
          throw (IO.userError
            s!"fuel 29 crossed call-value completion: {reprStr result.outcome}")
      | none =>
          throw (IO.userError "fuel 29 lost call-value/write/call-value code")

      match context.runCodeWithStorage? executionInputs
          observeWriteObserveCompletionFuel,
          context.runCodeWithStorage? executionInputs 32 with
      | some result, some largerResult =>
          assertTrue (result.outcome == .done expectedCallValuePair [])
            "fuel 30 returned unequal call values"
          assertTrue (largerResult.outcome == result.outcome)
            "additional fuel changed call-value/write/call-value"
          assertFixtureContext result.context
            observeCallValueWriteObserveProgram suppliedCallValue
            "fuel 30 call-value/write/call-value"
          assertFixtureContext largerResult.context
            observeCallValueWriteObserveProgram suppliedCallValue
            "fuel 32 call-value/write/call-value"
      | none, _ =>
          throw (IO.userError "fuel 30 lost call-value/write/call-value code")
      | _, none =>
          throw (IO.userError "fuel 32 lost call-value/write/call-value code")

  match (baseContextFor observeCallerWriteObserveCode).withPresentStorageAccount? with
  | none => throw (IO.userError "the caller/write/caller Account was absent")
  | some context =>
      match context.runCodeWithStorage? executionInputs 23 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (callerAddressRequestReady state)
            "fuel 23 did not stop at the second caller request"
          assertFixtureContext resultContext observeCallerWriteObserveProgram
            expectedCallerAddressWord "fuel 23 caller/write/caller"
      | some result =>
          throw (IO.userError
            s!"fuel 23 crossed the second caller request: {reprStr result.outcome}")
      | none => throw (IO.userError "fuel 23 lost caller/write/caller code")

      match context.runCodeWithStorage? executionInputs 29 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (oneStepBeforeCallerAddressPair state)
            "fuel 29 did not stop before the caller pair"
          assertFixtureContext resultContext observeCallerWriteObserveProgram
            expectedCallerAddressWord "fuel 29 caller/write/caller"
      | some result =>
          throw (IO.userError
            s!"fuel 29 crossed caller completion: {reprStr result.outcome}")
      | none => throw (IO.userError "fuel 29 lost caller/write/caller code")

      match context.runCodeWithStorage? executionInputs 30,
          context.runCodeWithStorage? executionInputs 32 with
      | some result, some largerResult =>
          assertTrue (result.outcome == .done expectedCallerAddressPair [])
            "fuel 30 returned unequal caller addresses"
          assertTrue (largerResult.outcome == result.outcome)
            "additional fuel changed caller/write/caller"
          assertFixtureContext result.context observeCallerWriteObserveProgram
            expectedCallerAddressWord "fuel 30 caller/write/caller"
          assertFixtureContext largerResult.context observeCallerWriteObserveProgram
            expectedCallerAddressWord "fuel 32 caller/write/caller"
      | none, _ => throw (IO.userError "fuel 30 lost caller/write/caller code")
      | _, none => throw (IO.userError "fuel 32 lost caller/write/caller code")

  match
      callValueInitialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress executionInputs observeWriteObserveCompletionFuel
          callValueDoneOutcome,
      callValueInitialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress executionInputs 32 callValueDoneOutcome with
  | some (some (some continuation)), some (some (some largerContinuation)) =>
      assertTrue
        (callValueFoldResult continuation ==
          (some suppliedCallValue, callValueFrameData))
        "parent fold lost value-derived storage or terminal bytes"
      assertTrue
        (callValueFoldResult largerContinuation ==
          (some suppliedCallValue, callValueFrameData))
        "fuel 32 changed the parent fold result"
  | _, _ =>
      throw (IO.userError
        "call-value execution did not reach parent-indexed completion")

  match
      callerInitialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress executionInputs 30 callerDoneOutcome,
      callerInitialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress executionInputs 32 callerDoneOutcome with
  | some (some (some continuation)), some (some (some largerContinuation)) =>
      assertTrue
        (callerFoldResult continuation ==
          (some expectedCallerAddressWord, callerFrameData))
        "parent fold lost caller-derived storage or terminal bytes"
      assertTrue (callerFoldResult largerContinuation == callerFoldResult continuation)
        "fuel 32 changed the caller-derived parent fold"
  | _, _ =>
      throw (IO.userError
        "caller execution did not reach parent-indexed completion")

  match (baseContextFor observeWriteObserveCode).withPresentStorageAccount? with
  | none =>
      throw (IO.userError "the observe/write/observe storage Account was absent")
  | some context =>
      match context.runCodeWithStorage? executionInputs
          observeWriteObserveSecondRequestFuel with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (storageAddressRequestReady state)
            "fuel 23 did not stop at the second address request"
          assertFixtureContext resultContext observeWriteObserveProgram newValue
            "fuel 23 observe/write/observe"
      | some result =>
          throw (IO.userError
            s!"fuel 23 crossed the second request: {reprStr result.outcome}")
      | none =>
          throw (IO.userError "fuel 23 lost observe/write/observe code")

      match context.runCodeWithStorage? executionInputs 29 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (oneStepBeforeStorageAddressPair state)
            "fuel 29 did not stop one step before the result pair"
          assertFixtureContext resultContext observeWriteObserveProgram newValue
            "fuel 29 observe/write/observe"
      | some result =>
          throw (IO.userError
            s!"fuel 29 crossed completion: {reprStr result.outcome}")
      | none =>
          throw (IO.userError "fuel 29 lost observe/write/observe code")

      match context.runCodeWithStorage? executionInputs
          observeWriteObserveCompletionFuel,
          context.runCodeWithStorage? executionInputs 64 with
      | some result, some largerResult =>
          assertTrue (result.outcome == .done expectedStorageAddressPair [])
            "fuel 30 returned unequal storage selectors"
          assertTrue (largerResult.outcome == result.outcome)
            "additional fuel changed observe/write/observe"
          assertFixtureContext result.context observeWriteObserveProgram newValue
            "fuel 30 observe/write/observe"
          assertFixtureContext largerResult.context
            observeWriteObserveProgram newValue
            "fuel 64 observe/write/observe"
      | none, _ =>
          throw (IO.userError "fuel 30 lost observe/write/observe code")
      | _, none =>
          throw (IO.userError "additional fuel lost observe/write/observe code")

  match (baseContextFor updateCode).withPresentStorageAccount? with
  | none =>
      throw (IO.userError "the selected working storage Account was absent")
  | some context =>
      assertMixedOutOfFuelAt context 21 oldValue .beforeWrite
      assertMixedOutOfFuelAt context 22 newValue .afterWrite
      assertMixedOutOfFuelAt context 27 newValue .beforeFinalRead
      assertFrameContinuationAdapter context

      match context.runCodeWithStorage? executionInputs completionFuel,
          context.runCodeWithStorage? executionInputs 64 with
      | none, _ =>
          throw (IO.userError "the working code Account was not selected")
      | _, none =>
          throw (IO.userError "additional fuel lost the selected code Account")
      | some result, some largerResult =>
          assertCompletedWriteResult result updateProgram [.bool true]
            "fuel 28 read/write/read"
          assertCompletedWriteResult largerResult updateProgram [.bool true]
            "fuel 64 read/write/read"
          assertTrue (largerResult.outcome == result.outcome)
            "additional fuel changed the completed read/write/read outcome"

  match (baseContextFor repeatedWriteCode).withPresentStorageAccount? with
  | none =>
      throw (IO.userError "the repeated-write storage Account was absent")
  | some context =>
      match context.runCodeWithStorage? executionInputs 64,
          context.runCodeWithStorage? executionInputs 96 with
      | none, _ =>
          throw (IO.userError "the repeated-write code was not selected")
      | _, none =>
          throw (IO.userError "additional fuel lost the repeated-write code")
      | some result, some largerResult =>
          assertCompletedWriteResult result repeatedWriteProgram []
            "fuel 64 repeated-write"
          assertCompletedWriteResult largerResult repeatedWriteProgram []
            "fuel 96 repeated-write"
          assertTrue (largerResult.outcome == result.outcome)
            "additional fuel changed the completed repeated-write outcome"

  match (baseContextFor zeroWriteCode).withPresentStorageAccount? with
  | none =>
      throw (IO.userError "the zero-write storage Account was absent")
  | some context =>
      match context.runCodeWithStorage? executionInputs 15 with
      | some { context := resultContext, outcome := .outOfFuel _ } =>
          assertTrue (selectedTargetMissing resultContext)
            "fuel 15 lost the handled sparse-zero update"
      | some result =>
          throw (IO.userError
            s!"fuel 15 crossed the zero boundary: {reprStr result.outcome}")
      | none =>
          throw (IO.userError "the zero boundary lost the selected code")

      match context.runCodeWithStorage?
          executionInputs zeroCompletionFuel with
      | none =>
          throw (IO.userError "the sparse-zero code Account was not selected")
      | some result =>
          assertTrue
            (result.outcome == .done (.word Word.zero) [])
            "the sparse-zero program returned the wrong result or local store"
          assertTrue (selectedTargetMissing result.context)
            "writing zero did not remove the sparse target entry"
          assertTrue
            (preservedOutsideSelectedStorage result.context zeroWriteProgram)
            "the zero write changed retained frame data"

end Tests
