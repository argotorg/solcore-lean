import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeFrameContinuationProperties
import Solcore.ContractRuntime.ParentIndexedFrameInitializationPresentStorageAccountCodeFrameContinuationCoherenceProperties
import Solcore.ContractRuntime.ParentIndexedFrameResolutionFoldProperties

/-! Parent-indexed completion of strict optional input-word execution. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def codeAddress : Address := ⟨0x10, by decide⟩
private def storageAddress : Address := ⟨0x20, by decide⟩
private def callerAddress : Address := ⟨0x40, by decide⟩
private def targetSlot : Word := ⟨0x42, by decide⟩
private def oldValue : Word := ⟨0x51, by decide⟩
private def observedOffset : Word := ⟨1, by decide⟩
private def expectedWord : Word := ⟨0x01020304, by decide⟩
private def missingSentinel : Word := ⟨0x100, by decide⟩

private def presentInput : HostStorageDriver.InputData := {
  bytes := [0xaa].toByteArray.append (encodeWordBytesBE expectedWord)
  size_lt_wordModulus := by native_decide
}

private def incompleteInput : HostStorageDriver.InputData := {
  bytes := [0xaa, 0x01].toByteArray
  size_lt_wordModulus := by decide
}

private def inputsFor (inputData : HostStorageDriver.InputData) :
    HostStorageDriver.ExecutionInputs := {
  codeAddress := codeAddress
  callValue := ⟨0x73, by decide⟩
  callerAddress := callerAddress
  inputData := inputData
  currentAddress := codeAddress
}

private def presentInputs := inputsFor presentInput
private def incompleteInputs := inputsFor incompleteInput

/-- Presence writes and re-observes the exact Word; absence returns sentinels. -/
private def observeCaseWriteObserveProgram : Program := {
  resultType := .product .word .word
  body :=
    .caseE
      (.apply (.var HostFunction.inputDataWordBE?.index)
        (.word observedOffset))
      (.pair (.word missingSentinel) (.word missingSentinel))
      (.letE
        (.apply (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word targetSlot) (.var 0)))
        (.caseE
          (.apply (.var (HostFunction.inputDataWordBE?.index + 2))
            (.word observedOffset))
          (.pair (.var 2) (.word missingSentinel))
          (.pair (.var 2) (.var 0))))
}

private theorem observeCaseWriteObserveProgram_host_checked :
    observeCaseWriteObserveProgram.checkHost = true := by decide

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

private inductive InputWordBETrapReason where
  | invalidDoneInputs
  deriving Repr, BEq, DecidableEq

private def presentTerminal : Bytes := [0xa3, 0xb4].toByteArray
private def incompleteTerminal : Bytes := [0xc5, 0xd6].toByteArray

private def doneOutcomeFor
    (expectedPair expectedStored : Word) (terminal : Bytes)
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (value : Value) (store : Store) : FrameOutcome InputWordBETrapReason :=
  match value, store with
  | .pair (.word first) (.word second), [] =>
      if first = expectedPair ∧ second = expectedPair ∧
          context.readStorage targetSlot = expectedStored then
        .returned terminal
      else .trapped .invalidDoneInputs
  | _, _ => .trapped .invalidDoneInputs

private def presentDoneOutcome :=
  doneOutcomeFor expectedWord expectedWord presentTerminal

private def incompleteDoneOutcome :=
  doneOutcomeFor missingSentinel oldValue incompleteTerminal

private def storageValueAt?
    (state : WorldState) (address : Address) (slot : Word) : Option Word :=
  (state.account? address).bind fun account => account.storageValue? slot

private def codeProgramIs (state : WorldState) : Bool :=
  match state.code? codeAddress with
  | none => false
  | some code => code.program == observeCaseWriteObserveProgram

private def foldResult
    (continuation :
      ParentIndexedFrameContinuationContext Nat Nat InputWordBETrapReason
        parentWorking) :
    Option Word × Bytes :=
  continuation.foldResolutionWithTrapRollback
    (fun values data =>
      (storageValueAt? values.1 storageAddress targetSlot, data))
    (fun _ data => (none, data))
    (fun _ _ => (none, ByteArray.empty))

private def continuationIdentity
    (continuation :
      ParentIndexedFrameContinuationContext Nat Nat InputWordBETrapReason
        parentWorking)
    (expectedStored : Word) : Bool :=
  (continuation.stateCheckpoint.account? codeAddress).isNone &&
    (storageValueAt? continuation.stateCheckpoint storageAddress targetSlot).isNone &&
    continuation.effectCheckpoint.rollback == 101 &&
    continuation.effectCheckpoint.trace.toList == [] &&
    continuation.effectWorking.rollback == 201 &&
    continuation.effectWorking.trace.toList == [] &&
    storageValueAt? continuation.result.working storageAddress targetSlot ==
      some expectedStored &&
    codeProgramIs continuation.result.working

private theorem continuation_parent_index_exact
    (continuation :
      ParentIndexedFrameContinuationContext Nat Nat InputWordBETrapReason
        parentWorking) :
    (continuation.stateCheckpoint, continuation.effectCheckpoint) =
      parentWorking :=
  continuation.checkpoint_eq_parentWorking

/-- A completed indexed continuation is exactly stable at every larger budget. -/
private theorem parentCompletion_done_stable
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome : HostStorageDriver.Context Nat (FrameTrace Nat) →
      Value → Store → FrameOutcome InputWordBETrapReason)
    {fuel largerFuel : Nat}
    {continuation :
      ParentIndexedFrameContinuationContext Nat Nat InputWordBETrapReason
        parentWorking}
    (completed :
      initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome =
        some (some (some continuation)))
    (more : fuel ≤ largerFuel) :
    initialization.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress inputs largerFuel doneOutcome =
      some (some (some continuation)) :=
  initialization.runCodeWithStorageParentIndexedContinuationContext?_some_some_some_stable
    storageAddress inputs doneOutcome completed more

private def inputWordRequestReady (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension =>
      suspension.request == .inputDataWordBE? observedOffset
  | _ => false

private def oneStepBeforeResult (expected : Word) (state : State) : Bool :=
  match hostAdvance state with
  | .next next => next == State.final (.pair (.word expected) (.word expected))
  | _ => false

private def assertMissingLayers
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome : HostStorageDriver.Context Nat (FrameTrace Nat) →
      Value → Store → FrameOutcome InputWordBETrapReason)
    (fuel : Nat) (label : String) : IO Unit := do
  match missingStorageInitialization
      |>.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress inputs fuel doneOutcome with
  | none => pure ()
  | _ => throw (IO.userError s!"{label}: missing storage crossed outer Option")
  match missingCodeInitialization
      |>.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress inputs fuel doneOutcome with
  | some none => pure ()
  | _ => throw (IO.userError s!"{label}: missing code crossed middle Option")

private def assertCompletion
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome : HostStorageDriver.Context Nat (FrameTrace Nat) →
      Value → Store → FrameOutcome InputWordBETrapReason)
    (fuel largerFuel : Nat) (expectedStored : Word) (terminal : Bytes)
    (label : String) : IO Unit := do
  match
      initialization.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress inputs fuel doneOutcome,
      initialization.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress inputs largerFuel doneOutcome with
  | some (some (some continuation)),
      some (some (some largerContinuation)) =>
      assertTrue (foldResult continuation == (some expectedStored, terminal))
        s!"{label}: parent fold lost exact storage or terminal bytes"
      assertTrue (foldResult largerContinuation == foldResult continuation)
        s!"{label}: larger fuel changed the parent fold"
      assertTrue
        (continuationIdentity continuation expectedStored &&
          continuationIdentity largerContinuation expectedStored)
        s!"{label}: completion changed context, effects, index, or trace"
      assertTrue (largerContinuation.result.outcome == continuation.result.outcome)
        s!"{label}: larger fuel changed the completed outcome"
  | _, _ => throw (IO.userError s!"{label}: parent completion was absent")

def testAddressSelectedHostInputWordBEParent : IO Unit := do
  assertTrue observeCaseWriteObserveProgram.checkHost
    "the host checker rejected the parent strict input-word consumer"
  assertTrue (presentInput.wordBE? observedOffset == some expectedWord)
    "the complete parent fixture did not decode exactly"
  assertTrue ((incompleteInput.wordBE? observedOffset).isNone)
    "the incomplete parent fixture was padded instead of rejected"

  assertMissingLayers presentInputs presentDoneOutcome 30 "complete window"
  assertMissingLayers incompleteInputs incompleteDoneOutcome 30
    "incomplete window"

  match initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress with
  | none => throw (IO.userError "the parent storage Account was absent")
  | some context =>
      match context.runCodeWithStorage? presentInputs 23 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (inputWordRequestReady state)
            "fuel 23 did not stop at the second strict input-word request"
          assertTrue (resultContext.readStorage targetSlot == expectedWord)
            "fuel 23 lost the word-derived storage write"
      | _ => throw (IO.userError "fuel 23 crossed its measured boundary")
      match context.runCodeWithStorage? presentInputs 29 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (oneStepBeforeResult expectedWord state)
            "fuel 29 did not stop one step before the present pair"
          assertTrue (resultContext.readStorage targetSlot == expectedWord)
            "fuel 29 lost the word-derived storage write"
      | _ => throw (IO.userError "fuel 29 crossed its measured boundary")
      match context.runCodeWithStorage? incompleteInputs 11 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (oneStepBeforeResult missingSentinel state)
            "fuel 11 did not stop one step before the absent pair"
          assertTrue (resultContext.readStorage targetSlot == oldValue)
            "the incomplete-window branch changed storage"
      | _ => throw (IO.userError "fuel 11 crossed its measured boundary")

  match initialization.runCodeWithStorageParentIndexedContinuationContext?
      storageAddress presentInputs 29 presentDoneOutcome with
  | some (some none) => pure ()
  | _ => throw (IO.userError "fuel 29 crossed the present inner Option")

  match initialization.runCodeWithStorageParentIndexedContinuationContext?
      storageAddress incompleteInputs 11 incompleteDoneOutcome with
  | some (some none) => pure ()
  | _ => throw (IO.userError "fuel 11 crossed the incomplete inner Option")

  assertCompletion presentInputs presentDoneOutcome 30 64 expectedWord
    presentTerminal "complete window"
  assertCompletion incompleteInputs incompleteDoneOutcome 12 64 oldValue
    incompleteTerminal "incomplete window"

end Tests
