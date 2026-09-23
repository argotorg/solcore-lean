import Solcore.Test.ParentIndexedSelectedExecutionFixture
/-! Shared measured fixture for run-fixed current-address execution tests. -/
set_option autoImplicit false
namespace Tests.CurrentAddressExecutionFixture
open Solcore.Core
open Solcore.ContractRuntime

def codeAddress : Address := ⟨0x10, by decide⟩
def storageAddress : Address := ⟨0x20, by decide⟩
def currentAddress : Address := ⟨0x30, by decide⟩
def alternateCurrentAddress : Address := ⟨0x35, by decide⟩
def callerAddress : Address := ⟨0x40, by decide⟩

def suppliedCallValue : Word := ⟨0x50, by decide⟩
def targetSlot : Word := ⟨0x61, by decide⟩
def oldValue : Word := ⟨0x62, by decide⟩
def retainedSlot : Word := ⟨0x63, by decide⟩
def retainedValue : Word := ⟨0x64, by decide⟩

def inputData : HostStorageDriver.InputData := {
  bytes := [0x11, 0x22, 0x33].toByteArray
  size_lt_wordModulus := by decide
}

def executionInputsFor
    (current : Address) : HostStorageDriver.ExecutionInputs := {
  codeAddress := codeAddress
  callValue := suppliedCallValue
  callerAddress := callerAddress
  inputData := inputData
  currentAddress := current
}

def executionInputs : HostStorageDriver.ExecutionInputs :=
  executionInputsFor currentAddress
def alternateExecutionInputs : HostStorageDriver.ExecutionInputs :=
  executionInputsFor alternateCurrentAddress

/-- Observe current, write its Word, then observe current again. -/
def program : Program := {
  resultType := .product .word .word
  body :=
    .letE
      (.apply (.var HostFunction.currentAddress.index) .unit)
      (.letE
        (.apply
          (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word targetSlot) (.var 0)))
        (.letE
          (.apply
            (.var (HostFunction.currentAddress.index + 2))
            .unit)
          (.pair (.var 2) (.var 0))))
}

theorem program_host_checked : program.checkHost = true := by decide

def code : CheckedHostCoreProgram := ⟨program, program_host_checked⟩

def storageAccount : Account :=
  Account.empty
    |>.storageWrite targetSlot oldValue
    |>.storageWrite retainedSlot retainedValue

def workingWorld : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress (Account.empty.withCode code)
    |>.putAccount storageAddress storageAccount

def checkpointWorld : WorldState :=
  WorldState.empty.putAccount storageAddress storageAccount

def parentWorking :
    WorldState × FrameEffectJournal Nat (FrameTrace Nat) :=
  (checkpointWorld, ⟨101, FrameTrace.empty⟩)

def initialization :
    ParentIndexedFrameInitialization Nat Nat parentWorking := {
  initialWorld := workingWorld
  workingRollback := 201
}

inductive TrapReason where
  | invalidDoneInputs
  | policyTrap
  deriving Repr, BEq, DecidableEq

def returnData : Bytes := [0xa1, 0xb2].toByteArray
def revertData : Bytes := [0xc1, 0xd2].toByteArray

def expectedWord (current : Address) : Word := addressToWord current
def expectedPair (current : Address) : Value :=
  .pair (.word (expectedWord current)) (.word (expectedWord current))
def storageValueAt?
    (state : WorldState) (address : Address) (slot : Word) : Option Word :=
  ParentIndexedSelectedExecutionFixture.storageValueAt? state address slot

def exactCompletion
    (current : Address)
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (value : Value) (store : Store) : Bool :=
  value == expectedPair current && store == [] &&
    context.readStorage targetSlot == expectedWord current

def doneOutcomeFor
    (current : Address) (outcome : FrameOutcome TrapReason)
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (value : Value) (store : Store) : FrameOutcome TrapReason :=
  if exactCompletion current context value store then outcome
  else .trapped .invalidDoneInputs

def returnedDoneOutcomeFor (current : Address) :=
  doneOutcomeFor current (.returned returnData)

def revertedDoneOutcomeFor (current : Address) :=
  doneOutcomeFor current (.reverted revertData)

def trappedDoneOutcomeFor (current : Address) :=
  doneOutcomeFor current (.trapped .policyTrap)

abbrev Result := ParentIndexedSelectedExecutionResult
  Nat Nat TrapReason parentWorking

def runWith
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome : HostStorageDriver.Context Nat (FrameTrace Nat) →
      Value → Store → FrameOutcome TrapReason)
    (fuel : Nat) : Result :=
  initialization.runCodeWithStorageParentIndexedResult
    storageAddress inputs fuel doneOutcome

def resumeWith
    (result : Result) (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome : HostStorageDriver.Context Nat (FrameTrace Nat) →
      Value → Store → FrameOutcome TrapReason)
    (additional : Nat) : Result :=
  result.resumeWithFuel initialization inputs doneOutcome additional

def codeProgramIs (state : WorldState) : Bool :=
  match state.code? codeAddress with
  | some selected => selected.program == program
  | none => false

def accountAbsentAt
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (address : Address) : Bool :=
  (context.context.values.working.1.account? address).isNone &&
    (context.context.values.checkpoint.state.account? address).isNone

def contextPreserved
    (context : HostStorageDriver.Context Nat (FrameTrace Nat)) : Bool :=
  let values := context.context.values
  context.context.storageAddress == storageAddress &&
    codeProgramIs values.working.1 &&
    accountAbsentAt context currentAddress &&
    accountAbsentAt context alternateCurrentAddress &&
    context.storageAccount.storageValue? retainedSlot == some retainedValue &&
    storageValueAt? values.working.1 storageAddress retainedSlot ==
      some retainedValue &&
    storageValueAt? values.checkpoint.state storageAddress targetSlot ==
      some oldValue &&
    storageValueAt? values.checkpoint.state storageAddress retainedSlot ==
      some retainedValue &&
    values.checkpoint.effects.rollback == 101 &&
    values.checkpoint.effects.trace.toList == [] &&
    values.working.2.rollback == 201 &&
    values.working.2.trace.toList == []

def contextHasCurrentWrite
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (current : Address) : Bool :=
  context.readStorage targetSlot == expectedWord current &&
    storageValueAt? context.context.values.working.1
      storageAddress targetSlot == some (expectedWord current)

def currentAddressRequestReady (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension => suspension.request == .currentAddress
  | _ => false

def storageWriteRequestReady
    (current : Address) (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension =>
      suspension.request == .storageWrite targetSlot (expectedWord current)
  | _ => false

def beforeSecondObservation (state : State) : Bool :=
  state.control == .ret .unit &&
    match state.continuation with
    | [.letBody body _] =>
        body == .letE
          (.apply
            (.var (HostFunction.currentAddress.index + 2)) .unit)
          (.pair (.var 2) (.var 0))
    | _ => false

def oneStepBeforePair (current : Address) (state : State) : Bool :=
  match hostAdvance state with
  | .next next => next == State.final (expectedPair current)
  | _ => false

inductive FoldMarker where
  | returned
  | reverted
  | trapped
  | mismatch
  deriving Repr, BEq, DecidableEq

def foldValuesMatch
    (expectedRollback : Nat) (expectedValue : Word)
    (values : WorldState ×
      FrameEffectJournal Nat (FrameTrace Nat)) : Bool :=
  storageValueAt? values.1 storageAddress targetSlot == some expectedValue &&
    values.2.rollback == expectedRollback &&
    values.2.trace.toList == []

def foldResult
    (current : Address)
    (continuation : ParentIndexedFrameContinuationContext
      Nat Nat TrapReason parentWorking) : FoldMarker :=
  continuation.foldResolutionWithTrapRollback
    (fun values data =>
      if foldValuesMatch 201 (expectedWord current) values &&
          data == returnData then .returned else .mismatch)
    (fun values data =>
      if foldValuesMatch 101 oldValue values &&
          data == revertData then .reverted else .mismatch)
    (fun values reason =>
      if foldValuesMatch 101 oldValue values &&
          reason == .policyTrap then .trapped else .mismatch)

/-- Measured exact boundaries of the executable checked program. -/
def writeRequestFuel : Nat := 16
def postWriteFuel : Nat := 17
def secondRequestFuel : Nat := 23
def pairReadyFuel : Nat := 29
def completionFuel : Nat := 30

end Tests.CurrentAddressExecutionFixture
