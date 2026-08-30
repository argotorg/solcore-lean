import Solcore.Semantics.ParentIndexedSelectedExecutionCompatibilityProperties
import Solcore.Semantics.ParentIndexedSelectedExecutionFoldCoherenceProperties
import Solcore.Semantics.ParentIndexedSelectedExecutionResumptionProperties

/-! Shared measured fixture for branch-complete parent execution tests. -/

set_option autoImplicit false

namespace Tests.ParentIndexedSelectedExecutionFixture

open Solcore.Core
open Solcore.Semantics

def codeAddress : Address := ⟨0x10, by decide⟩
def storageAddress : Address := ⟨0x20, by decide⟩
def callerAddress : Address := ⟨0x40, by decide⟩

def targetSlot : Word := ⟨0x51, by decide⟩
def oldValue : Word := ⟨0x52, by decide⟩
def writtenValue : Word := ⟨0x53, by decide⟩

def inputData : HostStorageDriver.InputData := {
  bytes := [0x11, 0x22, 0x33].toByteArray
  size_lt_wordModulus := by decide
}

def executionInputs : HostStorageDriver.ExecutionInputs := {
  codeAddress := codeAddress
  callValue := Word.zero
  callerAddress := callerAddress
  inputData := inputData
}

/-- Write working storage, then observe the immutable input size. -/
def program : Program := {
  resultType := .word
  body :=
    .letE
      (.apply
        (.var HostFunction.storageWrite.index)
        (.pair (.word targetSlot) (.word writtenValue)))
      (.apply (.var (HostFunction.inputDataSize.index + 1)) .unit)
}

theorem program_host_checked : program.checkHost = true := by
  decide

def code : CheckedHostCoreProgram := ⟨program, program_host_checked⟩

def storageAccount : Account :=
  Account.empty.storageWrite targetSlot oldValue

def checkpointWorld : WorldState :=
  WorldState.empty.putAccount storageAddress storageAccount

def workingWorld : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress (Account.empty.withCode code)
    |>.putAccount storageAddress storageAccount

def parentWorking :
    WorldState × FrameEffectJournal Nat (FrameTrace Nat) :=
  (checkpointWorld, ⟨101, FrameTrace.empty⟩)

def initialization :
    ParentIndexedFrameInitialization Nat Nat parentWorking := {
  initialWorld := workingWorld
  workingRollback := 201
}

def missingStorageInitialization :
    ParentIndexedFrameInitialization Nat Nat parentWorking := {
  initialWorld :=
    WorldState.empty.putAccount codeAddress (Account.empty.withCode code)
  workingRollback := 201
}

def missingCodeInitialization :
    ParentIndexedFrameInitialization Nat Nat parentWorking := {
  initialWorld := WorldState.empty.putAccount storageAddress storageAccount
  workingRollback := 201
}

inductive TrapReason where
  | policyTrap
  deriving Repr, BEq, DecidableEq

def returnData : Bytes := [0xa1, 0xb2].toByteArray
def revertData : Bytes := [0xc1, 0xd2].toByteArray

def returnedDoneOutcome
    (_ : HostStorageDriver.Context Nat (FrameTrace Nat))
    (_ : Value) (_ : Store) : FrameOutcome TrapReason :=
  .returned returnData

def revertedDoneOutcome
    (_ : HostStorageDriver.Context Nat (FrameTrace Nat))
    (_ : Value) (_ : Store) : FrameOutcome TrapReason :=
  .reverted revertData

def trappedDoneOutcome
    (_ : HostStorageDriver.Context Nat (FrameTrace Nat))
    (_ : Value) (_ : Store) : FrameOutcome TrapReason :=
  .trapped .policyTrap

abbrev Result := ParentIndexedSelectedExecutionResult
  Nat Nat TrapReason parentWorking

def runWith
    (doneOutcome : HostStorageDriver.Context Nat (FrameTrace Nat) →
      Value → Store → FrameOutcome TrapReason)
    (fuel : Nat) : Result :=
  initialization.runCodeWithStorageParentIndexedResult
    storageAddress executionInputs fuel doneOutcome

def storageValueAt?
    (state : WorldState) (address : Address) (slot : Word) : Option Word :=
  (state.account? address).bind fun account => account.storageValue? slot

def contextHasTarget
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (expected : Word) : Bool :=
  context.readStorage targetSlot == expected &&
    storageValueAt? context.context.values.working.1
      storageAddress targetSlot == some expected

def contextPreserved
    (context : HostStorageDriver.Context Nat (FrameTrace Nat)) : Bool :=
  storageValueAt? context.context.values.checkpoint.state
      storageAddress targetSlot == some oldValue &&
    context.context.values.checkpoint.effects.rollback == 101 &&
    context.context.values.checkpoint.effects.trace.toList == [] &&
    context.context.values.working.2.rollback == 201 &&
    context.context.values.working.2.trace.toList == []

def writeRequestReady (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension =>
      suspension.request == .storageWrite targetSlot writtenValue
  | _ => false

def beforeInputSuffix (state : State) : Bool :=
  state.control == .ret .unit &&
    match state.continuation with
    | [.letBody body _] =>
        body == .apply
          (.var (HostFunction.inputDataSize.index + 1)) .unit
    | _ => false

def inputSizeRequestReady (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension => suspension.request == .inputDataSize
  | _ => false

def exactCompletion (value : Value) (store : Store) : Bool :=
  value == .word inputData.sizeWord && store == []

def syntheticFault : MachineFault :=
  .invalidHostArgument .storageRead .unit

inductive FoldMarker where
  | returned
  | reverted
  | trapped
  | mismatch
  deriving Repr, BEq, DecidableEq

def foldValuesMatch
    (expectedRollback : Nat) (expectedValue : Word)
    (values :
      WorldState × FrameEffectJournal Nat (FrameTrace Nat)) : Bool :=
  storageValueAt? values.1 storageAddress targetSlot == some expectedValue &&
    values.2.rollback == expectedRollback &&
    values.2.trace.toList == []

def onReturned
    (values : WorldState × FrameEffectJournal Nat (FrameTrace Nat))
    (data : Bytes) : FoldMarker :=
  if foldValuesMatch 201 writtenValue values && data == returnData then
    .returned
  else .mismatch

def onReverted
    (values : WorldState × FrameEffectJournal Nat (FrameTrace Nat))
    (data : Bytes) : FoldMarker :=
  if foldValuesMatch 101 oldValue values && data == revertData then
    .reverted
  else .mismatch

def onTrapped
    (values : WorldState × FrameEffectJournal Nat (FrameTrace Nat))
    (reason : TrapReason) : FoldMarker :=
  if foldValuesMatch 101 oldValue values && reason == .policyTrap then
    .trapped
  else .mismatch

def foldResult
    (continuation : ParentIndexedFrameContinuationContext
      Nat Nat TrapReason parentWorking) : FoldMarker :=
  continuation.foldResolutionWithTrapRollback
    onReturned onReverted onTrapped

def writeRequestFuel : Nat := 9
def postWriteFuel : Nat := 10
def inputRequestFuel : Nat := 15
def completionFuel : Nat := 16

end Tests.ParentIndexedSelectedExecutionFixture
