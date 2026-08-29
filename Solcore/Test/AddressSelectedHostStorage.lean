import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionProperties

/-! End-to-end regressions for address-selected storage read/write execution. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def codeAddress : Address := ⟨0x10, by decide⟩
private def storageAddress : Address := ⟨0x20, by decide⟩
private def otherAddress : Address := ⟨0x30, by decide⟩

private def selectorSlot : Word := ⟨0x41, by decide⟩
private def targetSlot : Word := ⟨0x42, by decide⟩
private def retainedSlot : Word := ⟨0x43, by decide⟩
private def oldValue : Word := ⟨0x51, by decide⟩
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

private def baseContextFor (code : CheckedHostCoreProgram) :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨storageAddress,
    ⟨⟨checkpointWorld, checkpointEffects⟩,
      (workingWorldFor code, workingEffects)⟩⟩

private def storageValueAt?
    (state : WorldState) (address : Address) (slot : Word) : Option Word :=
  (state.account? address).bind fun account => account.storageValue? slot

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

private def completionFuel : Nat := 28
private def zeroCompletionFuel : Nat := 16

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
  match context.runCodeWithStorage? codeAddress fuel with
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

def testAddressSelectedHostStorage : IO Unit := do
  assertTrue updateProgram.checkHost
    "the host checker rejected the read/write/read program"
  assertTrue zeroWriteProgram.checkHost
    "the host checker rejected the sparse-zero program"

  match (baseContextFor updateCode).withPresentStorageAccount? with
  | none =>
      throw (IO.userError "the selected working storage Account was absent")
  | some context =>
      assertMixedOutOfFuelAt context 21 oldValue .beforeWrite
      assertMixedOutOfFuelAt context 22 newValue .afterWrite
      assertMixedOutOfFuelAt context 27 newValue .beforeFinalRead

      match context.runCodeWithStorage? codeAddress completionFuel with
      | none =>
          throw (IO.userError "the working code Account was not selected")
      | some result =>
          assertTrue
            (result.outcome == .done (.word newValue) [.bool true])
            "the read/write/read program lost its value or Core-local cell"
          assertTrue (selectedStorageHas result.context newValue)
            "the selected working storage was not updated exactly"
          assertTrue
            (preservedOutsideSelectedStorage result.context updateProgram)
            "the run changed code, another Account, checkpoint, effects, or selector"

  match (baseContextFor zeroWriteCode).withPresentStorageAccount? with
  | none =>
      throw (IO.userError "the zero-write storage Account was absent")
  | some context =>
      match context.runCodeWithStorage? codeAddress 15 with
      | some { context := resultContext, outcome := .outOfFuel _ } =>
          assertTrue (selectedTargetMissing resultContext)
            "fuel 15 lost the handled sparse-zero update"
      | some result =>
          throw (IO.userError
            s!"fuel 15 crossed the zero boundary: {reprStr result.outcome}")
      | none =>
          throw (IO.userError "the zero boundary lost the selected code")

      match context.runCodeWithStorage? codeAddress zeroCompletionFuel with
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
