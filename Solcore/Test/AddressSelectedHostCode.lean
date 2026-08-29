import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionWithInputsProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWrite
import Solcore.Semantics.HostStorageDriverWithExecutionInputsFuelProperties

/-! End-to-end regressions for address-selected handled host execution. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def codeAddress : Address := ⟨0x10, by decide⟩
private def storageAddress : Address := ⟨0x20, by decide⟩
private def absentAddress : Address := ⟨0x30, by decide⟩
private def suppliedCallValue : Word := ⟨0x73, by decide⟩

private def inputsFor
    (address : Address) : HostStorageDriver.ExecutionInputs := {
  codeAddress := address
  callValue := suppliedCallValue
}

private def slotA : Word := ⟨0x41, by decide⟩
private def slotB : Word := ⟨0x42, by decide⟩
private def finalValue : Word := ⟨0xfa, by decide⟩
private def alternateFinalValue : Word := ⟨0xfb, by decide⟩
private def codeDecoySlot : Word := ⟨0x51, by decide⟩
private def codeDecoyValue : Word := ⟨0x52, by decide⟩
private def checkpointDecoySlot : Word := ⟨0x61, by decide⟩
private def checkpointDecoyValue : Word := ⟨0x62, by decide⟩

/-- The first storage response selects the slot read by the second request. -/
private def dependentReadProgram : Program := {
  resultType := .word
  body :=
    .letE
      (.apply (.var HostFunction.storageRead.index) (.word slotA))
      (.apply (.var (HostFunction.storageRead.index + 1)) (.var 0))
}

private theorem dependentReadProgram_host_checked :
    dependentReadProgram.checkHost = true := by
  decide

private theorem dependentReadProgram_closed_rejected :
    dependentReadProgram.check = false := by
  decide

private def dependentReadCode : CheckedHostCoreProgram :=
  ⟨dependentReadProgram, dependentReadProgram_host_checked⟩

/-- A local cell must survive both handled request boundaries. -/
private def cellDependentReadProgram : Program := {
  resultType := .word
  body :=
    .letE
      (.newCell .bool (.bool true))
      (.letE
        (.apply (.var (HostFunction.storageRead.index + 1)) (.word slotA))
        (.apply (.var (HostFunction.storageRead.index + 2)) (.var 0)))
}

private theorem cellDependentReadProgram_host_checked :
    cellDependentReadProgram.checkHost = true := by
  decide

private def cellDependentReadCode : CheckedHostCoreProgram :=
  ⟨cellDependentReadProgram, cellDependentReadProgram_host_checked⟩

private def codeAccount : Account :=
  Account.empty
    |>.storageWrite slotA codeDecoySlot
    |>.storageWrite codeDecoySlot codeDecoyValue
    |>.withCode dependentReadCode

private def storageAccount : Account :=
  Account.empty
    |>.storageWrite slotA slotB
    |>.storageWrite slotB finalValue

private def checkpointAccount : Account :=
  Account.empty
    |>.storageWrite slotA checkpointDecoySlot
    |>.storageWrite checkpointDecoySlot checkpointDecoyValue

private def checkpointWorld : WorldState :=
  WorldState.empty.putAccount storageAddress checkpointAccount

private def workingWorld : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress codeAccount
    |>.putAccount storageAddress storageAccount

private def baseContext :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨storageAddress,
    ⟨⟨checkpointWorld, ⟨7, [8]⟩⟩,
      (workingWorld, ⟨9, [10, 11]⟩)⟩⟩

private theorem compileTimeNoFaultRegression
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (resultContext : HostStorageDriver.Context Nat (List Nat))
    (error : MachineFault)
    (faultState : State) :
    context.runCodeWithStorageWithInputs? inputs fuel ≠
      some ⟨resultContext, .fault error faultState⟩ :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageWithInputs?_ne_some_fault
    context inputs fuel resultContext error faultState

private theorem compileTimeAbsentBranchRegression
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (absent :
      context.context.values.working.1.account? inputs.codeAddress = none) :
    context.runCodeWithStorageWithInputs? inputs fuel = none :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageWithInputs?_of_absent
    context inputs fuel absent

private theorem compileTimeNoCodeBranchRegression
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (account : Account)
    (fuel : Nat)
    (present :
      context.context.values.working.1.account? inputs.codeAddress = some account)
    (withoutCode : account.code? = none) :
    context.runCodeWithStorageWithInputs? inputs fuel = none :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageWithInputs?_of_account_without_code
    context inputs account fuel present withoutCode

private theorem compileTimePresentBranchRegression
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (account : Account)
    (code : CheckedHostCoreProgram)
    (fuel : Nat)
    (accountPresent :
      context.context.values.working.1.account? inputs.codeAddress = some account)
    (codePresent : account.code? = some code) :
    context.runCodeWithStorageWithInputs? inputs fuel =
      some (code.runWithStorageInputs context inputs fuel) :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageWithInputs?_of_present
    context inputs account code fuel accountPresent codePresent

private theorem compileTimeRemainingFuelRegression
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : State)
    (suspension : HostSuspension)
    (execution :
      hostRun fuel state = .suspended suspension remainingFuel) :
    HostStorageDriver.runWithInputs context inputs fuel state =
      HostStorageDriver.runWithInputs
        (HostStorageDriver.handleSuspension
          inputs context suspension).1 inputs remainingFuel
        (HostStorageDriver.handleSuspension
          inputs context suspension).2 :=
  HostStorageDriver.runWithInputs_of_suspended
    context inputs fuel remainingFuel state suspension execution

private theorem compileTimeFuelSoundRegression
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : State) :
    HostStorageDriver.FuelSound
      (HostStorageDriver.runWithInputs context inputs fuel state)
      inputs fuel context state :=
  HostStorageDriver.runWithInputs_fuelSound context inputs fuel state

private theorem compileTimeCheckedTypingRegression
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    (code.runWithStorageInputs context inputs fuel).outcome.HasType
      code.program.resultType code.program.dataDefinitions :=
  code.runWithStorageInputs_hasType context inputs fuel

private theorem compileTimeCheckedNoFaultRegression
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (error : MachineFault)
    (faultState : State) :
    (code.runWithStorageInputs context inputs fuel).outcome ≠
      .fault error faultState :=
  code.runWithStorageInputs_ne_fault context inputs fuel error faultState

private theorem compileTimeCheckedFuelSoundRegression
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    HostStorageDriver.FuelSound
      (code.runWithStorageInputs context inputs fuel) inputs
      fuel context (State.initial code.program.body hostEnvironment) :=
  code.runWithStorageInputs_fuelSound context inputs fuel

private def returnedContextLooksUnchanged
    (context : HostStorageDriver.Context Nat (List Nat)) :
    Bool :=
  context.context.storageAddress == storageAddress &&
    context.storageAccount.storageRead slotA == slotB &&
    context.storageAccount.storageRead slotB == finalValue &&
    context.context.values.checkpoint.effects.rollback == 7 &&
    context.context.values.checkpoint.effects.trace == [8] &&
    context.context.values.working.2.rollback == 9 &&
    context.context.values.working.2.trace == [10, 11]

def testAddressSelectedHostCode : IO Unit := do
  assertTrue dependentReadProgram.checkHost
    "the host checker rejected the dependent storage-read program"
  assertTrue (!dependentReadProgram.check)
    "the closed checker accepted host-only stored code"

  match baseContext.withPresentStorageAccount? with
  | none =>
      throw (IO.userError "the working storage Account did not refine")
  | some context =>
      assertTrue
        (context.runCodeWithStorageWithInputs?
          (inputsFor absentAddress) 12).isNone
        "an absent code Account unexpectedly executed"
      assertTrue
        (context.runCodeWithStorageWithInputs?
          (inputsFor storageAddress) 12).isNone
        "the storage Account was incorrectly used as a code fallback"

      match context.runCodeWithStorageWithInputs?
          (inputsFor codeAddress) 11 with
      | some result =>
          assertTrue (returnedContextLooksUnchanged result.context)
            "an out-of-fuel run changed the read-only host context"
          match result.outcome with
          | .outOfFuel state =>
              match hostAdvance state with
              | .suspended suspension =>
                  assertTrue (suspension.request == .storageRead slotB)
                    "fuel 11 did not stop at the dependent second request"
              | boundary =>
                  throw (IO.userError
                    s!"fuel 11 stopped at the wrong boundary: {reprStr boundary}")
          | outcome =>
              throw (IO.userError
                s!"fuel 11 changed outcome class: {reprStr outcome}")
      | none =>
          throw (IO.userError "the working code Account was not selected")

      match context.runCodeWithStorageWithInputs?
          (inputsFor codeAddress) 12 with
      | some result =>
          assertTrue
            (result.outcome == .done (.word finalValue) [])
            "fuel 12 did not finish two dependent handled reads"
          assertTrue (returnedContextLooksUnchanged result.context)
            "a completed read-only run changed its host context"
      | none =>
          throw (IO.userError "selected host code disappeared at fuel 12")

      let updatedContext :=
        context.writeStorage slotB alternateFinalValue
      match updatedContext.runCodeWithStorageWithInputs?
          (inputsFor codeAddress) 12 with
      | some result =>
          assertTrue
            (result.outcome == .done (.word alternateFinalValue) [])
            "changing working storage did not change the handled result"
      | none =>
          throw (IO.userError "a storage update erased selected host code")

      let cellResult :=
        cellDependentReadCode.runWithStorageInputs
          context (inputsFor codeAddress) 64
      assertTrue
        (cellResult.outcome == .done (.word finalValue) [.bool true])
        "handled reads lost the Core-local cell store"
      assertTrue (returnedContextLooksUnchanged cellResult.context)
        "the checked driver changed its read-only context"

end Tests
