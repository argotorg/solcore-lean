import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecution
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
import Solcore.ContractRuntime.HostStorageDriver
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeFrameContinuation
import Solcore.ContractRuntime.ParentIndexedFrameInitialization
import Solcore.ContractRuntime.ParentIndexedFrameResolutionFold
import Solcore.ContractRuntime.HostStorageHandler

/-!
# Address-selected host tests

Address-selected host handlers end to end: storage, code, input data and its size, and input words.
-/

section
-- leanmerge: from Solcore.Test.AddressSelectedHostCode
/-! End-to-end regressions for address-selected handled host execution. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def codeAddress : Address := ⟨0x10, by decide⟩
private def storageAddress : Address := ⟨0x20, by decide⟩
private def absentAddress : Address := ⟨0x30, by decide⟩
private def callerAddress : Address := ⟨0x40, by decide⟩
private def suppliedCallValue : Word := ⟨0x73, by decide⟩
private def inputData : HostStorageDriver.InputData := {
  bytes := [0x34, 0x00, 0xfe].toByteArray
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
    context.runCodeWithStorage? inputs fuel ≠
      some ⟨resultContext, .fault error faultState⟩ :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_ne_some_fault
    context inputs fuel resultContext error faultState

private theorem compileTimeAbsentBranchRegression
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (absent :
      context.context.values.working.1.account? inputs.codeAddress = none) :
    context.runCodeWithStorage? inputs fuel = none :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_of_absent
    context inputs fuel absent

private theorem compileTimeNoCodeBranchRegression
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (account : Account)
    (fuel : Nat)
    (present :
      context.context.values.working.1.account? inputs.codeAddress = some account)
    (withoutCode : account.code? = none) :
    context.runCodeWithStorage? inputs fuel = none :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_of_account_without_code
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
    context.runCodeWithStorage? inputs fuel =
      some (code.runWithStorage context inputs fuel) :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_of_present
    context inputs account code fuel accountPresent codePresent

private theorem compileTimeRemainingFuelRegression
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : State)
    (suspension : HostSuspension)
    (execution :
      hostRun fuel state = .suspended suspension remainingFuel) :
    HostStorageDriver.run context inputs fuel state =
      if (@HostStorageDriver.handler Nat (List Nat) inputs).supports
          suspension.request then
        HostStorageDriver.run
          (HostStorageDriver.handleSuspension
            inputs context suspension).1 inputs remainingFuel
          (HostStorageDriver.handleSuspension
            inputs context suspension).2
      else
        ⟨context, .unsupported suspension remainingFuel⟩ :=
  HostStorageDriver.run_of_suspended
    context inputs fuel remainingFuel state suspension execution

private theorem compileTimeFuelSoundRegression
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : State) :
    HostStorageDriver.FuelSound
      (HostStorageDriver.run context inputs fuel state)
      inputs fuel context state :=
  HostStorageDriver.run_fuelSound context inputs fuel state

private theorem compileTimeCheckedTypingRegression
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    (code.runWithStorage context inputs fuel).outcome.HasType
      code.program.resultType code.program.dataDefinitions :=
  code.runWithStorage_hasType context inputs fuel

private theorem compileTimeCheckedNoFaultRegression
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (error : MachineFault)
    (faultState : State) :
    (code.runWithStorage context inputs fuel).outcome ≠
      .fault error faultState :=
  code.runWithStorage_ne_fault context inputs fuel error faultState

private theorem compileTimeCheckedFuelSoundRegression
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    HostStorageDriver.FuelSound
      (code.runWithStorage context inputs fuel) inputs
      fuel context (State.initial code.program.body hostEnvironment) :=
  code.runWithStorage_fuelSound context inputs fuel

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
        (context.runCodeWithStorage?
          (inputsFor absentAddress) 12).isNone
        "an absent code Account unexpectedly executed"
      assertTrue
        (context.runCodeWithStorage?
          (inputsFor storageAddress) 12).isNone
        "the storage Account was incorrectly used as a code fallback"

      match context.runCodeWithStorage?
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

      match context.runCodeWithStorage?
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
      match updatedContext.runCodeWithStorage?
          (inputsFor codeAddress) 12 with
      | some result =>
          assertTrue
            (result.outcome == .done (.word alternateFinalValue) [])
            "changing working storage did not change the handled result"
      | none =>
          throw (IO.userError "a storage update erased selected host code")

      let cellResult :=
        cellDependentReadCode.runWithStorage
          context (inputsFor codeAddress) 64
      assertTrue
        (cellResult.outcome == .done (.word finalValue) [.bool true])
        "handled reads lost the Core-local cell store"
      assertTrue (returnedContextLooksUnchanged cellResult.context)
        "the checked driver changed its read-only context"

end Tests
end

section
-- leanmerge: from Solcore.Test.AddressSelectedHostInputData
/-! End-to-end regressions for run-fixed optional input-byte observation. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def callValue : Word := ⟨0x73, by decide⟩

private def observedOffset : Word := ⟨1, by decide⟩
private def expectedByte : Word := ⟨0x7f, by decide⟩

private def nonzeroInput : HostStorageDriver.InputData := {
  bytes := [0xa5, 0x7f].toByteArray
  size_lt_wordModulus := by decide
}

private def zeroInput : HostStorageDriver.InputData := {
  bytes := [0xa5, 0x00].toByteArray
  size_lt_wordModulus := by decide
}

private def absentInput : HostStorageDriver.InputData := {
  bytes := [0xa5].toByteArray
  size_lt_wordModulus := by decide
}

private def inputsFor_variant
    (inputData : HostStorageDriver.InputData) :
    HostStorageDriver.ExecutionInputs := {
  codeAddress := codeAddress
  callValue := callValue
  callerAddress := callerAddress
  inputData := inputData
  currentAddress := codeAddress
}

private def nonzeroInputs := inputsFor_variant nonzeroInput
private def zeroInputs := inputsFor_variant zeroInput
private def absentInputs := inputsFor_variant absentInput

private def inputByteProgram : Program := {
  resultType := .sum .unit .word
  body :=
    .apply (.var HostFunction.inputDataByte?.index) (.word observedOffset)
}

private theorem inputByteProgram_host_checked :
    inputByteProgram.checkHost = true := by
  decide

private theorem inputByteProgram_closed_rejected :
    inputByteProgram.check = false := by
  decide

private def inputByteCode : CheckedHostCoreProgram :=
  ⟨inputByteProgram, inputByteProgram_host_checked⟩

private def storageSlot : Word := ⟨0x51, by decide⟩
private def storageValue : Word := ⟨0x52, by decide⟩

private def codeAccount_variant : Account :=
  Account.empty.withCode inputByteCode

private def storageAccount_variant : Account :=
  Account.empty.storageWrite storageSlot storageValue

private def checkpointWorld_variant : WorldState :=
  WorldState.empty.putAccount storageAddress storageAccount_variant

private def workingWorld_variant : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress codeAccount_variant
    |>.putAccount storageAddress storageAccount_variant

private def baseContext_variant :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨storageAddress,
    ⟨⟨checkpointWorld_variant, ⟨7, [8]⟩⟩,
      (workingWorld_variant, ⟨9, [10, 11]⟩)⟩⟩

private def requestReadyState : State :=
  ⟨.ret (.word observedOffset), [.hostApply .inputDataByte?], []⟩

private theorem inputByteProgram_suspends :
    hostRun 5 (State.initial inputByteProgram.body hostEnvironment) =
      .suspended ⟨.inputDataByte? observedOffset, [], []⟩ 0 := by
  decide

private def contextLooksUnchanged
    (context : HostStorageDriver.Context Nat (List Nat)) : Bool :=
  context.context.storageAddress == storageAddress &&
    context.storageAccount.storageRead storageSlot == storageValue &&
    (context.context.values.working.1.account? codeAddress).isSome &&
    (context.context.values.working.1.account? storageAddress).isSome &&
    context.context.values.checkpoint.effects.rollback == 7 &&
    context.context.values.checkpoint.effects.trace == [8] &&
    context.context.values.working.2.rollback == 9 &&
    context.context.values.working.2.trace == [10, 11]

/-- Optional input observation changes no part of the handled driver context. -/
private theorem inputByte_runWithStorage_preserves_context
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs) :
    (inputByteCode.runWithStorage context inputs 5).context = context := by
  unfold CheckedHostCoreProgram.runWithStorage
  change
    (HostStorageDriver.run context inputs 5
      (State.initial inputByteProgram.body hostEnvironment)).context = context
  cases response : inputs.inputData.byte? observedOffset with
  | none =>
      rw [HostStorageDriver.run_of_suspended_inputDataByte?_none
        context inputs 5 0 _ observedOffset [] []
        inputByteProgram_suspends response]
      change
        (HostStorageDriver.run context inputs 0
          (State.final (.inLeft .word .unit))).context = context
      rw [HostStorageDriver.run_of_done context inputs 0
        (State.final (.inLeft .word .unit)) (.inLeft .word .unit) [] rfl]
  | some byte =>
      rw [HostStorageDriver.run_of_suspended_inputDataByte?_some
        context inputs 5 0 _ observedOffset byte [] []
        inputByteProgram_suspends response]
      change
        (HostStorageDriver.run context inputs 0
          (State.final (.inRight .unit (.word byte)))).context = context
      rw [HostStorageDriver.run_of_done context inputs 0
        (State.final (.inRight .unit (.word byte)))
        (.inRight .unit (.word byte)) [] rfl]

/-- Varying only input bytes preserves the exact completed driver context. -/
private theorem inputByte_run_context_independent
    (context : HostStorageDriver.Context Nat (List Nat))
    (first second : HostStorageDriver.InputData) :
    (inputByteCode.runWithStorage context (inputsFor_variant first) 5).context =
      (inputByteCode.runWithStorage context (inputsFor_variant second) 5).context :=
  (inputByte_runWithStorage_preserves_context context (inputsFor_variant first)).trans
    (inputByte_runWithStorage_preserves_context
      context (inputsFor_variant second)).symm

private theorem inputByte_outcome_of_some
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (byte : Word)
    (present : inputs.inputData.byte? observedOffset = some byte) :
    (inputByteCode.runWithStorage context inputs 5).outcome =
      .done (.inRight .unit (.word byte)) [] := by
  unfold CheckedHostCoreProgram.runWithStorage
  change
    (HostStorageDriver.run context inputs 5
      (State.initial inputByteProgram.body hostEnvironment)).outcome = _
  rw [HostStorageDriver.run_of_suspended_inputDataByte?_some
    context inputs 5 0 _ observedOffset byte [] []
    inputByteProgram_suspends present]
  change
    (HostStorageDriver.run context inputs 0
      (State.final (.inRight .unit (.word byte)))).outcome = _
  rw [HostStorageDriver.run_of_done context inputs 0
    (State.final (.inRight .unit (.word byte)))
    (.inRight .unit (.word byte)) [] rfl]

private theorem inputByte_outcome_of_none
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (absent : inputs.inputData.byte? observedOffset = none) :
    (inputByteCode.runWithStorage context inputs 5).outcome =
      .done (.inLeft .word .unit) [] := by
  unfold CheckedHostCoreProgram.runWithStorage
  change
    (HostStorageDriver.run context inputs 5
      (State.initial inputByteProgram.body hostEnvironment)).outcome = _
  rw [HostStorageDriver.run_of_suspended_inputDataByte?_none
    context inputs 5 0 _ observedOffset [] []
    inputByteProgram_suspends absent]
  change
    (HostStorageDriver.run context inputs 0
      (State.final (.inLeft .word .unit))).outcome = _
  rw [HostStorageDriver.run_of_done context inputs 0
    (State.final (.inLeft .word .unit)) (.inLeft .word .unit) [] rfl]

private theorem nonzero_outcome_exact
    (context : HostStorageDriver.Context Nat (List Nat)) :
    (inputByteCode.runWithStorage context nonzeroInputs 5).outcome =
      .done (.inRight .unit (.word expectedByte)) [] :=
  inputByte_outcome_of_some context nonzeroInputs expectedByte (by decide)

private theorem zero_outcome_exact
    (context : HostStorageDriver.Context Nat (List Nat)) :
    (inputByteCode.runWithStorage context zeroInputs 5).outcome =
      .done (.inRight .unit (.word Word.zero)) [] :=
  inputByte_outcome_of_some context zeroInputs Word.zero (by decide)

private theorem absent_outcome_exact
    (context : HostStorageDriver.Context Nat (List Nat)) :
    (inputByteCode.runWithStorage context absentInputs 5).outcome =
      .done (.inLeft .word .unit) [] :=
  inputByte_outcome_of_none context absentInputs (by decide)

private def assertCompleted
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) (expected : Value) (label : String) : IO Unit := do
  match context.runCodeWithStorage? inputs fuel with
  | none =>
      throw (IO.userError s!"{label}: the code Account was not selected")
  | some result =>
      assertTrue (result.outcome == .done expected [])
        s!"{label}: optional input-byte result was not exact"
      assertTrue (contextLooksUnchanged result.context)
        s!"{label}: read-only observation mutated the frame context"

def testAddressSelectedHostInputData : IO Unit := do
  assertTrue inputByteProgram.checkHost
    "the host checker rejected the optional input-byte program"
  assertTrue (!inputByteProgram.check)
    "the closed checker accepted the host-only input-byte program"

  match baseContext_variant.withPresentStorageAccount? with
  | none =>
      throw (IO.userError "the working storage Account did not refine")
  | some context =>
      assertTrue
        (context.runCodeWithStorage?
          { nonzeroInputs with codeAddress := absentAddress } 5).isNone
        "an absent code selector unexpectedly executed"
      assertTrue
        (context.runCodeWithStorage?
          { nonzeroInputs with codeAddress := storageAddress } 5).isNone
        "the storage Account was used as a code fallback"

      match context.runCodeWithStorage? nonzeroInputs 4 with
      | none =>
          throw (IO.userError "the code Account disappeared at the fuel boundary")
      | some result =>
          assertTrue (result.outcome == .outOfFuel requestReadyState)
            "fuel 4 did not stop at the request-ready state"
          assertTrue (contextLooksUnchanged result.context)
            "the request-ready boundary mutated the frame context"
          assertTrue
            (hostAdvance requestReadyState ==
              .suspended ⟨.inputDataByte? observedOffset, [], []⟩)
            "the fuel boundary did not expose the exact input-byte request"

      assertCompleted context nonzeroInputs 5
        (.inRight .unit (.word expectedByte)) "present nonzero byte"
      assertCompleted context zeroInputs 5
        (.inRight .unit (.word Word.zero)) "present zero byte"
      assertCompleted context absentInputs 5
        (.inLeft .word .unit) "absent byte"

      assertCompleted context nonzeroInputs 32
        (.inRight .unit (.word expectedByte)) "larger-fuel nonzero byte"
      assertCompleted context zeroInputs 32
        (.inRight .unit (.word Word.zero)) "larger-fuel zero byte"
      assertCompleted context absentInputs 32
        (.inLeft .word .unit) "larger-fuel absent byte"

end Tests
end

section
-- leanmerge: from Solcore.Test.AddressSelectedHostInputDataParent
/-! Parent-indexed completion of byte-derived selected-storage execution. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def targetSlot : Word := ⟨0x42, by decide⟩
private def oldValue : Word := ⟨0x51, by decide⟩
private def observedOffset_variant : Word := ⟨0, by decide⟩
private def expectedByte_variant : Word := ⟨0x12, by decide⟩
private def missingSentinel : Word := ⟨0x100, by decide⟩

private def inputData_variant : HostStorageDriver.InputData := {
  bytes := [0x12, 0x00, 0xff].toByteArray
  size_lt_wordModulus := by decide
}

private def executionInputs : HostStorageDriver.ExecutionInputs := {
  codeAddress := codeAddress
  callValue := ⟨0x73, by decide⟩
  callerAddress := callerAddress
  inputData := inputData_variant
  currentAddress := codeAddress
}

/-- Read, case-unpack, write, read again, and retain both exact bytes. -/
private def observeCaseWriteObserveProgram : Program := {
  resultType := .product .word .word
  body :=
    .caseE
      (.apply
        (.var HostFunction.inputDataByte?.index)
        (.word observedOffset_variant))
      (.pair (.word missingSentinel) (.word missingSentinel))
      (.letE
        (.apply
          (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word targetSlot) (.var 0)))
        (.caseE
          (.apply
            (.var (HostFunction.inputDataByte?.index + 2))
            (.word observedOffset_variant))
          (.pair (.var 2) (.word missingSentinel))
          (.pair (.var 2) (.var 0))))
}

private theorem observeCaseWriteObserveProgram_host_checked :
    observeCaseWriteObserveProgram.checkHost = true := by
  decide

private def observeCaseWriteObserveCode : CheckedHostCoreProgram :=
  ⟨observeCaseWriteObserveProgram,
    observeCaseWriteObserveProgram_host_checked⟩

private def storageAccount_variant2 : Account :=
  Account.empty.storageWrite targetSlot oldValue

private def workingWorld_variant2 : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress
      (Account.empty.withCode observeCaseWriteObserveCode)
    |>.putAccount storageAddress storageAccount_variant2

private def checkpointWorld_variant2 : WorldState :=
  WorldState.empty.putAccount storageAddress Account.empty

private def parentWorking :
    WorldState × FrameEffectJournal Nat (FrameTrace Nat) :=
  (checkpointWorld_variant2, ⟨101, FrameTrace.empty⟩)

private def initialization :
    ParentIndexedFrameInitialization Nat Nat parentWorking := {
  initialWorld := workingWorld_variant2
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
  initialWorld := WorldState.empty.putAccount storageAddress storageAccount_variant2
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
      if first = expectedByte_variant ∧ second = expectedByte_variant ∧
          context.readStorage targetSlot = expectedByte_variant then
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
      suspension.request == .inputDataByte? observedOffset_variant
  | _ => false

private def oneStepBeforeResult (state : State) : Bool :=
  match hostAdvance state with
  | .next next =>
      next == State.final
        (.pair (.word expectedByte_variant) (.word expectedByte_variant))
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
  assertTrue (inputData_variant.byte? observedOffset_variant == some expectedByte_variant)
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
            (resultContext.readStorage targetSlot == expectedByte_variant)
            "fuel 23 lost the byte-derived storage write"
      | _ => throw (IO.userError "fuel 23 crossed its measured boundary")

      match context.runCodeWithStorage? executionInputs 29 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (oneStepBeforeResult state)
            "fuel 29 did not stop one step before the byte pair"
          assertTrue
            (resultContext.readStorage targetSlot == expectedByte_variant)
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
        (foldResult continuation == (some expectedByte_variant, terminalBytes))
        "the parent fold lost byte-derived storage or terminal bytes"
      assertTrue (foldResult largerContinuation == foldResult continuation)
        "fuel 32 changed the exact parent fold result"
      assertTrue
        (largerContinuation.result.outcome == continuation.result.outcome)
        "fuel 32 changed the completed parent outcome"
  | _, _ =>
      throw (IO.userError "input-byte execution did not complete its parent")

end Tests
end

section
-- leanmerge: from Solcore.Test.AddressSelectedHostInputDataSize
/-! End-to-end regressions for exact run-fixed input-size observation. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def emptyInput : HostStorageDriver.InputData := {
  bytes := [].toByteArray
  size_lt_wordModulus := by decide
}

private def nonemptyInput : HostStorageDriver.InputData := {
  bytes := [0xa5, 0x00, 0x7f].toByteArray
  size_lt_wordModulus := by decide
}

private def expectedNonemptySize : Word := ⟨3, by decide⟩

private def emptyInputs := inputsFor_variant emptyInput
private def nonemptyInputs := inputsFor_variant nonemptyInput

private def inputSizeProgram : Program := {
  resultType := .word
  body := .apply (.var HostFunction.inputDataSize.index) .unit
}

private theorem inputSizeProgram_host_checked :
    inputSizeProgram.checkHost = true := by
  decide

private theorem inputSizeProgram_closed_rejected :
    inputSizeProgram.check = false := by
  decide

private def inputSizeCode : CheckedHostCoreProgram :=
  ⟨inputSizeProgram, inputSizeProgram_host_checked⟩

private def codeAccount_variant2 : Account :=
  Account.empty.withCode inputSizeCode

private def workingWorld_variant3 : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress codeAccount_variant2
    |>.putAccount storageAddress storageAccount_variant

private def baseContext_variant2 :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨storageAddress,
    ⟨⟨checkpointWorld_variant, ⟨7, [8]⟩⟩,
      (workingWorld_variant3, ⟨9, [10, 11]⟩)⟩⟩

private def requestReadyState_variant : State :=
  ⟨.ret .unit, [.hostApply .inputDataSize], []⟩

private theorem inputSizeProgram_stops_request_ready :
    hostRun 4 (State.initial inputSizeProgram.body hostEnvironment) =
      .outOfFuel requestReadyState_variant := by
  native_decide

private theorem inputSizeProgram_suspends :
    hostRun 5 (State.initial inputSizeProgram.body hostEnvironment) =
      .suspended ⟨.inputDataSize, [], []⟩ 0 := by
  decide

/-- Exact handled execution returns the derived size without changing context. -/
private theorem inputSize_run_exact
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs) :
    inputSizeCode.runWithStorage context inputs 5 =
      ⟨context, .done (.word inputs.inputData.sizeWord) []⟩ := by
  unfold CheckedHostCoreProgram.runWithStorage
  change
    HostStorageDriver.run context inputs 5
        (State.initial inputSizeProgram.body hostEnvironment) = _
  rw [HostStorageDriver.run_of_suspended_inputDataSize
    context inputs 5 0 _ [] [] inputSizeProgram_suspends]
  change
    HostStorageDriver.run context inputs 0
        (State.final (.word inputs.inputData.sizeWord)) = _
  rw [HostStorageDriver.run_of_done context inputs 0
    (State.final (.word inputs.inputData.sizeWord))
    (.word inputs.inputData.sizeWord) [] rfl]

/-- Read-only size observation preserves the entire completed driver context. -/
private theorem inputSize_runWithStorage_preserves_context
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs) :
    (inputSizeCode.runWithStorage context inputs 5).context = context := by
  rw [inputSize_run_exact]

/-- Changing only input data cannot change any part of the completed context. -/
private theorem inputSize_run_context_independent
    (context : HostStorageDriver.Context Nat (List Nat))
    (first second : HostStorageDriver.InputData) :
    (inputSizeCode.runWithStorage context (inputsFor_variant first) 5).context =
      (inputSizeCode.runWithStorage context (inputsFor_variant second) 5).context := by
  rw [inputSize_runWithStorage_preserves_context,
    inputSize_runWithStorage_preserves_context]

private theorem inputSize_outcome_exact
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs) :
    (inputSizeCode.runWithStorage context inputs 5).outcome =
      .done (.word inputs.inputData.sizeWord) [] := by
  rw [inputSize_run_exact]

private theorem empty_outcome_exact
    (context : HostStorageDriver.Context Nat (List Nat)) :
    (inputSizeCode.runWithStorage context emptyInputs 5).outcome =
      .done (.word Word.zero) [] := by
  rw [inputSize_outcome_exact]
  rw [show emptyInputs.inputData.sizeWord = Word.zero by
    apply Fin.ext
    rfl]

private theorem nonempty_outcome_exact
    (context : HostStorageDriver.Context Nat (List Nat)) :
    (inputSizeCode.runWithStorage context nonemptyInputs 5).outcome =
      .done (.word expectedNonemptySize) [] := by
  rw [inputSize_outcome_exact]
  rw [show nonemptyInputs.inputData.sizeWord = expectedNonemptySize by
    apply Fin.ext
    rfl]

private theorem input_only_variation_changes_outcome
    (context : HostStorageDriver.Context Nat (List Nat)) :
    (inputSizeCode.runWithStorage context emptyInputs 5).outcome ≠
      (inputSizeCode.runWithStorage context nonemptyInputs 5).outcome := by
  rw [empty_outcome_exact, nonempty_outcome_exact]
  intro equal
  have sizesEqual : Word.zero = expectedNonemptySize := by
    exact Value.word.inj (HostDriverOutcome.done.inj equal).1
  have valuesEqual := congrArg Fin.val sizesEqual
  simp [Word.zero, expectedNonemptySize] at valuesEqual

/-- A completed size observation retains its exact context and result at fuel 32. -/
private theorem inputSize_run_stable
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs) :
    inputSizeCode.runWithStorage context inputs 32 =
      ⟨context, .done (.word inputs.inputData.sizeWord) []⟩ :=
  inputSizeCode.runWithStorage_done_stable context inputs
    (inputSize_run_exact context inputs) (by decide)

private def assertCompleted_variant
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) (expected : Word) (label : String) : IO Unit := do
  match context.runCodeWithStorage? inputs fuel with
  | none =>
      throw (IO.userError s!"{label}: the code Account was not selected")
  | some result =>
      assertTrue (result.outcome == .done (.word expected) [])
        s!"{label}: input size was not returned exactly"
      assertTrue (contextLooksUnchanged result.context)
        s!"{label}: read-only size observation mutated the frame context"

def testAddressSelectedHostInputDataSize : IO Unit := do
  assertTrue inputSizeProgram.checkHost
    "the host checker rejected the input-size program"
  assertTrue (!inputSizeProgram.check)
    "the closed checker accepted the host-only input-size program"
  assertTrue (emptyInput.sizeWord == Word.zero)
    "empty input did not expose exact size zero"
  assertTrue (nonemptyInput.sizeWord == expectedNonemptySize)
    "nonempty input did not expose its exact byte count"

  match baseContext_variant2.withPresentStorageAccount? with
  | none =>
      throw (IO.userError "the working storage Account did not refine")
  | some context =>
      assertTrue
        (context.runCodeWithStorage?
          { nonemptyInputs with codeAddress := absentAddress } 5).isNone
        "an absent code selector unexpectedly executed"
      assertTrue
        (context.runCodeWithStorage?
          { nonemptyInputs with codeAddress := storageAddress } 5).isNone
        "the storage Account was used as a code fallback"

      match context.runCodeWithStorage? nonemptyInputs 4 with
      | none =>
          throw (IO.userError "the code Account disappeared at the fuel boundary")
      | some result =>
          assertTrue (result.outcome == .outOfFuel requestReadyState_variant)
            "fuel 4 did not stop at the input-size request-ready state"
          assertTrue (contextLooksUnchanged result.context)
            "the request-ready boundary mutated the frame context"
          assertTrue
            (hostAdvance requestReadyState_variant ==
              .suspended ⟨.inputDataSize, [], []⟩)
            "the fuel boundary did not expose the exact input-size request"

      assertCompleted_variant context emptyInputs 5 Word.zero "empty input"
      assertCompleted_variant context nonemptyInputs 5 expectedNonemptySize
        "nonempty input"
      assertCompleted_variant context emptyInputs 32 Word.zero
        "larger-fuel empty input"
      assertCompleted_variant context nonemptyInputs 32 expectedNonemptySize
        "larger-fuel nonempty input"

      match context.runCodeWithStorage? emptyInputs 5,
          context.runCodeWithStorage? nonemptyInputs 5,
          context.runCodeWithStorage? nonemptyInputs 32 with
      | some emptyResult, some nonemptyResult, some largerResult =>
          assertTrue (emptyResult.outcome != nonemptyResult.outcome)
            "changing only input data did not change the observed size"
          assertTrue
            (nonemptyResult.outcome == largerResult.outcome &&
              contextLooksUnchanged emptyResult.context &&
              contextLooksUnchanged nonemptyResult.context &&
              contextLooksUnchanged largerResult.context)
            "input-only variation or larger fuel changed the completed context"
      | _, _, _ =>
          throw (IO.userError "input-size execution lost the selected code")

end Tests
end

section
-- leanmerge: from Solcore.Test.AddressSelectedHostInputDataSizeParent
/-! Parent-indexed completion of input-size-derived selected-storage execution. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def expectedSize : Word := ⟨3, by decide⟩

/-- Observe the exact size, write it, observe it again, and retain both Words. -/
private def observeWriteObserveProgram : Program := {
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

private theorem observeWriteObserveProgram_host_checked :
    observeWriteObserveProgram.checkHost = true := by
  decide

private def observeWriteObserveCode : CheckedHostCoreProgram :=
  ⟨observeWriteObserveProgram, observeWriteObserveProgram_host_checked⟩

private def workingWorld_variant4 : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress (Account.empty.withCode observeWriteObserveCode)
    |>.putAccount storageAddress storageAccount_variant2

private def initialization_variant :
    ParentIndexedFrameInitialization Nat Nat parentWorking := {
  initialWorld := workingWorld_variant4
  workingRollback := 201
}

private def missingStorageInitialization_variant :
    ParentIndexedFrameInitialization Nat Nat parentWorking := {
  initialWorld := WorldState.empty.putAccount codeAddress
    (Account.empty.withCode observeWriteObserveCode)
  workingRollback := 201
}

private inductive InputDataSizeTrapReason where
  | invalidDoneInputs
  deriving Repr, BEq, DecidableEq

private def terminalBytes_variant : Bytes := [0xc5, 0xd6].toByteArray

private def doneOutcome_variant
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (value : Value)
    (store : Store) : FrameOutcome InputDataSizeTrapReason :=
  match value, store with
  | .pair (.word first) (.word second), [] =>
      if first = expectedSize ∧ second = expectedSize ∧
          context.readStorage targetSlot = expectedSize then
        .returned terminalBytes_variant
      else
        .trapped .invalidDoneInputs
  | _, _ => .trapped .invalidDoneInputs

private def foldResult_variant
    (continuation :
      ParentIndexedFrameContinuationContext
        Nat Nat InputDataSizeTrapReason parentWorking) : Option Word × Bytes :=
  continuation.foldResolutionWithTrapRollback
    (fun values data =>
      (storageValueAt? values.1 storageAddress targetSlot, data))
    (fun _ data => (none, data))
    (fun _ _ => (none, ByteArray.empty))

private def inputDataSizeRequestReady (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension => suspension.request == .inputDataSize
  | _ => false

private def oneStepBeforeResult_variant (state : State) : Bool :=
  match hostAdvance state with
  | .next next =>
      next == State.final
        (.pair (.word expectedSize) (.word expectedSize))
  | _ => false

/-- The exact parent continuation at fuel 30 survives fuel 32. -/
private theorem parentCompletion_done_stable_variant
    {continuation :
      ParentIndexedFrameContinuationContext
        Nat Nat InputDataSizeTrapReason parentWorking}
    (completed :
      initialization_variant.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress executionInputs 30 doneOutcome_variant =
        some (some (some continuation))) :
    initialization_variant.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress executionInputs 32 doneOutcome_variant =
      some (some (some continuation)) :=
  initialization_variant.runCodeWithStorageParentIndexedContinuationContext?_some_some_some_stable
    storageAddress executionInputs doneOutcome_variant completed (by decide)

def testAddressSelectedHostInputDataSizeParent : IO Unit := do
  assertTrue observeWriteObserveProgram.checkHost
    "the host checker rejected the parent input-size consumer"
  assertTrue (inputData_variant.sizeWord == expectedSize)
    "the parent fixture did not expose its exact size"

  match missingStorageInitialization_variant
      |>.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress executionInputs 30 doneOutcome_variant with
  | none => pure ()
  | _ => throw (IO.userError "missing storage crossed the outer Option")

  match missingCodeInitialization
      |>.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress executionInputs 30 doneOutcome_variant with
  | some none => pure ()
  | _ => throw (IO.userError "missing code crossed the middle Option")

  match initialization_variant.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress with
  | none => throw (IO.userError "the parent storage Account was absent")
  | some context =>
      match context.runCodeWithStorage? executionInputs 23 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (inputDataSizeRequestReady state)
            "fuel 23 did not stop at the second input-size request"
          assertTrue (resultContext.readStorage targetSlot == expectedSize)
            "fuel 23 lost the input-size-derived storage write"
      | _ => throw (IO.userError "fuel 23 crossed its measured boundary")

      match context.runCodeWithStorage? executionInputs 29 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (oneStepBeforeResult_variant state)
            "fuel 29 did not stop one step before the size pair"
          assertTrue (resultContext.readStorage targetSlot == expectedSize)
            "fuel 29 lost the input-size-derived storage write"
      | _ => throw (IO.userError "fuel 29 crossed its measured boundary")

  match initialization_variant
      |>.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress executionInputs 29 doneOutcome_variant with
  | some (some none) => pure ()
  | _ => throw (IO.userError "fuel 29 crossed the inner Option")

  match
      initialization_variant.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress executionInputs 30 doneOutcome_variant,
      initialization_variant.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress executionInputs 32 doneOutcome_variant with
  | some (some (some continuation)),
      some (some (some largerContinuation)) =>
      assertTrue
        (foldResult_variant continuation == (some expectedSize, terminalBytes_variant))
        "the parent fold lost size-derived storage or terminal bytes"
      assertTrue (foldResult_variant largerContinuation == foldResult_variant continuation)
        "fuel 32 changed the exact parent fold result"
      assertTrue
        (largerContinuation.result.outcome == continuation.result.outcome)
        "fuel 32 changed the completed parent outcome"
  | _, _ =>
      throw (IO.userError "input-size execution did not complete its parent")

end Tests
end

section
-- leanmerge: from Solcore.Test.AddressSelectedHostInputDataSizeStorage
/-! End-to-end regression for storing and re-observing exact input size. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def otherAddress : Address := ⟨0x30, by decide⟩
private def targetSlot_variant : Word := ⟨0x51, by decide⟩
private def retainedSlot : Word := ⟨0x52, by decide⟩
private def retainedValue : Word := ⟨0x53, by decide⟩
private def oldValue_variant : Word := ⟨0x54, by decide⟩
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

private def inputsFor_variant2
    (inputData : HostStorageDriver.InputData) :
    HostStorageDriver.ExecutionInputs := {
  codeAddress := codeAddress
  callValue := Word.zero
  callerAddress := callerAddress
  inputData := inputData
  currentAddress := codeAddress
}

private def executionInputs_variant := inputsFor_variant2 threeByteInput
private def alternateInputs := inputsFor_variant2 oneByteInput

/-- Observe size, write that exact Word, then observe the same size again. -/
private def observeSizeWriteObserveProgram : Program := {
  resultType := .product .word .word
  body :=
    .letE
      (.apply (.var HostFunction.inputDataSize.index) .unit)
      (.letE
        (.apply
          (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word targetSlot_variant) (.var 0)))
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
    |>.storageWrite targetSlot_variant oldValue_variant
    |>.storageWrite retainedSlot retainedValue

private def workingWorld_variant5 : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress
      (Account.empty.withCode observeSizeWriteObserveCode)
    |>.putAccount storageAddress selectedStorageAccount
    |>.putAccount otherAddress
      (Account.empty.storageWrite otherSlot otherValue)

private def checkpointWorld_variant3 : WorldState :=
  WorldState.empty
    |>.putAccount storageAddress
      (Account.empty.storageWrite checkpointSlot checkpointValue)
    |>.putAccount otherAddress
      (Account.empty.storageWrite otherSlot otherValue)

private def baseContext_variant3 :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨storageAddress,
    ⟨⟨checkpointWorld_variant3, ⟨11, [12, 13]⟩⟩,
      (workingWorld_variant5, ⟨21, [22, 23]⟩)⟩⟩

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
  context.storageAccount.storageValue? targetSlot_variant == some size &&
    storageValueAt? working storageAddress targetSlot_variant == some size

private def oneStepBeforeResult_variant2 (size : Word) (state : State) : Bool :=
  match hostAdvance state with
  | .next next => next == State.final (expectedPair size)
  | _ => false

private theorem observeSizeWriteObserve_done_stable
    {context : HostStorageDriver.Context Nat (List Nat)}
    {finalContext : HostStorageDriver.Context Nat (List Nat)}
    (execution :
      context.runCodeWithStorage? executionInputs_variant 30 =
        some ⟨finalContext, .done (expectedPair threeByteInput.sizeWord) []⟩) :
    context.runCodeWithStorage? executionInputs_variant 32 =
      some ⟨finalContext, .done (expectedPair threeByteInput.sizeWord) []⟩ :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
    context executionInputs_variant execution (by decide)

def testAddressSelectedHostInputDataSizeStorage : IO Unit := do
  assertTrue observeSizeWriteObserveProgram.checkHost
    "the host checker rejected size/write/size"
  assertTrue (threeByteInput.sizeWord == ⟨3, by decide⟩)
    "the three-byte fixture did not retain its exact size"
  assertTrue (oneByteInput.sizeWord == ⟨1, by decide⟩)
    "the one-byte fixture did not retain its exact size"

  match baseContext_variant3.withPresentStorageAccount? with
  | none => throw (IO.userError "the selected storage Account was absent")
  | some context =>
      match context.runCodeWithStorage? executionInputs_variant 23 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (inputDataSizeRequestReady state)
            "fuel 23 did not stop at the second input-size request"
          assertTrue (storesSize resultContext threeByteInput.sizeWord)
            "fuel 23 lost the size-derived write"
          assertTrue (preservesUnrelated resultContext)
            "fuel 23 changed unrelated frame state"
      | _ => throw (IO.userError "fuel 23 crossed its measured boundary")

      match context.runCodeWithStorage? executionInputs_variant 29 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (oneStepBeforeResult_variant2 threeByteInput.sizeWord state)
            "fuel 29 did not stop one step before the size pair"
          assertTrue (storesSize resultContext threeByteInput.sizeWord)
            "fuel 29 lost the size-derived write"
          assertTrue (preservesUnrelated resultContext)
            "fuel 29 changed unrelated frame state"
      | _ => throw (IO.userError "fuel 29 crossed its measured boundary")

      match context.runCodeWithStorage? executionInputs_variant 30,
          context.runCodeWithStorage? executionInputs_variant 32 with
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
end

section
-- leanmerge: from Solcore.Test.AddressSelectedHostInputDataStorage
/-! End-to-end regression for a byte-derived selected-storage write. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def observedByte : Word := ⟨0x7b, by decide⟩
private def inputData_variant2 : HostStorageDriver.InputData := {
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

private def inputsFor_variant3
    (data : HostStorageDriver.InputData) :
    HostStorageDriver.ExecutionInputs := {
  codeAddress := codeAddress
  callValue := Word.zero
  callerAddress := callerAddress
  inputData := data
  currentAddress := codeAddress
}

private def executionInputs_variant2 : HostStorageDriver.ExecutionInputs :=
  inputsFor_variant3 inputData_variant2

private def zeroExecutionInputs : HostStorageDriver.ExecutionInputs :=
  inputsFor_variant3 zeroInputData

private def absentExecutionInputs : HostStorageDriver.ExecutionInputs :=
  inputsFor_variant3 absentInputData

/--
Observe one optional byte. Absence returns the left sentinel. Presence writes the
exact widened byte, observes the same offset again, and returns both values.
-/
private def observeCaseWriteObserveProgram_variant : Program := {
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
          (.pair (.word targetSlot_variant) (.var 0)))
        (.caseE
          (.apply
            (.var (HostFunction.inputDataByte?.index + 2))
            (.word observedOffset))
          (.inLeft (.product .word .word) .unit)
          (.inRight .unit (.pair (.var 2) (.var 0)))))
}

private theorem observeCaseWriteObserveProgram_host_checked_variant :
    observeCaseWriteObserveProgram_variant.checkHost = true := by
  decide

private def observeCaseWriteObserveCode_variant : CheckedHostCoreProgram :=
  ⟨observeCaseWriteObserveProgram_variant,
    observeCaseWriteObserveProgram_host_checked_variant⟩

private def workingWorld_variant6 : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress
      (Account.empty.withCode observeCaseWriteObserveCode_variant)
    |>.putAccount storageAddress selectedStorageAccount
    |>.putAccount otherAddress
      (Account.empty.storageWrite otherSlot otherValue)

private def baseContext_variant4 :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨storageAddress,
    ⟨⟨checkpointWorld_variant3, ⟨11, [12, 13]⟩⟩,
      (workingWorld_variant6, ⟨21, [22, 23]⟩)⟩⟩

private def expectedResult (byte : Word) : Value :=
  .inRight .unit (.pair (.word byte) (.word byte))

private def expectedAbsence : Value :=
  .inLeft (.product .word .word) .unit

private def codeProgramIs_variant (state : WorldState) : Bool :=
  match state.code? codeAddress with
  | none => false
  | some code => code.program == observeCaseWriteObserveProgram_variant

private def preservesUnrelated_variant
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat)) :
    Bool :=
  let values := context.context.values
  context.context.storageAddress == storageAddress &&
    codeProgramIs_variant values.working.1 &&
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
  context.storageAccount.storageValue? targetSlot_variant == some byte &&
    storageValueAt? working storageAddress targetSlot_variant == some byte

private def inputDataByteRequestReady_variant (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension =>
      suspension.request == .inputDataByte? observedOffset
  | _ => false

private def oneStepBeforeResult_variant3 (byte : Word) (state : State) : Bool :=
  match hostAdvance state with
  | .next next => next == State.final (expectedResult byte)
  | _ => false

private theorem observeCaseWriteObserve_done_stable
    {context : HostStorageDriver.Context Nat (List Nat)}
    {finalContext : HostStorageDriver.Context Nat (List Nat)}
    (execution :
      context.runCodeWithStorage? executionInputs_variant2 32 =
        some ⟨finalContext, .done (expectedResult observedByte) []⟩) :
    context.runCodeWithStorage? executionInputs_variant2 64 =
      some ⟨finalContext, .done (expectedResult observedByte) []⟩ :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
    context executionInputs_variant2 execution (by decide)

def testAddressSelectedHostInputDataStorage : IO Unit := do
  assertTrue observeCaseWriteObserveProgram_variant.checkHost
    "the host checker rejected observe/case/write/observe"
  assertTrue (inputData_variant2.byte? observedOffset == some observedByte)
    "the fixture byte did not widen exactly"

  match baseContext_variant4.withPresentStorageAccount? with
  | none =>
      throw (IO.userError "the selected storage Account was absent")
  | some context =>
      match context.runCodeWithStorage? executionInputs_variant2 23 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (inputDataByteRequestReady_variant state)
            "fuel 23 did not stop at the second byte observation"
          assertTrue (storesNonzeroByte resultContext observedByte)
            "fuel 23 lost the byte-derived write"
          assertTrue (preservesUnrelated_variant resultContext)
            "fuel 23 changed unrelated context state"
      | some result =>
          throw (IO.userError
            s!"fuel 23 crossed the second observation: {reprStr result.outcome}")
      | none =>
          throw (IO.userError "fuel 23 lost the selected code")

      match context.runCodeWithStorage? executionInputs_variant2 31 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (oneStepBeforeResult_variant3 observedByte state)
            "fuel 31 did not stop one step before the successful pair"
          assertTrue (storesNonzeroByte resultContext observedByte)
            "fuel 31 lost the byte-derived write"
          assertTrue (preservesUnrelated_variant resultContext)
            "fuel 31 changed unrelated context state"
      | some result =>
          throw (IO.userError
            s!"fuel 31 crossed the completion boundary: {reprStr result.outcome}")
      | none =>
          throw (IO.userError "fuel 31 lost the selected code")

      match context.runCodeWithStorage? executionInputs_variant2 32,
          context.runCodeWithStorage? executionInputs_variant2 64 with
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
            (preservesUnrelated_variant result.context &&
              preservesUnrelated_variant largerResult.context)
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
            ((result.context.storageAccount.storageValue? targetSlot_variant).isNone &&
              result.context.storageAccount.storageRead targetSlot_variant == Word.zero)
            "the present zero byte did not perform the sparse zero write"
          assertTrue (preservesUnrelated_variant result.context)
            "the present-zero run changed unrelated context state"
      | none =>
          throw (IO.userError "the present-zero run lost the selected code")

      match context.runCodeWithStorage? absentExecutionInputs 32 with
      | some result =>
          assertTrue (result.outcome == .done expectedAbsence [])
            "an absent byte did not follow the typed left sentinel branch"
          assertTrue (result.context.storageAccount.storageRead targetSlot_variant == oldValue_variant)
            "the absence branch performed a storage write"
          assertTrue (preservesUnrelated_variant result.context)
            "the absence branch changed unrelated context state"
      | none =>
          throw (IO.userError "the absence run lost the selected code")

end Tests
end

section
-- leanmerge: from Solcore.Test.AddressSelectedHostInputWordBE
/-! End-to-end regressions for strict optional big-endian input-word reads. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def expectedWord : Word := ⟨0x01020304, by decide⟩

private def presentInput : HostStorageDriver.InputData := {
  bytes := [0xaa].toByteArray.append (encodeWordBytesBE expectedWord)
  size_lt_wordModulus := by native_decide
}

private def zeroInput_variant : HostStorageDriver.InputData := {
  bytes := [0xaa].toByteArray.append (encodeWordBytesBE Word.zero)
  size_lt_wordModulus := by native_decide
}

private def incompleteInput : HostStorageDriver.InputData := {
  bytes := [0xaa, 0x01].toByteArray
  size_lt_wordModulus := by decide
}

private def presentInputs := inputsFor_variant presentInput
private def zeroInputs_variant := inputsFor_variant zeroInput_variant
private def incompleteInputs := inputsFor_variant incompleteInput

private def inputWordProgram : Program := {
  resultType := .sum .unit .word
  body :=
    .apply (.var HostFunction.inputDataWordBE?.index) (.word observedOffset)
}

private theorem inputWordProgram_host_checked :
    inputWordProgram.checkHost = true := by
  decide

private theorem inputWordProgram_closed_rejected :
    inputWordProgram.check = false := by
  decide

private def inputWordCode : CheckedHostCoreProgram :=
  ⟨inputWordProgram, inputWordProgram_host_checked⟩

private def codeAccount_variant3 : Account :=
  Account.empty.withCode inputWordCode

private def workingWorld_variant7 : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress codeAccount_variant3
    |>.putAccount storageAddress storageAccount_variant

private def baseContext_variant5 :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨storageAddress,
    ⟨⟨checkpointWorld_variant, ⟨7, [8]⟩⟩,
      (workingWorld_variant7, ⟨9, [10, 11]⟩)⟩⟩

private def requestReadyState_variant2 : State :=
  ⟨.ret (.word observedOffset), [.hostApply .inputDataWordBE?], []⟩

private theorem inputWordProgram_suspends :
    hostRun 5 (State.initial inputWordProgram.body hostEnvironment) =
      .suspended ⟨.inputDataWordBE? observedOffset, [], []⟩ 0 := by
  decide

private theorem inputWord_runWithStorage_preserves_context
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs) :
    (inputWordCode.runWithStorage context inputs 5).context = context := by
  unfold CheckedHostCoreProgram.runWithStorage
  change
    (HostStorageDriver.run context inputs 5
      (State.initial inputWordProgram.body hostEnvironment)).context = context
  cases response : inputs.inputData.wordBE? observedOffset with
  | none =>
      rw [HostStorageDriver.run_of_suspended_inputDataWordBE?_none
        context inputs 5 0 _ observedOffset [] []
        inputWordProgram_suspends response]
      change
        (HostStorageDriver.run context inputs 0
          (State.final (.inLeft .word .unit))).context = context
      rw [HostStorageDriver.run_of_done context inputs 0
        (State.final (.inLeft .word .unit)) (.inLeft .word .unit) [] rfl]
  | some word =>
      rw [HostStorageDriver.run_of_suspended_inputDataWordBE?_some
        context inputs 5 0 _ observedOffset word [] []
        inputWordProgram_suspends response]
      change
        (HostStorageDriver.run context inputs 0
          (State.final (.inRight .unit (.word word)))).context = context
      rw [HostStorageDriver.run_of_done context inputs 0
        (State.final (.inRight .unit (.word word)))
        (.inRight .unit (.word word)) [] rfl]

private theorem inputWord_outcome_of_some
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (word : Word)
    (present : inputs.inputData.wordBE? observedOffset = some word) :
    (inputWordCode.runWithStorage context inputs 5).outcome =
      .done (.inRight .unit (.word word)) [] := by
  unfold CheckedHostCoreProgram.runWithStorage
  change
    (HostStorageDriver.run context inputs 5
      (State.initial inputWordProgram.body hostEnvironment)).outcome = _
  rw [HostStorageDriver.run_of_suspended_inputDataWordBE?_some
    context inputs 5 0 _ observedOffset word [] []
    inputWordProgram_suspends present]
  change
    (HostStorageDriver.run context inputs 0
      (State.final (.inRight .unit (.word word)))).outcome = _
  rw [HostStorageDriver.run_of_done context inputs 0
    (State.final (.inRight .unit (.word word)))
    (.inRight .unit (.word word)) [] rfl]

private theorem inputWord_outcome_of_none
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (absent : inputs.inputData.wordBE? observedOffset = none) :
    (inputWordCode.runWithStorage context inputs 5).outcome =
      .done (.inLeft .word .unit) [] := by
  unfold CheckedHostCoreProgram.runWithStorage
  change
    (HostStorageDriver.run context inputs 5
      (State.initial inputWordProgram.body hostEnvironment)).outcome = _
  rw [HostStorageDriver.run_of_suspended_inputDataWordBE?_none
    context inputs 5 0 _ observedOffset [] []
    inputWordProgram_suspends absent]
  change
    (HostStorageDriver.run context inputs 0
      (State.final (.inLeft .word .unit))).outcome = _
  rw [HostStorageDriver.run_of_done context inputs 0
    (State.final (.inLeft .word .unit)) (.inLeft .word .unit) [] rfl]

private theorem present_outcome_exact
    (context : HostStorageDriver.Context Nat (List Nat)) :
    (inputWordCode.runWithStorage context presentInputs 5).outcome =
      .done (.inRight .unit (.word expectedWord)) [] :=
  inputWord_outcome_of_some context presentInputs expectedWord (by native_decide)

private theorem zero_outcome_exact_variant
    (context : HostStorageDriver.Context Nat (List Nat)) :
    (inputWordCode.runWithStorage context zeroInputs_variant 5).outcome =
      .done (.inRight .unit (.word Word.zero)) [] :=
  inputWord_outcome_of_some context zeroInputs_variant Word.zero (by native_decide)

private theorem incomplete_outcome_exact
    (context : HostStorageDriver.Context Nat (List Nat)) :
    (inputWordCode.runWithStorage context incompleteInputs 5).outcome =
      .done (.inLeft .word .unit) [] :=
  inputWord_outcome_of_none context incompleteInputs (by native_decide)

private def assertCompleted_variant2
    (context : HostStorageDriver.Context Nat (List Nat))
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) (expected : Value) (label : String) : IO Unit := do
  match context.runCodeWithStorage? inputs fuel with
  | none =>
      throw (IO.userError s!"{label}: the code Account was not selected")
  | some result =>
      assertTrue (result.outcome == .done expected [])
        s!"{label}: strict input-word result was not exact"
      assertTrue (contextLooksUnchanged result.context)
        s!"{label}: read-only input-word observation mutated the context"

def testAddressSelectedHostInputWordBE : IO Unit := do
  assertTrue inputWordProgram.checkHost
    "the host checker rejected the strict input-word program"
  assertTrue (!inputWordProgram.check)
    "the closed checker accepted the host-only input-word program"
  assertTrue (presentInput.wordBE? observedOffset == some expectedWord)
    "a complete big-endian window did not decode exactly"
  assertTrue (zeroInput_variant.wordBE? observedOffset == some Word.zero)
    "a complete zero window was confused with absence"
  assertTrue ((incompleteInput.wordBE? observedOffset).isNone)
    "an incomplete window was padded instead of rejected"

  match baseContext_variant5.withPresentStorageAccount? with
  | none => throw (IO.userError "the working storage Account did not refine")
  | some context =>
      assertTrue
        (context.runCodeWithStorage?
          { presentInputs with codeAddress := absentAddress } 5).isNone
        "an absent code selector unexpectedly executed"
      assertTrue
        (context.runCodeWithStorage?
          { presentInputs with codeAddress := storageAddress } 5).isNone
        "the storage Account was used as a code fallback"

      match context.runCodeWithStorage? presentInputs 4 with
      | none => throw (IO.userError "the code Account disappeared at fuel 4")
      | some result =>
          assertTrue (result.outcome == .outOfFuel requestReadyState_variant2)
            "fuel 4 did not stop at the input-word request-ready state"
          assertTrue (contextLooksUnchanged result.context)
            "the request-ready boundary mutated the frame context"
          assertTrue
            (hostAdvance requestReadyState_variant2 ==
              .suspended ⟨.inputDataWordBE? observedOffset, [], []⟩)
            "the boundary did not expose the exact input-word request"

      assertCompleted_variant2 context presentInputs 5
        (.inRight .unit (.word expectedWord)) "complete nonzero window"
      assertCompleted_variant2 context zeroInputs_variant 5
        (.inRight .unit (.word Word.zero)) "complete zero window"
      assertCompleted_variant2 context incompleteInputs 5
        (.inLeft .word .unit) "incomplete window"
      assertCompleted_variant2 context presentInputs 32
        (.inRight .unit (.word expectedWord)) "larger-fuel complete window"
      assertCompleted_variant2 context incompleteInputs 32
        (.inLeft .word .unit) "larger-fuel incomplete window"

end Tests
end

section
-- leanmerge: from Solcore.Test.AddressSelectedHostInputWordBEParent
/-! Parent-indexed completion of strict optional input-word execution. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def inputsFor_variant4 (inputData : HostStorageDriver.InputData) :
    HostStorageDriver.ExecutionInputs := {
  codeAddress := codeAddress
  callValue := ⟨0x73, by decide⟩
  callerAddress := callerAddress
  inputData := inputData
  currentAddress := codeAddress
}

private def presentInputs_variant := inputsFor_variant4 presentInput
private def incompleteInputs_variant := inputsFor_variant4 incompleteInput

/-- Presence writes and re-observes the exact Word; absence returns sentinels. -/
private def observeCaseWriteObserveProgram_variant2 : Program := {
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

private theorem observeCaseWriteObserveProgram_host_checked_variant2 :
    observeCaseWriteObserveProgram_variant2.checkHost = true := by decide

private def observeCaseWriteObserveCode_variant2 : CheckedHostCoreProgram :=
  ⟨observeCaseWriteObserveProgram_variant2,
    observeCaseWriteObserveProgram_host_checked_variant2⟩

private def workingWorld_variant8 : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress
      (Account.empty.withCode observeCaseWriteObserveCode_variant2)
    |>.putAccount storageAddress storageAccount_variant2

private def initialization_variant2 :
    ParentIndexedFrameInitialization Nat Nat parentWorking := {
  initialWorld := workingWorld_variant8
  workingRollback := 201
}

private def missingStorageInitialization_variant2 :
    ParentIndexedFrameInitialization Nat Nat parentWorking := {
  initialWorld := WorldState.empty.putAccount codeAddress
    (Account.empty.withCode observeCaseWriteObserveCode_variant2)
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

private def codeProgramIs_variant2 (state : WorldState) : Bool :=
  match state.code? codeAddress with
  | none => false
  | some code => code.program == observeCaseWriteObserveProgram_variant2

private def foldResult_variant2
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
    codeProgramIs_variant2 continuation.result.working

private theorem continuation_parent_index_exact
    (continuation :
      ParentIndexedFrameContinuationContext Nat Nat InputWordBETrapReason
        parentWorking) :
    (continuation.stateCheckpoint, continuation.effectCheckpoint) =
      parentWorking :=
  continuation.checkpoint_eq_parentWorking

/-- A completed indexed continuation is exactly stable at every larger budget. -/
private theorem parentCompletion_done_stable_variant2
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome : HostStorageDriver.Context Nat (FrameTrace Nat) →
      Value → Store → FrameOutcome InputWordBETrapReason)
    {fuel largerFuel : Nat}
    {continuation :
      ParentIndexedFrameContinuationContext Nat Nat InputWordBETrapReason
        parentWorking}
    (completed :
      initialization_variant2.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome =
        some (some (some continuation)))
    (more : fuel ≤ largerFuel) :
    initialization_variant2.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress inputs largerFuel doneOutcome =
      some (some (some continuation)) :=
  initialization_variant2.runCodeWithStorageParentIndexedContinuationContext?_some_some_some_stable
    storageAddress inputs doneOutcome completed more

private def inputWordRequestReady (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension =>
      suspension.request == .inputDataWordBE? observedOffset
  | _ => false

private def oneStepBeforeResult_variant4 (expected : Word) (state : State) : Bool :=
  match hostAdvance state with
  | .next next => next == State.final (.pair (.word expected) (.word expected))
  | _ => false

private def assertMissingLayers
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome : HostStorageDriver.Context Nat (FrameTrace Nat) →
      Value → Store → FrameOutcome InputWordBETrapReason)
    (fuel : Nat) (label : String) : IO Unit := do
  match missingStorageInitialization_variant2
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
      initialization_variant2.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress inputs fuel doneOutcome,
      initialization_variant2.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress inputs largerFuel doneOutcome with
  | some (some (some continuation)),
      some (some (some largerContinuation)) =>
      assertTrue (foldResult_variant2 continuation == (some expectedStored, terminal))
        s!"{label}: parent fold lost exact storage or terminal bytes"
      assertTrue (foldResult_variant2 largerContinuation == foldResult_variant2 continuation)
        s!"{label}: larger fuel changed the parent fold"
      assertTrue
        (continuationIdentity continuation expectedStored &&
          continuationIdentity largerContinuation expectedStored)
        s!"{label}: completion changed context, effects, index, or trace"
      assertTrue (largerContinuation.result.outcome == continuation.result.outcome)
        s!"{label}: larger fuel changed the completed outcome"
  | _, _ => throw (IO.userError s!"{label}: parent completion was absent")

def testAddressSelectedHostInputWordBEParent : IO Unit := do
  assertTrue observeCaseWriteObserveProgram_variant2.checkHost
    "the host checker rejected the parent strict input-word consumer"
  assertTrue (presentInput.wordBE? observedOffset == some expectedWord)
    "the complete parent fixture did not decode exactly"
  assertTrue ((incompleteInput.wordBE? observedOffset).isNone)
    "the incomplete parent fixture was padded instead of rejected"

  assertMissingLayers presentInputs_variant presentDoneOutcome 30 "complete window"
  assertMissingLayers incompleteInputs_variant incompleteDoneOutcome 30
    "incomplete window"

  match initialization_variant2.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress with
  | none => throw (IO.userError "the parent storage Account was absent")
  | some context =>
      match context.runCodeWithStorage? presentInputs_variant 23 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (inputWordRequestReady state)
            "fuel 23 did not stop at the second strict input-word request"
          assertTrue (resultContext.readStorage targetSlot == expectedWord)
            "fuel 23 lost the word-derived storage write"
      | _ => throw (IO.userError "fuel 23 crossed its measured boundary")
      match context.runCodeWithStorage? presentInputs_variant 29 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (oneStepBeforeResult_variant4 expectedWord state)
            "fuel 29 did not stop one step before the present pair"
          assertTrue (resultContext.readStorage targetSlot == expectedWord)
            "fuel 29 lost the word-derived storage write"
      | _ => throw (IO.userError "fuel 29 crossed its measured boundary")
      match context.runCodeWithStorage? incompleteInputs_variant 11 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (oneStepBeforeResult_variant4 missingSentinel state)
            "fuel 11 did not stop one step before the absent pair"
          assertTrue (resultContext.readStorage targetSlot == oldValue)
            "the incomplete-window branch changed storage"
      | _ => throw (IO.userError "fuel 11 crossed its measured boundary")

  match initialization_variant2.runCodeWithStorageParentIndexedContinuationContext?
      storageAddress presentInputs_variant 29 presentDoneOutcome with
  | some (some none) => pure ()
  | _ => throw (IO.userError "fuel 29 crossed the present inner Option")

  match initialization_variant2.runCodeWithStorageParentIndexedContinuationContext?
      storageAddress incompleteInputs_variant 11 incompleteDoneOutcome with
  | some (some none) => pure ()
  | _ => throw (IO.userError "fuel 11 crossed the incomplete inner Option")

  assertCompletion presentInputs_variant presentDoneOutcome 30 64 expectedWord
    presentTerminal "complete window"
  assertCompletion incompleteInputs_variant incompleteDoneOutcome 12 64 oldValue
    incompleteTerminal "incomplete window"

end Tests
end

section
-- leanmerge: from Solcore.Test.AddressSelectedHostInputWordBEStorage
/-! End-to-end regression for a strict input-word-derived storage write. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def absentAddress_variant : Address := ⟨0x31, by decide⟩
private def completeInput : HostStorageDriver.InputData := {
  bytes := [0xaa].toByteArray.append (encodeWordBytesBE expectedWord)
  size_lt_wordModulus := by native_decide
}

private def inputsFor_variant5
    (data : HostStorageDriver.InputData) :
    HostStorageDriver.ExecutionInputs := {
  codeAddress := codeAddress
  callValue := Word.zero
  callerAddress := callerAddress
  inputData := data
  currentAddress := codeAddress
}

private def completeInputs := inputsFor_variant5 completeInput
private def incompleteInputs_variant2 := inputsFor_variant5 incompleteInput

/--
Observe one strict optional word. Absence returns the left sentinel. Presence
writes the exact decoded word, observes the same window again, and returns both
observations.
-/
private def observeCaseWriteObserveProgram_variant3 : Program := {
  resultType := .sum .unit (.product .word .word)
  body :=
    .caseE
      (.apply
        (.var HostFunction.inputDataWordBE?.index)
        (.word observedOffset))
      (.inLeft (.product .word .word) .unit)
      (.letE
        (.apply
          (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word targetSlot_variant) (.var 0)))
        (.caseE
          (.apply
            (.var (HostFunction.inputDataWordBE?.index + 2))
            (.word observedOffset))
          (.inLeft (.product .word .word) .unit)
          (.inRight .unit (.pair (.var 2) (.var 0)))))
}

private theorem observeCaseWriteObserveProgram_host_checked_variant3 :
    observeCaseWriteObserveProgram_variant3.checkHost = true := by
  decide

private def observeCaseWriteObserveCode_variant3 : CheckedHostCoreProgram :=
  ⟨observeCaseWriteObserveProgram_variant3,
    observeCaseWriteObserveProgram_host_checked_variant3⟩

private def workingWorld_variant9 : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress
      (Account.empty.withCode observeCaseWriteObserveCode_variant3)
    |>.putAccount storageAddress selectedStorageAccount
    |>.putAccount otherAddress
      (Account.empty.storageWrite otherSlot otherValue)

private def baseContext_variant6 :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨storageAddress,
    ⟨⟨checkpointWorld_variant3, ⟨11, [12, 13]⟩⟩,
      (workingWorld_variant9, ⟨21, [22, 23]⟩)⟩⟩

private def expectedResult_variant (word : Word) : Value :=
  .inRight .unit (.pair (.word word) (.word word))

private def codeProgramIs_variant3 (state : WorldState) : Bool :=
  match state.code? codeAddress with
  | none => false
  | some code => code.program == observeCaseWriteObserveProgram_variant3

private def preservesUnrelated_variant2
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat)) :
    Bool :=
  let values := context.context.values
  context.context.storageAddress == storageAddress &&
    codeProgramIs_variant3 values.working.1 &&
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

private def storesDecodedWord
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat))
    (word : Word) : Bool :=
  let working := context.context.values.working.1
  context.storageAccount.storageValue? targetSlot_variant == some word &&
    storageValueAt? working storageAddress targetSlot_variant == some word

private def retainsOldValue
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat)) :
    Bool :=
  let working := context.context.values.working.1
  context.storageAccount.storageValue? targetSlot_variant == some oldValue_variant &&
    storageValueAt? working storageAddress targetSlot_variant == some oldValue_variant

private def inputDataWordRequestReady (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension =>
      suspension.request == .inputDataWordBE? observedOffset
  | _ => false

private def oneStepBeforeResult_variant5 (word : Word) (state : State) : Bool :=
  match hostAdvance state with
  | .next next => next == State.final (expectedResult_variant word)
  | _ => false

def testAddressSelectedHostInputWordBEStorage : IO Unit := do
  assertTrue observeCaseWriteObserveProgram_variant3.checkHost
    "the host checker rejected input-word/case/write/input-word"
  assertTrue (completeInput.wordBE? observedOffset == some expectedWord)
    "the complete nonzero window did not decode exactly"
  assertTrue ((incompleteInput.wordBE? observedOffset).isNone)
    "the incomplete window was padded instead of rejected"

  match baseContext_variant6.withPresentStorageAccount? with
  | none => throw (IO.userError "the selected storage Account was absent")
  | some context =>
      assertTrue
        (context.runCodeWithStorage?
          { completeInputs with codeAddress := absentAddress_variant } 32).isNone
        "an absent code selector unexpectedly executed"
      assertTrue
        (context.runCodeWithStorage?
          { completeInputs with codeAddress := storageAddress } 32).isNone
        "the storage Account was used as a code fallback"

      match context.runCodeWithStorage? completeInputs 23 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (inputDataWordRequestReady state)
            "fuel 23 did not stop at the second input-word request"
          assertTrue (storesDecodedWord resultContext expectedWord)
            "fuel 23 lost the word-derived write"
          assertTrue (preservesUnrelated_variant2 resultContext)
            "fuel 23 changed unrelated context state"
      | some result =>
          throw (IO.userError
            s!"fuel 23 crossed the second observation: {reprStr result.outcome}")
      | none => throw (IO.userError "fuel 23 lost the selected code")

      match context.runCodeWithStorage? completeInputs 31 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (oneStepBeforeResult_variant5 expectedWord state)
            "fuel 31 did not stop one step before the successful pair"
          assertTrue (storesDecodedWord resultContext expectedWord)
            "fuel 31 lost the word-derived write"
          assertTrue (preservesUnrelated_variant2 resultContext)
            "fuel 31 changed unrelated context state"
      | some result =>
          throw (IO.userError
            s!"fuel 31 crossed the completion boundary: {reprStr result.outcome}")
      | none => throw (IO.userError "fuel 31 lost the selected code")

      match context.runCodeWithStorage? completeInputs 32,
          context.runCodeWithStorage? completeInputs 64 with
      | some result, some largerResult =>
          assertTrue
            (result.outcome == .done (expectedResult_variant expectedWord) [])
            "fuel 32 did not return both exact input-word observations"
          assertTrue (largerResult.outcome == result.outcome)
            "additional fuel changed the exact successful result"
          assertTrue (storesDecodedWord result.context expectedWord)
            "completion did not store the decoded word"
          assertTrue (storesDecodedWord largerResult.context expectedWord)
            "larger-fuel completion lost the decoded word"
          assertTrue
            (preservesUnrelated_variant2 result.context &&
              preservesUnrelated_variant2 largerResult.context)
            "completion changed unrelated storage or frame fields"
      | none, _ => throw (IO.userError "fuel 32 lost the selected code")
      | _, none => throw (IO.userError "additional fuel lost the selected code")

      match context.runCodeWithStorage? incompleteInputs_variant2 32,
          context.runCodeWithStorage? incompleteInputs_variant2 64 with
      | some result, some largerResult =>
          assertTrue (result.outcome == .done expectedAbsence [])
            "an incomplete window did not follow the typed left branch"
          assertTrue (largerResult.outcome == result.outcome)
            "additional fuel changed the incomplete-window result"
          assertTrue (retainsOldValue result.context)
            "the incomplete-window branch performed a storage write"
          assertTrue (retainsOldValue largerResult.context)
            "larger fuel changed the retained target value"
          assertTrue
            (preservesUnrelated_variant2 result.context &&
              preservesUnrelated_variant2 largerResult.context)
            "the incomplete-window branch changed unrelated context state"
      | none, _ => throw (IO.userError "the incomplete-window run lost code")
      | _, none => throw (IO.userError "larger-fuel incomplete run lost code")

end Tests
end

section
-- leanmerge: from Solcore.Test.AddressSelectedHostStorage
/-! End-to-end regressions for address-selected storage read/write execution. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def alternateCallerAddress : Address := ⟨0x45, by decide⟩
private def maximumAddress : Address := ⟨addressModulus - 1, by decide⟩
private def inputsFor_variant6
    (address : Address) : HostStorageDriver.ExecutionInputs := {
  codeAddress := address
  callValue := suppliedCallValue
  callerAddress := callerAddress
  inputData := inputData_variant
  currentAddress := address
}

private def executionInputs_variant3 : HostStorageDriver.ExecutionInputs :=
  inputsFor_variant6 codeAddress

private def alternateCallerInputs : HostStorageDriver.ExecutionInputs :=
  { executionInputs_variant3 with callerAddress := alternateCallerAddress }

private def expectedStorageAddressWord : Word := ⟨0x20, by decide⟩
private def expectedCodeAddressWord : Word := ⟨0x10, by decide⟩
private def expectedCallerAddressWord : Word := ⟨0x40, by decide⟩
private def expectedAlternateCallerAddressWord : Word := ⟨0x45, by decide⟩
private def expectedMaximumAddressWord : Word :=
  ⟨addressModulus - 1, by decide⟩

private def selectorSlot : Word := ⟨0x41, by decide⟩
private def retainedSlot_variant : Word := ⟨0x43, by decide⟩
private def intermediateValue : Word := ⟨0x54, by decide⟩
private def newValue : Word := ⟨0x52, by decide⟩
private def codeSlot : Word := ⟨0x61, by decide⟩
private def codeValue : Word := ⟨0x62, by decide⟩
private def otherSlot_variant : Word := ⟨0x71, by decide⟩
private def otherValue_variant : Word := ⟨0x72, by decide⟩

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
private def observeWriteObserveProgram_variant : Program := {
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

private theorem observeWriteObserveProgram_host_checked_variant :
    observeWriteObserveProgram_variant.checkHost = true := by
  decide

private def observeWriteObserveCode_variant : CheckedHostCoreProgram :=
  ⟨observeWriteObserveProgram_variant, observeWriteObserveProgram_host_checked_variant⟩

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

private def selectedStorageAccount_variant : Account :=
  Account.empty
    |>.storageWrite selectorSlot targetSlot
    |>.storageWrite targetSlot oldValue
    |>.storageWrite retainedSlot_variant retainedValue

private def otherWorkingAccount : Account :=
  Account.empty.storageWrite otherSlot_variant otherValue_variant

private def workingWorldFor (code : CheckedHostCoreProgram) : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress (codeAccountFor code)
    |>.putAccount storageAddress selectedStorageAccount_variant
    |>.putAccount otherAddress otherWorkingAccount

private def checkpointWorld_variant4 : WorldState :=
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
    ⟨⟨checkpointWorld_variant4, checkpointEffects⟩,
      (workingWorldFor code, workingEffects)⟩⟩

private def callValueParentWorking :
    WorldState × FrameEffectJournal Nat (FrameTrace Nat) :=
  (checkpointWorld_variant4, ⟨101, FrameTrace.empty⟩)

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
  (checkpointWorld_variant4, ⟨101, FrameTrace.empty⟩)

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

private def codeProgramIs_variant4
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
    codeProgramIs_variant4 values.working.1 codeAddress program &&
    storageValueAt? values.working.1 codeAddress codeSlot == some codeValue &&
    storageValueAt? values.working.1 otherAddress otherSlot_variant ==
      some otherValue_variant &&
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
    context.storageAccount.storageRead retainedSlot_variant == retainedValue &&
    storageValueAt? working storageAddress retainedSlot_variant == some retainedValue

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
    context.storageAccount.storageRead retainedSlot_variant == retainedValue

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
  match context.runCodeWithStorage? executionInputs_variant3 fuel with
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
      (inputsFor_variant6 maximumAddress) completionFuel returnedDoneOutcome with
  | none => pure ()
  | some _ =>
      throw (IO.userError
        "missing code did not remain an outer continuation failure")

  match context.runCodeWithStorageContinuationContext?
      executionInputs_variant3 22 returnedDoneOutcome with
  | some none => pure ()
  | none =>
      throw (IO.userError
        "fuel 22 confused selected exhaustion with missing code")
  | some (some _) =>
      throw (IO.userError
        "fuel 22 constructed a continuation before completion")

  match context.runCodeWithStorageContinuationContext?
        executionInputs_variant3 completionFuel returnedDoneOutcome,
      context.runCodeWithStorageContinuationContext?
        executionInputs_variant3 completionFuel revertedDoneOutcome,
      context.runCodeWithStorageContinuationContext?
        executionInputs_variant3 completionFuel trappedDoneOutcome,
      context.runCodeWithStorageContinuationContext?
        executionInputs_variant3 64 returnedDoneOutcome with
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
      context.runCodeWithStorage? executionInputs_variant3 completionFuel =
        some ⟨finalContext,
          .done (.word newValue) [.bool true]⟩)
    (written : finalContext.storageAccount.storageRead targetSlot = newValue) :
    (baseContextFor updateCode).withPresentStorageAccount? = some context ∧
      context.runCodeWithStorage? executionInputs_variant3 64 =
        some ⟨finalContext,
          .done (.word newValue) [.bool true]⟩ ∧
      finalContext.storageAccount.storageRead targetSlot = newValue := by
  exact ⟨selected,
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
      context executionInputs_variant3 execution (by decide),
    written⟩

/-- The exact nested continuation produced at fuel 28 survives fuel 64. -/
private theorem updateProgram_frameContinuation_done_stable
    {context : HostStorageDriver.Context Nat (List Nat)}
    {continuation :
      FrameContinuationContext Nat (List Nat) FrameAdapterTrapReason}
    (completed :
      context.runCodeWithStorageContinuationContext?
        executionInputs_variant3 completionFuel returnedDoneOutcome =
          some (some continuation)) :
    context.runCodeWithStorageContinuationContext?
      executionInputs_variant3 64 returnedDoneOutcome = some (some continuation) := by
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_some_some_stable
      context executionInputs_variant3 returnedDoneOutcome completed (by decide)

/-- The selected public stability theorem applies to the mixed fixture. -/
private theorem observeWriteObserveProgram_done_stable
    {context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat)}
    (selected :
      (baseContextFor observeWriteObserveCode_variant).withPresentStorageAccount? =
        some context)
    {finalContext :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat)}
    (execution :
      context.runCodeWithStorage? executionInputs_variant3
          observeWriteObserveCompletionFuel =
        some ⟨finalContext, .done expectedStorageAddressPair []⟩) :
    (baseContextFor observeWriteObserveCode_variant).withPresentStorageAccount? =
        some context ∧
      context.runCodeWithStorage? executionInputs_variant3 64 =
        some ⟨finalContext, .done expectedStorageAddressPair []⟩ := by
  exact ⟨selected,
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
      context executionInputs_variant3 execution (by decide)⟩

/-- The selected code observation retains its exact result with more fuel. -/
private theorem codeAddressProgram_done_stable
    {context : HostStorageDriver.Context Nat (List Nat)}
    (selected :
      (baseContextFor codeAddressCode).withPresentStorageAccount? =
        some context)
    {finalContext : HostStorageDriver.Context Nat (List Nat)}
    (execution :
      context.runCodeWithStorage? executionInputs_variant3
          codeAddressCompletionFuel =
        some ⟨finalContext, .done (.word expectedCodeAddressWord) []⟩) :
    (baseContextFor codeAddressCode).withPresentStorageAccount? =
        some context ∧
      context.runCodeWithStorage? executionInputs_variant3 32 =
        some ⟨finalContext, .done (.word expectedCodeAddressWord) []⟩ := by
  exact ⟨selected,
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
      context executionInputs_variant3 execution (by decide)⟩

/-- The supplied call value and exact terminal context survive larger fuel. -/
private theorem callValueProgram_done_stable
    {context : HostStorageDriver.Context Nat (List Nat)}
    (selected :
      (baseContextFor callValueCode).withPresentStorageAccount? =
        some context)
    {finalContext : HostStorageDriver.Context Nat (List Nat)}
    (execution :
      context.runCodeWithStorage? executionInputs_variant3 callValueCompletionFuel =
        some ⟨finalContext, .done (.word suppliedCallValue) []⟩) :
    (baseContextFor callValueCode).withPresentStorageAccount? =
        some context ∧
      context.runCodeWithStorage? executionInputs_variant3 32 =
        some ⟨finalContext, .done (.word suppliedCallValue) []⟩ := by
  exact ⟨selected,
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
      context executionInputs_variant3 execution (by decide)⟩

/-- The widened caller and terminal context survive larger fuel. -/
private theorem callerAddressProgram_done_stable
    {context : HostStorageDriver.Context Nat (List Nat)}
    (selected :
      (baseContextFor callerAddressCode).withPresentStorageAccount? =
        some context)
    {finalContext : HostStorageDriver.Context Nat (List Nat)}
    (execution :
      context.runCodeWithStorage? executionInputs_variant3 5 =
        some ⟨finalContext, .done (.word expectedCallerAddressWord) []⟩) :
    (baseContextFor callerAddressCode).withPresentStorageAccount? =
        some context ∧
      context.runCodeWithStorage? executionInputs_variant3 32 =
        some ⟨finalContext, .done (.word expectedCallerAddressWord) []⟩ := by
  exact ⟨selected,
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
      context executionInputs_variant3 execution (by decide)⟩

/-- Caller variation changes the response but preserves the exact host context. -/
private theorem callerAddress_handling_context_independent
    (context : HostStorageDriver.Context Nat (List Nat))
    (continuation : List Frame) (store : Store) :
    (HostStorageDriver.handleSuspension executionInputs_variant3 context
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
    (callerAddressCode.runWithStorage context executionInputs_variant3 5).context =
      (callerAddressCode.runWithStorage context alternateCallerInputs 5).context :=
  (callerAddress_runWithStorage_preserves_context context executionInputs_variant3).trans
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
      context.runCodeWithStorage? executionInputs_variant3
          observeWriteObserveCompletionFuel =
        some ⟨finalContext, .done expectedCallValuePair []⟩) :
    (baseContextFor observeCallValueWriteObserveCode).withPresentStorageAccount? =
        some context ∧
      context.runCodeWithStorage? executionInputs_variant3 32 =
        some ⟨finalContext, .done expectedCallValuePair []⟩ := by
  exact ⟨selected,
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
      context executionInputs_variant3 execution (by decide)⟩

/-- The caller-derived write and both observations survive larger fuel. -/
private theorem observeCallerWriteObserveProgram_done_stable
    {context : HostStorageDriver.Context Nat (List Nat)}
    (selected :
      (baseContextFor observeCallerWriteObserveCode).withPresentStorageAccount? =
        some context)
    {finalContext : HostStorageDriver.Context Nat (List Nat)}
    (execution :
      context.runCodeWithStorage? executionInputs_variant3 30 =
        some ⟨finalContext, .done expectedCallerAddressPair []⟩) :
    (baseContextFor observeCallerWriteObserveCode).withPresentStorageAccount? =
        some context ∧
      context.runCodeWithStorage? executionInputs_variant3 32 =
        some ⟨finalContext, .done expectedCallerAddressPair []⟩ := by
  exact ⟨selected,
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
      context executionInputs_variant3 execution (by decide)⟩

/-- Parent-indexed completion retains the exact context at fuel 32. -/
private theorem callValueParentCompletion_done_stable
    {continuation :
      ParentIndexedFrameContinuationContext
        Nat Nat FrameAdapterTrapReason callValueParentWorking}
    (completed :
      callValueInitialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress executionInputs_variant3 observeWriteObserveCompletionFuel
          callValueDoneOutcome =
        some (some (some continuation))) :
    callValueInitialization.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress executionInputs_variant3 32 callValueDoneOutcome =
      some (some (some continuation)) :=
  callValueInitialization.runCodeWithStorageParentIndexedContinuationContext?_some_some_some_stable
    storageAddress executionInputs_variant3 callValueDoneOutcome completed (by decide)

/-- Caller-derived parent completion retains its exact context at fuel 32. -/
private theorem callerParentCompletion_done_stable
    {continuation :
      ParentIndexedFrameContinuationContext
        Nat Nat FrameAdapterTrapReason callerParentWorking}
    (completed :
      callerInitialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress executionInputs_variant3 30 callerDoneOutcome =
        some (some (some continuation))) :
    callerInitialization.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress executionInputs_variant3 32 callerDoneOutcome =
      some (some (some continuation)) :=
  callerInitialization.runCodeWithStorageParentIndexedContinuationContext?_some_some_some_stable
    storageAddress executionInputs_variant3 callerDoneOutcome completed (by decide)

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
  assertTrue observeWriteObserveProgram_variant.checkHost
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
      match context.runCodeWithStorage? executionInputs_variant3 4 with
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
          executionInputs_variant3 storageAddressCompletionFuel,
          context.runCodeWithStorage? executionInputs_variant3 32 with
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
      match context.runCodeWithStorage? executionInputs_variant3 4 with
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
          executionInputs_variant3 codeAddressCompletionFuel,
          context.runCodeWithStorage? executionInputs_variant3 32 with
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
      match context.runCodeWithStorage? executionInputs_variant3 4 with
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
          executionInputs_variant3 callValueCompletionFuel,
          context.runCodeWithStorage? executionInputs_variant3 32 with
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
      match context.runCodeWithStorage? executionInputs_variant3 4 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (callerAddressRequestReady state)
            "fuel 4 did not stop at the caller-address request"
          assertFixtureContext resultContext callerAddressProgram oldValue
            "fuel 4 caller-address observation"
      | some result =>
          throw (IO.userError
            s!"fuel 4 crossed the caller boundary: {reprStr result.outcome}")
      | none => throw (IO.userError "fuel 4 lost the caller-address code")

      match context.runCodeWithStorage? executionInputs_variant3 5,
          context.runCodeWithStorage? executionInputs_variant3 32,
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
      match context.runCodeWithStorage? executionInputs_variant3
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

      match context.runCodeWithStorage? executionInputs_variant3 29 with
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

      match context.runCodeWithStorage? executionInputs_variant3
          observeWriteObserveCompletionFuel,
          context.runCodeWithStorage? executionInputs_variant3 64 with
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
      match context.runCodeWithStorage? executionInputs_variant3
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

      match context.runCodeWithStorage? executionInputs_variant3 29 with
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

      match context.runCodeWithStorage? executionInputs_variant3
          observeWriteObserveCompletionFuel,
          context.runCodeWithStorage? executionInputs_variant3 32 with
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
      match context.runCodeWithStorage? executionInputs_variant3 23 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (callerAddressRequestReady state)
            "fuel 23 did not stop at the second caller request"
          assertFixtureContext resultContext observeCallerWriteObserveProgram
            expectedCallerAddressWord "fuel 23 caller/write/caller"
      | some result =>
          throw (IO.userError
            s!"fuel 23 crossed the second caller request: {reprStr result.outcome}")
      | none => throw (IO.userError "fuel 23 lost caller/write/caller code")

      match context.runCodeWithStorage? executionInputs_variant3 29 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (oneStepBeforeCallerAddressPair state)
            "fuel 29 did not stop before the caller pair"
          assertFixtureContext resultContext observeCallerWriteObserveProgram
            expectedCallerAddressWord "fuel 29 caller/write/caller"
      | some result =>
          throw (IO.userError
            s!"fuel 29 crossed caller completion: {reprStr result.outcome}")
      | none => throw (IO.userError "fuel 29 lost caller/write/caller code")

      match context.runCodeWithStorage? executionInputs_variant3 30,
          context.runCodeWithStorage? executionInputs_variant3 32 with
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
          storageAddress executionInputs_variant3 observeWriteObserveCompletionFuel
          callValueDoneOutcome,
      callValueInitialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress executionInputs_variant3 32 callValueDoneOutcome with
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
          storageAddress executionInputs_variant3 30 callerDoneOutcome,
      callerInitialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress executionInputs_variant3 32 callerDoneOutcome with
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

  match (baseContextFor observeWriteObserveCode_variant).withPresentStorageAccount? with
  | none =>
      throw (IO.userError "the observe/write/observe storage Account was absent")
  | some context =>
      match context.runCodeWithStorage? executionInputs_variant3
          observeWriteObserveSecondRequestFuel with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (storageAddressRequestReady state)
            "fuel 23 did not stop at the second address request"
          assertFixtureContext resultContext observeWriteObserveProgram_variant newValue
            "fuel 23 observe/write/observe"
      | some result =>
          throw (IO.userError
            s!"fuel 23 crossed the second request: {reprStr result.outcome}")
      | none =>
          throw (IO.userError "fuel 23 lost observe/write/observe code")

      match context.runCodeWithStorage? executionInputs_variant3 29 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (oneStepBeforeStorageAddressPair state)
            "fuel 29 did not stop one step before the result pair"
          assertFixtureContext resultContext observeWriteObserveProgram_variant newValue
            "fuel 29 observe/write/observe"
      | some result =>
          throw (IO.userError
            s!"fuel 29 crossed completion: {reprStr result.outcome}")
      | none =>
          throw (IO.userError "fuel 29 lost observe/write/observe code")

      match context.runCodeWithStorage? executionInputs_variant3
          observeWriteObserveCompletionFuel,
          context.runCodeWithStorage? executionInputs_variant3 64 with
      | some result, some largerResult =>
          assertTrue (result.outcome == .done expectedStorageAddressPair [])
            "fuel 30 returned unequal storage selectors"
          assertTrue (largerResult.outcome == result.outcome)
            "additional fuel changed observe/write/observe"
          assertFixtureContext result.context observeWriteObserveProgram_variant newValue
            "fuel 30 observe/write/observe"
          assertFixtureContext largerResult.context
            observeWriteObserveProgram_variant newValue
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

      match context.runCodeWithStorage? executionInputs_variant3 completionFuel,
          context.runCodeWithStorage? executionInputs_variant3 64 with
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
      match context.runCodeWithStorage? executionInputs_variant3 64,
          context.runCodeWithStorage? executionInputs_variant3 96 with
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
      match context.runCodeWithStorage? executionInputs_variant3 15 with
      | some { context := resultContext, outcome := .outOfFuel _ } =>
          assertTrue (selectedTargetMissing resultContext)
            "fuel 15 lost the handled sparse-zero update"
      | some result =>
          throw (IO.userError
            s!"fuel 15 crossed the zero boundary: {reprStr result.outcome}")
      | none =>
          throw (IO.userError "the zero boundary lost the selected code")

      match context.runCodeWithStorage?
          executionInputs_variant3 zeroCompletionFuel with
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
end

section
-- leanmerge: from Solcore.Test.AddressSelectedHostStorageProperties
/-! Compile-time use of the public storage-driver proof interface. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

universe u v w x

private def frameContinuationData : Bytes := [0xa1, 0xb2].toByteArray

private def returnedFrameOutcome
    {Context : Type x}
    (_ : Context) (_ : Value) (_ : Store) : FrameOutcome Unit :=
  .returned frameContinuationData

private def revertedFrameOutcome
    {Context : Type x}
    (_ : Context) (_ : Value) (_ : Store) : FrameOutcome Unit :=
  .reverted frameContinuationData

private def trappedFrameOutcome
    {Context : Type x}
    (_ : Context) (_ : Value) (_ : Store) : FrameOutcome Unit :=
  .trapped ()

/-- The public handler API exposes the exact write update and resumed Core state. -/
private theorem compileTimeWriteResumeRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (slot value : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostStorageDriver.handleSuspension inputs context
        ⟨.storageWrite slot value, continuation, store⟩).1 =
          context.writeStorage slot value ∧
      (HostStorageDriver.handleSuspension inputs context
          ⟨.storageWrite slot value, continuation, store⟩).2.control =
        .ret .unit ∧
      (HostStorageDriver.handleSuspension inputs context
          ⟨.storageWrite slot value, continuation, store⟩).2.continuation =
        continuation ∧
      (HostStorageDriver.handleSuspension inputs context
          ⟨.storageWrite slot value, continuation, store⟩).2.store = store := by
  exact
    ⟨HostStorageDriver.handleSuspension_storageWrite_context
        inputs context slot value continuation store,
      HostStorageDriver.handleSuspension_storageWrite_control
        inputs context slot value continuation store,
      HostStorageDriver.handleSuspension_storageWrite_continuation
        inputs context slot value continuation store,
      HostStorageDriver.handleSuspension_storageWrite_store
        inputs context slot value continuation store⟩

/-- The selector handler exposes its exact lossless, context-preserving response. -/
private theorem compileTimeStorageAddressResumeRegression
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (continuation : List Frame) (store : Store) :
    (HostStorageDriver.handleSuspension inputs context
        ⟨.storageAddress, continuation, store⟩).1 = context ∧
      (HostStorageDriver.handleSuspension inputs context
        ⟨.storageAddress, continuation, store⟩).2.control =
          .ret (.word (addressToWord context.context.storageAddress)) ∧
      (HostStorageDriver.handleSuspension inputs context
        ⟨.storageAddress, continuation, store⟩).2.continuation = continuation ∧
      (HostStorageDriver.handleSuspension inputs context
        ⟨.storageAddress, continuation, store⟩).2.store = store ∧
      wordToAddress?
          ((HostStorageDriver.handler inputs).handle
            context .storageAddress).2 =
        some context.context.storageAddress := by
  exact
    ⟨HostStorageDriver.handleSuspension_storageAddress_context
        inputs context continuation store,
      HostStorageDriver.handleSuspension_storageAddress_control
        inputs context continuation store,
      HostStorageDriver.handleSuspension_storageAddress_continuation
        inputs context continuation store,
      HostStorageDriver.handleSuspension_storageAddress_store
        inputs context continuation store,
      HostStorageDriver.wordToAddress?_handler_storageAddress
        inputs context⟩

/-- The public selector rule reuses Core's exact remaining fuel. -/
private theorem compileTimeStorageAddressRemainingFuelRegression
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel remainingFuel : Nat) (state : State)
    (continuation : List Frame) (store : Store)
    (execution :
      hostRun fuel state =
        .suspended ⟨.storageAddress, continuation, store⟩ remainingFuel) :
    HostStorageDriver.run context inputs fuel state =
      HostStorageDriver.run context inputs remainingFuel
        ⟨.ret (.word (addressToWord context.context.storageAddress)),
          continuation, store⟩ :=
  HostStorageDriver.run_of_suspended_storageAddress
    context inputs fuel remainingFuel state continuation store execution

/-- The code-selector handler exposes its exact lossless response and state. -/
private theorem compileTimeCodeAddressResumeRegression
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (continuation : List Frame) (store : Store) :
    (HostStorageDriver.handleSuspension inputs context
        ⟨.codeAddress, continuation, store⟩).1 = context ∧
      (HostStorageDriver.handleSuspension inputs context
        ⟨.codeAddress, continuation, store⟩).2.control =
          .ret (.word (addressToWord inputs.codeAddress)) ∧
      (HostStorageDriver.handleSuspension inputs context
        ⟨.codeAddress, continuation, store⟩).2.continuation = continuation ∧
      (HostStorageDriver.handleSuspension inputs context
        ⟨.codeAddress, continuation, store⟩).2.store = store ∧
      wordToAddress?
          ((HostStorageDriver.handler inputs).handle
            context .codeAddress).2 = some inputs.codeAddress := by
  exact
    ⟨HostStorageDriver.handleSuspension_codeAddress_context
        inputs context continuation store,
      HostStorageDriver.handleSuspension_codeAddress_control
        inputs context continuation store,
      HostStorageDriver.handleSuspension_codeAddress_continuation
        inputs context continuation store,
      HostStorageDriver.handleSuspension_codeAddress_store
        inputs context continuation store,
      HostStorageDriver.wordToAddress?_handler_codeAddress
        inputs context⟩

/-- The public code-selector rule reuses Core's exact remaining fuel. -/
private theorem compileTimeCodeAddressRemainingFuelRegression
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel remainingFuel : Nat) (state : State)
    (continuation : List Frame) (store : Store)
    (execution :
      hostRun fuel state =
        .suspended ⟨.codeAddress, continuation, store⟩ remainingFuel) :
    HostStorageDriver.run context inputs fuel state =
      HostStorageDriver.run context inputs remainingFuel
        ⟨.ret (.word (addressToWord inputs.codeAddress)), continuation, store⟩ :=
  HostStorageDriver.run_of_suspended_codeAddress
    context inputs fuel remainingFuel state continuation store execution

/-- Public handler observations fix read-after-write and sparse zero deletion. -/
private theorem compileTimeWriteObservationRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (slot value : Word) :
    (((HostStorageDriver.handler inputs).handle context
      (.storageWrite slot value)).1).readStorage slot = value ∧
      (((HostStorageDriver.handler inputs).handle context
        (.storageWrite slot Word.zero)).1).storageAccount.storageValue?
          slot = none := by
  exact
    ⟨HostStorageDriver.handler_storageWrite_readStorage_same
        inputs context slot value,
      HostStorageDriver.handler_storageWrite_zero_storageValue?
        inputs context slot⟩

/-- A successful selected run exposes both typing and exact fuel evidence. -/
private theorem compileTimeSelectedEvidenceRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? inputs fuel = some result) :
    (∃ code,
      context.context.values.working.1.code? inputs.codeAddress = some code ∧
        result.outcome.HasType
          code.program.resultType code.program.dataDefinitions) ∧
    (∃ code,
      context.context.values.working.1.code? inputs.codeAddress = some code ∧
        HostStorageDriver.FuelSound result inputs fuel context
          (State.initial code.program.body hostEnvironment)) := by
  exact
    ⟨FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_hasType
        context inputs fuel result executed,
      FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_fuelSound
        context inputs fuel result executed⟩

/-- The public selected entry point exposes its complete successful specification. -/
private theorem compileTimeSelectedCompletenessRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState)) :
    context.runCodeWithStorage? inputs fuel = some result ↔
      ∃ code,
        context.context.values.working.1.code? inputs.codeAddress = some code ∧
          HostStorageDriver.FuelSound result inputs fuel context
            (State.initial code.program.body hostEnvironment) :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_eq_some_iff_fuelSound
    context inputs fuel result

/-- The forward iff direction recovers the selected code and exact fuel evidence. -/
private theorem compileTimeSelectedCompletenessForwardRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? inputs fuel = some result) :
    ∃ code,
      context.context.values.working.1.code? inputs.codeAddress = some code ∧
        HostStorageDriver.FuelSound result inputs fuel context
          (State.initial code.program.body hostEnvironment) :=
  (compileTimeSelectedCompletenessRegression
    context inputs fuel result).mp executed

/-- Selected-code fuel evidence replays to the exact optional execution result. -/
private theorem compileTimeSelectedCompletenessReplayRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (code : CheckedHostCoreProgram)
    (selected :
      context.context.values.working.1.code? inputs.codeAddress = some code)
    (sound :
      HostStorageDriver.FuelSound result inputs fuel context
        (State.initial code.program.body hostEnvironment)) :
    context.runCodeWithStorage? inputs fuel = some result :=
  (compileTimeSelectedCompletenessRegression
    context inputs fuel result).mpr ⟨code, selected, sound⟩

/-- Optional failure is exactly failure of the existing code lookup. -/
private theorem compileTimeSelectedNoneCompletenessRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    context.runCodeWithStorage? inputs fuel = none ↔
      context.context.values.working.1.code? inputs.codeAddress = none :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_eq_none_iff
    context inputs fuel

/-- A selected exhausted run remains an attempted execution, never `none`. -/
private theorem compileTimeSelectedOutOfFuelIsSomeRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (code : CheckedHostCoreProgram)
    (selected :
      context.context.values.working.1.code? inputs.codeAddress = some code)
    (finalContext : HostStorageDriver.Context RollbackState TraceState)
    (state : State)
    (exhausted :
      code.runWithStorage context inputs fuel =
        ⟨finalContext, .outOfFuel state⟩) :
    context.runCodeWithStorage? inputs fuel =
      some ⟨finalContext, .outOfFuel state⟩ := by
  unfold FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?
  rw [selected]
  simp only [Option.map_some]
  exact congrArg some exhausted

/-- A selected checked run cannot expose the raw driver fault branch. -/
private theorem compileTimeSelectedNoFaultRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (resultContext :
      HostStorageDriver.Context RollbackState TraceState)
    (error : MachineFault)
    (faultState : State) :
    context.runCodeWithStorage? inputs fuel ≠
      some ⟨resultContext, .fault error faultState⟩ :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_ne_some_fault
    context inputs fuel resultContext error faultState

/-- Public selected-run laws retain every frame projection outside storage. -/
private theorem compileTimeSelectedInvariantRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (executed :
      context.runCodeWithStorage? inputs fuel = some result)
    (otherAddress : Address)
    (different : otherAddress ≠ context.context.storageAddress) :
    result.context.context.storageAddress = context.context.storageAddress ∧
      result.context.context.values.checkpoint =
        context.context.values.checkpoint ∧
      result.context.context.values.working.2 =
        context.context.values.working.2 ∧
      result.context.context.values.working.1.account? otherAddress =
        context.context.values.working.1.account? otherAddress ∧
      result.context.context.values.working.1.code? inputs.codeAddress =
        context.context.values.working.1.code? inputs.codeAddress := by
  exact
    ⟨FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_storageAddress
        context inputs fuel result executed,
      FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_checkpoint
        context inputs fuel result executed,
      FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_workingEffects
        context inputs fuel result executed,
      FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_workingAccount?_of_ne_storageAddress
        context inputs fuel result executed otherAddress different,
      FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_workingCode?
        context inputs fuel result executed inputs.codeAddress⟩

/-- The specialized driver exposes the generic executable/specification iff. -/
private theorem compileTimeStorageDriverCompletenessRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : State)
    (result :
      HostDriverResult
        (HostStorageDriver.Context RollbackState TraceState)) :
    HostStorageDriver.run context inputs fuel state = result ↔
      HostStorageDriver.FuelSound result inputs fuel context state :=
  HostStorageDriver.run_eq_iff_fuelSound
    context inputs fuel state result

/-- Combined storage done stability retains the exact full driver result. -/
private theorem compileTimeStorageDriverDoneStabilityRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel largerFuel : Nat}
    (state : State)
    {finalContext :
      HostStorageDriver.Context RollbackState TraceState}
    {value : Value}
    {store : Store}
    (execution :
      HostStorageDriver.run context inputs fuel state =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    HostStorageDriver.run context inputs largerFuel state =
      ⟨finalContext, .done value store⟩ :=
  HostStorageDriver.run_done_stable
    context inputs state execution more

/-- Checked execution exposes the same exact executable/specification iff. -/
private theorem compileTimeCheckedCompletenessRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result :
      HostDriverResult
        (HostStorageDriver.Context RollbackState TraceState)) :
    code.runWithStorage context inputs fuel = result ↔
      HostStorageDriver.FuelSound result inputs fuel context
        (State.initial code.program.body hostEnvironment) :=
  CheckedHostCoreProgram.runWithStorage_eq_iff_fuelSound
    code context inputs fuel result

/-- Checked done stability retains the exact full driver result. -/
private theorem compileTimeCheckedDoneStabilityRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel largerFuel : Nat}
    {finalContext :
      HostStorageDriver.Context RollbackState TraceState}
    {value : Value}
    {store : Store}
    (execution :
      code.runWithStorage context inputs fuel =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    code.runWithStorage context inputs largerFuel =
      ⟨finalContext, .done value store⟩ :=
  CheckedHostCoreProgram.runWithStorage_done_stable
    code context inputs execution more

/-- Address-selected done stability retains the exact optional full result. -/
private theorem compileTimeSelectedDoneStabilityRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel largerFuel : Nat}
    {finalContext :
      HostStorageDriver.Context RollbackState TraceState}
    {value : Value}
    {store : Store}
    (execution :
      context.runCodeWithStorage? inputs fuel =
        some ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    context.runCodeWithStorage? inputs largerFuel =
      some ⟨finalContext, .done value store⟩ :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_done_stable
    context inputs execution more

/-- The generic adapter distinguishes completion from exhaustion and raw faults. -/
private theorem compileTimeFrameContinuationBranchRegression
    {Context : Type x}
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context)
    (value : Value)
    (store : Store)
    (state : State)
    (error : MachineFault)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState) :
    (HostDriverResult.mk context (.done value store)).toFrameContinuationContext?
          values returnedFrameOutcome =
        some (FrameContinuationContext.fromCheckpointedWorkingPair
          (values context) (returnedFrameOutcome context value store)) ∧
      (HostDriverResult.mk context (.outOfFuel state)).toFrameContinuationContext?
          values returnedFrameOutcome = none ∧
      (HostDriverResult.mk context (.fault error state)).toFrameContinuationContext?
          values returnedFrameOutcome = none := by
  exact
    ⟨HostDriverResult.toFrameContinuationContext?_done
        context value store values returnedFrameOutcome,
      HostDriverResult.toFrameContinuationContext?_outOfFuel
        context state values returnedFrameOutcome,
      HostDriverResult.toFrameContinuationContext?_fault
        context error state values returnedFrameOutcome⟩

/-- Completion retains every terminal checkpoint, working, and outcome input. -/
private theorem compileTimeFrameContinuationProjectionRegression
    {Context : Type x}
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context)
    (value : Value)
    (store : Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState) :
    Option.map FrameContinuationContext.stateCheckpoint
        ((HostDriverResult.mk context (.done value store)).toFrameContinuationContext?
          values returnedFrameOutcome) =
        some (values context).checkpoint.state ∧
      Option.map FrameContinuationContext.effectCheckpoint
        ((HostDriverResult.mk context (.done value store)).toFrameContinuationContext?
          values returnedFrameOutcome) =
        some (values context).checkpoint.effects ∧
      Option.map FrameContinuationContext.effectWorking
        ((HostDriverResult.mk context (.done value store)).toFrameContinuationContext?
          values returnedFrameOutcome) =
        some (values context).working.2 ∧
      Option.map FrameContinuationContext.result
        ((HostDriverResult.mk context (.done value store)).toFrameContinuationContext?
          values returnedFrameOutcome) =
        some ⟨(values context).working.1,
          returnedFrameOutcome context value store⟩ := by
  exact
    ⟨HostDriverResult.stateCheckpoint_toFrameContinuationContext?_done
        context value store values returnedFrameOutcome,
      HostDriverResult.effectCheckpoint_toFrameContinuationContext?_done
        context value store values returnedFrameOutcome,
      HostDriverResult.effectWorking_toFrameContinuationContext?_done
        context value store values returnedFrameOutcome,
      HostDriverResult.result_toFrameContinuationContext?_done
        context value store values returnedFrameOutcome⟩

/-- Return, revert, and policy-selected trap resolution remain branch exact. -/
private theorem compileTimeFrameContinuationResolutionRegression
    {Context : Type x}
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context)
    (value : Value)
    (store : Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState) :
    Option.map FrameContinuationContext.resolve
        ((HostDriverResult.mk context (.done value store)).toFrameContinuationContext?
          values returnedFrameOutcome) =
        some (FrameResolutionResult.returned
          (values context).working.1 (values context).working.2
          frameContinuationData) ∧
      Option.map FrameContinuationContext.resolve
        ((HostDriverResult.mk context (.done value store)).toFrameContinuationContext?
          values revertedFrameOutcome) =
        some (FrameResolutionResult.reverted
          (values context).checkpoint.state
          ⟨(values context).checkpoint.effects.rollback,
            (values context).working.2.trace⟩
          frameContinuationData) ∧
      Option.map FrameContinuationContext.resolve
        ((HostDriverResult.mk context (.done value store)).toFrameContinuationContext?
          values trappedFrameOutcome) =
        some (FrameResolutionResult.trapped ()) := by
  exact
    ⟨HostDriverResult.resolve_toFrameContinuationContext?_done_returned
        context value store values returnedFrameOutcome
        frameContinuationData rfl,
      HostDriverResult.resolve_toFrameContinuationContext?_done_reverted
        context value store values revertedFrameOutcome
        frameContinuationData rfl,
      HostDriverResult.resolve_toFrameContinuationContext?_done_trapped
        context value store values trappedFrameOutcome () rfl⟩

/-- Checked adaptation exposes exhaustion exactly and preserves completed output. -/
private theorem compileTimeCheckedFrameContinuationRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    {TrapReason : Type w}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Value → Store → FrameOutcome TrapReason) :
    (code.runWithStorage context inputs fuel).toFrameContinuationContext?
          (fun current => current.context.values) doneOutcome = none ↔
      (∃ finalContext exhausted,
        code.runWithStorage context inputs fuel =
          ⟨finalContext, .outOfFuel exhausted⟩) ∨
      ∃ finalContext suspension remainingFuel,
        code.runWithStorage context inputs fuel =
          ⟨finalContext, .unsupported suspension remainingFuel⟩ :=
  code.runWithStorage_toFrameContinuationContext?_eq_none_iff
    context inputs fuel doneOutcome

private theorem compileTimeCheckedFrameContinuationStabilityRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    {TrapReason : Type w}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Value → Store → FrameOutcome TrapReason)
    {fuel largerFuel : Nat}
    {continuation :
      FrameContinuationContext RollbackState TraceState TrapReason}
    (completed :
      (code.runWithStorage context inputs fuel).toFrameContinuationContext?
          (fun current => current.context.values) doneOutcome =
        some continuation)
    (more : fuel ≤ largerFuel) :
    (code.runWithStorage context inputs largerFuel).toFrameContinuationContext?
        (fun current => current.context.values) doneOutcome =
      some continuation :=
  code.runWithStorage_toFrameContinuationContext?_some_stable
    context inputs doneOutcome completed more

/-- Selected adaptation keeps code absence distinct from selected exhaustion. -/
private theorem compileTimeSelectedFrameContinuationBoundaryRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    {TrapReason : Type w}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Value → Store → FrameOutcome TrapReason) :
    (context.runCodeWithStorageContinuationContext?
          inputs fuel doneOutcome = none ↔
        context.context.values.working.1.code? inputs.codeAddress = none) ∧
      (context.runCodeWithStorageContinuationContext?
          inputs fuel doneOutcome = some none ↔
        (∃ resultContext exhausted,
          context.runCodeWithStorage? inputs fuel =
            some ⟨resultContext, .outOfFuel exhausted⟩) ∨
        ∃ resultContext suspension remainingFuel,
          context.runCodeWithStorage? inputs fuel =
            some ⟨resultContext,
              .unsupported suspension remainingFuel⟩) := by
  exact
    ⟨FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_eq_none_iff
        context inputs fuel doneOutcome,
      FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_eq_some_none_iff
        context inputs fuel doneOutcome⟩

/-- A nested selected completion retains the exact continuation at larger fuel. -/
private theorem compileTimeSelectedFrameContinuationStabilityRegression
    {RollbackState : Type u}
    {TraceState : Type v}
    {TrapReason : Type w}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Value → Store → FrameOutcome TrapReason)
    {fuel largerFuel : Nat}
    {continuation :
      FrameContinuationContext RollbackState TraceState TrapReason}
    (completed :
      context.runCodeWithStorageContinuationContext?
        inputs fuel doneOutcome = some (some continuation))
    (more : fuel ≤ largerFuel) :
    context.runCodeWithStorageContinuationContext?
      inputs largerFuel doneOutcome = some (some continuation) :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_some_some_stable
    context inputs doneOutcome completed more

end Tests
end
