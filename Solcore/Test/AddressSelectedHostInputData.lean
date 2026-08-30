import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionProperties
import Solcore.Semantics.HostStorageDriverProperties

/-! End-to-end regressions for run-fixed optional input-byte observation. -/

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
private def callerAddress : Address := ⟨0x40, by decide⟩
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

private def inputsFor
    (inputData : HostStorageDriver.InputData) :
    HostStorageDriver.ExecutionInputs := {
  codeAddress := codeAddress
  callValue := callValue
  callerAddress := callerAddress
  inputData := inputData
  currentAddress := codeAddress
}

private def nonzeroInputs := inputsFor nonzeroInput
private def zeroInputs := inputsFor zeroInput
private def absentInputs := inputsFor absentInput

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

private def codeAccount : Account :=
  Account.empty.withCode inputByteCode

private def storageAccount : Account :=
  Account.empty.storageWrite storageSlot storageValue

private def checkpointWorld : WorldState :=
  WorldState.empty.putAccount storageAddress storageAccount

private def workingWorld : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress codeAccount
    |>.putAccount storageAddress storageAccount

private def baseContext :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨storageAddress,
    ⟨⟨checkpointWorld, ⟨7, [8]⟩⟩,
      (workingWorld, ⟨9, [10, 11]⟩)⟩⟩

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
    (inputByteCode.runWithStorage context (inputsFor first) 5).context =
      (inputByteCode.runWithStorage context (inputsFor second) 5).context :=
  (inputByte_runWithStorage_preserves_context context (inputsFor first)).trans
    (inputByte_runWithStorage_preserves_context
      context (inputsFor second)).symm

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

  match baseContext.withPresentStorageAccount? with
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
