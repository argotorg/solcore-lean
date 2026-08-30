import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionProperties
import Solcore.Semantics.HostStorageDriverProperties

/-! End-to-end regressions for exact run-fixed input-size observation. -/

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

private def emptyInput : HostStorageDriver.InputData := {
  bytes := [].toByteArray
  size_lt_wordModulus := by decide
}

private def nonemptyInput : HostStorageDriver.InputData := {
  bytes := [0xa5, 0x00, 0x7f].toByteArray
  size_lt_wordModulus := by decide
}

private def expectedNonemptySize : Word := ⟨3, by decide⟩

private def inputsFor
    (inputData : HostStorageDriver.InputData) :
    HostStorageDriver.ExecutionInputs := {
  codeAddress := codeAddress
  callValue := callValue
  callerAddress := callerAddress
  inputData := inputData
  currentAddress := codeAddress
}

private def emptyInputs := inputsFor emptyInput
private def nonemptyInputs := inputsFor nonemptyInput

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

private def storageSlot : Word := ⟨0x51, by decide⟩
private def storageValue : Word := ⟨0x52, by decide⟩

private def codeAccount : Account :=
  Account.empty.withCode inputSizeCode

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
  ⟨.ret .unit, [.hostApply .inputDataSize], []⟩

private theorem inputSizeProgram_stops_request_ready :
    hostRun 4 (State.initial inputSizeProgram.body hostEnvironment) =
      .outOfFuel requestReadyState := by
  native_decide

private theorem inputSizeProgram_suspends :
    hostRun 5 (State.initial inputSizeProgram.body hostEnvironment) =
      .suspended ⟨.inputDataSize, [], []⟩ 0 := by
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
    (inputSizeCode.runWithStorage context (inputsFor first) 5).context =
      (inputSizeCode.runWithStorage context (inputsFor second) 5).context := by
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

private def assertCompleted
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

  match baseContext.withPresentStorageAccount? with
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
          assertTrue (result.outcome == .outOfFuel requestReadyState)
            "fuel 4 did not stop at the input-size request-ready state"
          assertTrue (contextLooksUnchanged result.context)
            "the request-ready boundary mutated the frame context"
          assertTrue
            (hostAdvance requestReadyState ==
              .suspended ⟨.inputDataSize, [], []⟩)
            "the fuel boundary did not expose the exact input-size request"

      assertCompleted context emptyInputs 5 Word.zero "empty input"
      assertCompleted context nonemptyInputs 5 expectedNonemptySize
        "nonempty input"
      assertCompleted context emptyInputs 32 Word.zero
        "larger-fuel empty input"
      assertCompleted context nonemptyInputs 32 expectedNonemptySize
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
