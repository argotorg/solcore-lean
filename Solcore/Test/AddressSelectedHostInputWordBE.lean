import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionProperties
import Solcore.Semantics.HostStorageDriverProperties

/-! End-to-end regressions for strict optional big-endian input-word reads. -/

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
private def expectedWord : Word := ⟨0x01020304, by decide⟩

private def presentInput : HostStorageDriver.InputData := {
  bytes := [0xaa].toByteArray.append (encodeWordBytesBE expectedWord)
  size_lt_wordModulus := by native_decide
}

private def zeroInput : HostStorageDriver.InputData := {
  bytes := [0xaa].toByteArray.append (encodeWordBytesBE Word.zero)
  size_lt_wordModulus := by native_decide
}

private def incompleteInput : HostStorageDriver.InputData := {
  bytes := [0xaa, 0x01].toByteArray
  size_lt_wordModulus := by decide
}

private def inputsFor
    (inputData : HostStorageDriver.InputData) :
    HostStorageDriver.ExecutionInputs := {
  codeAddress := codeAddress
  callValue := callValue
  callerAddress := callerAddress
  inputData := inputData
}

private def presentInputs := inputsFor presentInput
private def zeroInputs := inputsFor zeroInput
private def incompleteInputs := inputsFor incompleteInput

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

private def storageSlot : Word := ⟨0x51, by decide⟩
private def storageValue : Word := ⟨0x52, by decide⟩

private def codeAccount : Account :=
  Account.empty.withCode inputWordCode

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
  ⟨.ret (.word observedOffset), [.hostApply .inputDataWordBE?], []⟩

private theorem inputWordProgram_suspends :
    hostRun 5 (State.initial inputWordProgram.body hostEnvironment) =
      .suspended ⟨.inputDataWordBE? observedOffset, [], []⟩ 0 := by
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

private theorem zero_outcome_exact
    (context : HostStorageDriver.Context Nat (List Nat)) :
    (inputWordCode.runWithStorage context zeroInputs 5).outcome =
      .done (.inRight .unit (.word Word.zero)) [] :=
  inputWord_outcome_of_some context zeroInputs Word.zero (by native_decide)

private theorem incomplete_outcome_exact
    (context : HostStorageDriver.Context Nat (List Nat)) :
    (inputWordCode.runWithStorage context incompleteInputs 5).outcome =
      .done (.inLeft .word .unit) [] :=
  inputWord_outcome_of_none context incompleteInputs (by native_decide)

private def assertCompleted
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
  assertTrue (zeroInput.wordBE? observedOffset == some Word.zero)
    "a complete zero window was confused with absence"
  assertTrue ((incompleteInput.wordBE? observedOffset).isNone)
    "an incomplete window was padded instead of rejected"

  match baseContext.withPresentStorageAccount? with
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
          assertTrue (result.outcome == .outOfFuel requestReadyState)
            "fuel 4 did not stop at the input-word request-ready state"
          assertTrue (contextLooksUnchanged result.context)
            "the request-ready boundary mutated the frame context"
          assertTrue
            (hostAdvance requestReadyState ==
              .suspended ⟨.inputDataWordBE? observedOffset, [], []⟩)
            "the boundary did not expose the exact input-word request"

      assertCompleted context presentInputs 5
        (.inRight .unit (.word expectedWord)) "complete nonzero window"
      assertCompleted context zeroInputs 5
        (.inRight .unit (.word Word.zero)) "complete zero window"
      assertCompleted context incompleteInputs 5
        (.inLeft .word .unit) "incomplete window"
      assertCompleted context presentInputs 32
        (.inRight .unit (.word expectedWord)) "larger-fuel complete window"
      assertCompleted context incompleteInputs 32
        (.inLeft .word .unit) "larger-fuel incomplete window"

end Tests
