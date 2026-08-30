import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionPreservationProperties

/-! End-to-end regression for a strict input-word-derived storage write. -/

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
private def absentAddress : Address := ⟨0x31, by decide⟩
private def callerAddress : Address := ⟨0x40, by decide⟩

private def observedOffset : Word := ⟨1, by decide⟩
private def expectedWord : Word := ⟨0x01020304, by decide⟩
private def targetSlot : Word := ⟨0x51, by decide⟩
private def retainedSlot : Word := ⟨0x52, by decide⟩
private def retainedValue : Word := ⟨0x53, by decide⟩
private def oldValue : Word := ⟨0x54, by decide⟩
private def otherSlot : Word := ⟨0x61, by decide⟩
private def otherValue : Word := ⟨0x62, by decide⟩
private def checkpointSlot : Word := ⟨0x71, by decide⟩
private def checkpointValue : Word := ⟨0x72, by decide⟩

private def completeInput : HostStorageDriver.InputData := {
  bytes := [0xaa].toByteArray.append (encodeWordBytesBE expectedWord)
  size_lt_wordModulus := by native_decide
}

private def incompleteInput : HostStorageDriver.InputData := {
  bytes := [0xaa, 0x01].toByteArray
  size_lt_wordModulus := by decide
}

private def inputsFor
    (data : HostStorageDriver.InputData) :
    HostStorageDriver.ExecutionInputs := {
  codeAddress := codeAddress
  callValue := Word.zero
  callerAddress := callerAddress
  inputData := data
  currentAddress := codeAddress
}

private def completeInputs := inputsFor completeInput
private def incompleteInputs := inputsFor incompleteInput

/--
Observe one strict optional word. Absence returns the left sentinel. Presence
writes the exact decoded word, observes the same window again, and returns both
observations.
-/
private def observeCaseWriteObserveProgram : Program := {
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
          (.pair (.word targetSlot) (.var 0)))
        (.caseE
          (.apply
            (.var (HostFunction.inputDataWordBE?.index + 2))
            (.word observedOffset))
          (.inLeft (.product .word .word) .unit)
          (.inRight .unit (.pair (.var 2) (.var 0)))))
}

private theorem observeCaseWriteObserveProgram_host_checked :
    observeCaseWriteObserveProgram.checkHost = true := by
  decide

private def observeCaseWriteObserveCode : CheckedHostCoreProgram :=
  ⟨observeCaseWriteObserveProgram,
    observeCaseWriteObserveProgram_host_checked⟩

private def selectedStorageAccount : Account :=
  Account.empty
    |>.storageWrite targetSlot oldValue
    |>.storageWrite retainedSlot retainedValue

private def workingWorld : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress
      (Account.empty.withCode observeCaseWriteObserveCode)
    |>.putAccount storageAddress selectedStorageAccount
    |>.putAccount otherAddress
      (Account.empty.storageWrite otherSlot otherValue)

private def checkpointWorld : WorldState :=
  WorldState.empty
    |>.putAccount storageAddress
      (Account.empty.storageWrite checkpointSlot checkpointValue)
    |>.putAccount otherAddress
      (Account.empty.storageWrite otherSlot otherValue)

private def baseContext :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨storageAddress,
    ⟨⟨checkpointWorld, ⟨11, [12, 13]⟩⟩,
      (workingWorld, ⟨21, [22, 23]⟩)⟩⟩

private def storageValueAt?
    (state : WorldState) (address : Address) (slot : Word) : Option Word :=
  (state.account? address).bind fun account => account.storageValue? slot

private def expectedResult (word : Word) : Value :=
  .inRight .unit (.pair (.word word) (.word word))

private def expectedAbsence : Value :=
  .inLeft (.product .word .word) .unit

private def codeProgramIs (state : WorldState) : Bool :=
  match state.code? codeAddress with
  | none => false
  | some code => code.program == observeCaseWriteObserveProgram

private def preservesUnrelated
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat)) :
    Bool :=
  let values := context.context.values
  context.context.storageAddress == storageAddress &&
    codeProgramIs values.working.1 &&
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
  context.storageAccount.storageValue? targetSlot == some word &&
    storageValueAt? working storageAddress targetSlot == some word

private def retainsOldValue
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat)) :
    Bool :=
  let working := context.context.values.working.1
  context.storageAccount.storageValue? targetSlot == some oldValue &&
    storageValueAt? working storageAddress targetSlot == some oldValue

private def inputDataWordRequestReady (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension =>
      suspension.request == .inputDataWordBE? observedOffset
  | _ => false

private def oneStepBeforeResult (word : Word) (state : State) : Bool :=
  match hostAdvance state with
  | .next next => next == State.final (expectedResult word)
  | _ => false

def testAddressSelectedHostInputWordBEStorage : IO Unit := do
  assertTrue observeCaseWriteObserveProgram.checkHost
    "the host checker rejected input-word/case/write/input-word"
  assertTrue (completeInput.wordBE? observedOffset == some expectedWord)
    "the complete nonzero window did not decode exactly"
  assertTrue ((incompleteInput.wordBE? observedOffset).isNone)
    "the incomplete window was padded instead of rejected"

  match baseContext.withPresentStorageAccount? with
  | none => throw (IO.userError "the selected storage Account was absent")
  | some context =>
      assertTrue
        (context.runCodeWithStorage?
          { completeInputs with codeAddress := absentAddress } 32).isNone
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
          assertTrue (preservesUnrelated resultContext)
            "fuel 23 changed unrelated context state"
      | some result =>
          throw (IO.userError
            s!"fuel 23 crossed the second observation: {reprStr result.outcome}")
      | none => throw (IO.userError "fuel 23 lost the selected code")

      match context.runCodeWithStorage? completeInputs 31 with
      | some { context := resultContext, outcome := .outOfFuel state } =>
          assertTrue (oneStepBeforeResult expectedWord state)
            "fuel 31 did not stop one step before the successful pair"
          assertTrue (storesDecodedWord resultContext expectedWord)
            "fuel 31 lost the word-derived write"
          assertTrue (preservesUnrelated resultContext)
            "fuel 31 changed unrelated context state"
      | some result =>
          throw (IO.userError
            s!"fuel 31 crossed the completion boundary: {reprStr result.outcome}")
      | none => throw (IO.userError "fuel 31 lost the selected code")

      match context.runCodeWithStorage? completeInputs 32,
          context.runCodeWithStorage? completeInputs 64 with
      | some result, some largerResult =>
          assertTrue
            (result.outcome == .done (expectedResult expectedWord) [])
            "fuel 32 did not return both exact input-word observations"
          assertTrue (largerResult.outcome == result.outcome)
            "additional fuel changed the exact successful result"
          assertTrue (storesDecodedWord result.context expectedWord)
            "completion did not store the decoded word"
          assertTrue (storesDecodedWord largerResult.context expectedWord)
            "larger-fuel completion lost the decoded word"
          assertTrue
            (preservesUnrelated result.context &&
              preservesUnrelated largerResult.context)
            "completion changed unrelated storage or frame fields"
      | none, _ => throw (IO.userError "fuel 32 lost the selected code")
      | _, none => throw (IO.userError "additional fuel lost the selected code")

      match context.runCodeWithStorage? incompleteInputs 32,
          context.runCodeWithStorage? incompleteInputs 64 with
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
            (preservesUnrelated result.context &&
              preservesUnrelated largerResult.context)
            "the incomplete-window branch changed unrelated context state"
      | none, _ => throw (IO.userError "the incomplete-window run lost code")
      | _, none => throw (IO.userError "larger-fuel incomplete run lost code")

end Tests
