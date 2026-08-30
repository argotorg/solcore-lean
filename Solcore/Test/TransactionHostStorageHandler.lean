import Solcore.Semantics.ContractWordCallInput
import Solcore.Semantics.TransactionHostStorageHandlerProperties

/-! Focused executable checks for transaction-aware log handling. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def address (value : Nat) : Address :=
  ⟨value % addressModulus, Nat.mod_lt _ (by decide)⟩

private def word (value : Nat) : Word :=
  Word.ofNatModulo value

private def storageAddress : Address := address 17
private def callerAddress : Address := address 19
private def activeAddress : Address := address 23
private def account : Account := Account.empty
private def world : WorldState :=
  WorldState.empty.putAccount storageAddress account

private def earlier : CheckedCoreWordLog := {
  emitter := address 29
  topic := word 31
  payload := word 37
}

private def created : Address := address 41

private def initialJournal : TransactionJournal :=
  (TransactionJournal.empty.recordLog earlier).recordCreatedContract created

private def effects : FrameEffectJournal TransactionJournal Unit :=
  ⟨initialJournal, ()⟩

private def context : TransactionHostStorageDriver.Context :=
  ⟨⟨storageAddress,
      ⟨⟨world, effects⟩, (world, effects)⟩⟩,
    account,
    by rfl⟩

private def topic : Word := word 43
private def payload : Word := word 47

private def inputs : HostStorageDriver.ExecutionInputs := {
  codeAddress := activeAddress
  callValue := word 53
  callerAddress := callerAddress
  inputData := HostStorageDriver.InputData.ofWord payload
  currentAddress := activeAddress
}

private def firstHandled :
    TransactionHostStorageDriver.Context × Unit :=
  TransactionHostStorageDriver.handleRequest inputs context
    (.emitLogWord topic payload)

private def secondHandled :
    TransactionHostStorageDriver.Context × Unit :=
  TransactionHostStorageDriver.handleRequest inputs firstHandled.1
    (.emitLogWord topic payload)

private def expected : CheckedCoreWordLog := {
  emitter := activeAddress
  topic := topic
  payload := payload
}

private def exactJournal : Bool :=
  secondHandled.1.workingJournal.logList == [earlier, expected, expected] &&
    secondHandled.1.workingJournal.createdContractList == [created]

private theorem compileTimeExactJournal : exactJournal = true := by
  native_decide

private theorem compileTimeWorldPreserved :
    firstHandled.1.context.values.working.1 = world := by
  simp [firstHandled, context]

private theorem compileTimeAccountPreserved :
    firstHandled.1.storageAccount = account := by
  simp [firstHandled, context]

private theorem compileTimeSelectorPreserved :
    firstHandled.1.context.storageAddress = storageAddress := by
  simp [firstHandled, context]

private theorem compileTimeCheckpointPreserved :
    firstHandled.1.context.values.checkpoint = context.context.values.checkpoint := by
  simp [firstHandled]

def testTransactionHostStorageHandler : IO Unit := do
  assertTrue exactJournal
    "transaction log handling must append exact duplicate logs in order"

end Tests
