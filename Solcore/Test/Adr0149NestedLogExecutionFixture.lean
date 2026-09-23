import Solcore.ContractRuntime.OneLevelNestedExecution

/-! Executable root/child fixtures for rollback-scoped word logs. -/

set_option autoImplicit false

namespace Tests.Adr0149NestedLogExecutionFixture

open Solcore.Core
open Solcore.ContractRuntime

def rootAddress : Address := ⟨0x1490, by decide⟩
def childAddress : Address := ⟨0x1491, by decide⟩
def callerAddress : Address := ⟨0x1492, by decide⟩

def rootTopicBefore : Word := ⟨0x10, by decide⟩
def rootPayloadBefore : Word := ⟨0x11, by decide⟩
def childTopic : Word := ⟨0x20, by decide⟩
def childPayload : Word := ⟨0x21, by decide⟩
def rootTopicAfter : Word := ⟨0x30, by decide⟩
def rootPayloadAfter : Word := ⟨0x31, by decide⟩
def callInput : Word := ⟨0x40, by decide⟩
def returnPayload : Word := ⟨0x50, by decide⟩
def revertPayload : Word := ⟨0x51, by decide⟩
def trapReason : Word := ⟨0x52, by decide⟩

def rootBeforeLog : CheckedCoreWordLog :=
  ⟨rootAddress, rootTopicBefore, rootPayloadBefore⟩

def childLog : CheckedCoreWordLog :=
  ⟨childAddress, childTopic, childPayload⟩

def rootAfterLog : CheckedCoreWordLog :=
  ⟨rootAddress, rootTopicAfter, rootPayloadAfter⟩

def emitExpr (topic payload : Word) (shift : Nat := 0) : Expr :=
  .apply (.var (HostFunction.emitLogWord.index + shift))
    (.pair (.word topic) (.word payload))

def returnedExpr (payload : Word) : Expr :=
  .inLeft (.sum .word .word) (.word payload)

def revertedExpr (payload : Word) : Expr :=
  .inRight .word (.inLeft .word (.word payload))

def trappedExpr (reason : Word) : Expr :=
  .inRight .word (.inRight .word (.word reason))

inductive RootOutcome where
  | returned
  | reverted
  | trapped

def rootTerminalExpr : RootOutcome → Expr
  | .returned => returnedExpr returnPayload
  | .reverted => revertedExpr revertPayload
  | .trapped => trappedExpr trapReason

def rootProgram (outcome : RootOutcome) : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE (emitExpr rootTopicBefore rootPayloadBefore)
      (.letE
        (.apply (.var (HostFunction.callContractWord.index + 1))
          (.pair (.word (addressToWord childAddress)) (.word callInput)))
        (.letE (emitExpr rootTopicAfter rootPayloadAfter 2)
          (rootTerminalExpr outcome)))
}

theorem rootProgram_checked (outcome : RootOutcome) :
    (rootProgram outcome).checkHost = true := by
  cases outcome <;> decide

def rootContract (outcome : RootOutcome) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨rootProgram outcome, rootProgram_checked outcome⟩ rfl

def childTerminalExpr : CheckedCoreWordOutcome → Expr
  | .returned payload => returnedExpr payload
  | .reverted payload => revertedExpr payload
  | .trapped reason => trappedExpr reason

def childProgram (outcome : CheckedCoreWordOutcome) : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE (emitExpr childTopic childPayload)
      (childTerminalExpr outcome)
}

theorem childProgram_checked (outcome : CheckedCoreWordOutcome) :
    (childProgram outcome).checkHost = true := by
  cases outcome <;> rfl

def childContract (outcome : CheckedCoreWordOutcome) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨childProgram outcome, childProgram_checked outcome⟩ rfl

def rootAccount (outcome : RootOutcome) : Account :=
  Account.empty.withCode (rootContract outcome).code

def childAccount (outcome : CheckedCoreWordOutcome) : Account :=
  Account.empty.withCode (childContract outcome).code

def initialWorld
    (rootOutcome : RootOutcome)
    (childOutcome : CheckedCoreWordOutcome) : WorldState :=
  WorldState.empty
    |>.putAccount rootAddress (rootAccount rootOutcome)
    |>.putAccount childAddress (childAccount childOutcome)

def installedRoot
    (rootOutcome : RootOutcome)
    (childOutcome : CheckedCoreWordOutcome) :
    InstalledCheckedCoreContract
      (initialWorld rootOutcome childOutcome) rootAddress
      (rootContract rootOutcome) := {
  account := rootAccount rootOutcome
  account_present := by rfl
  code_present := by rfl
}

def registry
    (rootOutcome : RootOutcome)
    (childOutcome : CheckedCoreWordOutcome) : CheckedContractRegistry := {
  lookup := fun address =>
    if address = rootAddress then some (rootContract rootOutcome)
    else if address = childAddress then some (childContract childOutcome)
    else none
}

def invocation : TopLevelInvocation := {
  target := rootAddress
  caller := callerAddress
  callValue := Word.zero
  inputData := HostStorageDriver.InputData.ofWord callInput
}

def runScenario
    (rootOutcome : RootOutcome)
    (childOutcome : CheckedCoreWordOutcome)
    (fuel : Nat) :
    OneLevelNestedExecution.Result
      (initialWorld rootOutcome childOutcome)
      (rootContract rootOutcome) invocation :=
  OneLevelNestedExecution.run
    (rootContract rootOutcome) invocation
    (installedRoot rootOutcome childOutcome)
    (registry rootOutcome childOutcome) fuel

end Tests.Adr0149NestedLogExecutionFixture
