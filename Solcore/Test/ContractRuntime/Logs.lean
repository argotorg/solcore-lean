import Solcore.ContractRuntime.Internal.NestedLaws
import Solcore.Test.ContractRuntime.Creation
import Solcore.Core.Internal.HostPreservation
import Solcore.Core.HostRunner
import Solcore.ContractRuntime.Internal.WorldStateLaws
import Solcore.ContractRuntime.Internal.TopLevelLaws
import Solcore.Test.ContractRuntime.TopLevelExecution
import Solcore.ContractRuntime.Internal.DriverLaws
import Solcore.ContractRuntime.Internal.StorageDriverLaws

/-!
# Log tests

The ADR-0149 logs: top-level, balanced, nested and creation-scoped logs, with commit and rollback.
-/

section
-- leanmerge: from Solcore.Test.Adr0149CreationLogExecutionFixture
/-! Checked creation programs with logs on both sides of the initializer. -/

set_option autoImplicit false

namespace Tests.Adr0149CreationLogExecutionFixture

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.ContractRuntime.OneLevelNestedExecution
open Adr0148CreationEndToEndFixture

def rootTopicBefore : Word := ⟨0x14910, by decide⟩
def rootPayloadBefore : Word := ⟨0x14911, by decide⟩
def initializerTopicFirst : Word := ⟨0x14920, by decide⟩
def initializerPayloadFirst : Word := ⟨0x14921, by decide⟩
def initializerTopicSecond : Word := ⟨0x14930, by decide⟩
def initializerPayloadSecond : Word := ⟨0x14931, by decide⟩
def rootTopicAfter : Word := ⟨0x14940, by decide⟩
def rootPayloadAfter : Word := ⟨0x14941, by decide⟩

def rootLogBefore : CheckedCoreWordLog :=
  ⟨creator, rootTopicBefore, rootPayloadBefore⟩

def initializerLogFirst : CheckedCoreWordLog :=
  ⟨created, initializerTopicFirst, initializerPayloadFirst⟩

def initializerLogSecond : CheckedCoreWordLog :=
  ⟨created, initializerTopicSecond, initializerPayloadSecond⟩

def rootLogAfter : CheckedCoreWordLog :=
  ⟨creator, rootTopicAfter, rootPayloadAfter⟩

def emitExpr (topic payload : Word) (shift : Nat := 0) : Expr :=
  .apply (.var (HostFunction.emitLogWord.index + shift))
    (.pair (.word topic) (.word payload))

def initializerProgram (outcome : CheckedCoreWordOutcome) : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE (emitExpr initializerTopicFirst initializerPayloadFirst)
      (.letE (emitExpr initializerTopicSecond initializerPayloadSecond 1)
        (initializerTerminal outcome))
}

theorem initializerProgram_checked (outcome : CheckedCoreWordOutcome) :
    (initializerProgram outcome).checkHost = true := by
  cases outcome <;> rfl

def initializerContract
    (outcome : CheckedCoreWordOutcome) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨initializerProgram outcome, initializerProgram_checked outcome⟩ rfl

inductive RootDisposition where
  | commit
  | revert
  | trap
  | catchFailure
  deriving Repr, BEq, DecidableEq

def successExpr : RootDisposition → Expr
  | .commit | .catchFailure => returned (.var 0)
  | .revert => reverted (.word rootRevertReason)
  | .trap => trapped (.word rootTrapReason)

def revertedResponseExpr : RootDisposition → Expr
  | .catchFailure => returned (.var 0)
  | _ => reverted (.var 0)

def trappedResponseExpr : RootDisposition → Expr
  | .catchFailure => returned (.var 0)
  | _ => trapped (.var 0)

/-- Decode the creation response stored below the post-request log binding. -/
def consumeStoredCreationResult (disposition : RootDisposition) : Expr :=
  .caseE (.var 1)
    (successExpr disposition)
    (.caseE (.var 0)
      (revertedResponseExpr disposition)
      (.caseE (.var 0)
        (trappedResponseExpr disposition)
        (trappedResponseExpr disposition)))

def rootProgram (disposition : RootDisposition) : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE (emitExpr rootTopicBefore rootPayloadBefore)
      (.letE (creationExpr 1)
        (.letE (emitExpr rootTopicAfter rootPayloadAfter 2)
          (consumeStoredCreationResult disposition)))
}

theorem rootProgram_checked (disposition : RootDisposition) :
    (rootProgram disposition).checkHost = true := by
  cases disposition <;> native_decide

def rootContract (disposition : RootDisposition) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨rootProgram disposition, rootProgram_checked disposition⟩ rfl

def creationWorld (disposition : RootDisposition) : WorldState :=
  Adr0148CreationEndToEndFixture.initialWorld (rootContract disposition)

def installedRoot (disposition : RootDisposition) :
    InstalledCheckedCoreContract (creationWorld disposition) creator
      (rootContract disposition) :=
  Adr0148CreationEndToEndFixture.rootInstalled (rootContract disposition)

def creationEnvironment
    (outcome : CheckedCoreWordOutcome) : ExecutionEnvironment :=
  environmentFor (initializerContract outcome)

def runScenario
    (disposition : RootDisposition)
    (initializerOutcome : CheckedCoreWordOutcome)
    (fuel : Nat) :
    Result (creationWorld disposition) (rootContract disposition) invocation :=
  runWithEnvironment (rootContract disposition) invocation
    (installedRoot disposition) (creationEnvironment initializerOutcome) fuel

def runWithSelectedEnvironment
    (disposition : RootDisposition)
    (environment : ExecutionEnvironment)
    (fuel : Nat) :
    Result (creationWorld disposition) (rootContract disposition) invocation :=
  runWithEnvironment (rootContract disposition) invocation
    (installedRoot disposition) environment fuel

def insufficientCreatorBalance : Word := ⟨2, by decide⟩

def insufficientRootAccount (disposition : RootDisposition) : Account :=
  Account.empty.withBalance insufficientCreatorBalance |>.withNonce oldNonce
    |>.withCode (rootContract disposition).code

def insufficientCreationWorld (disposition : RootDisposition) : WorldState :=
  WorldState.empty
    |>.putAccount unrelated unrelatedAccount
    |>.putAccount creator (insufficientRootAccount disposition)

def insufficientRootInstalled (disposition : RootDisposition) :
    InstalledCheckedCoreContract (insufficientCreationWorld disposition)
      creator (rootContract disposition) := {
  account := insufficientRootAccount disposition
  account_present := by rfl
  code_present := by rfl
}

def runWithInsufficientBalance (fuel : Nat) :
    Result (insufficientCreationWorld .catchFailure)
      (rootContract .catchFailure) invocation :=
  runWithEnvironment (rootContract .catchFailure) invocation
    (insufficientRootInstalled .catchFailure)
    (creationEnvironment (.returned initializerInput)) fuel

def unavailableCreationEnvironment : ExecutionEnvironment :=
  .callsOnly { lookup := fun _ => none }

def collisionCreationEnvironment : ExecutionEnvironment :=
  let base := creationEnvironment (.returned initializerInput)
  { base with
    creationAddressPolicy := {
      derive := fun _creator _nonce => unrelated
    }
  }

def successfulLogs : List CheckedCoreWordLog :=
  [rootLogBefore, initializerLogFirst, initializerLogSecond, rootLogAfter]

def failedInitializerLogs : List CheckedCoreWordLog :=
  [rootLogBefore, rootLogAfter]

def secondCreated : Address := ⟨0x2484, by decide⟩

/-- Run a second creation only after the first one returned successfully. -/
def sequentialCreationProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .caseE creationExpr
      (consumeResult .commit (creationExpr 1))
      (.caseE (.var 0)
        (reverted (.var 0))
        (.caseE (.var 0)
          (trapped (.var 0))
          (trapped (.var 0))))
}

theorem sequentialCreationProgram_checked :
    sequentialCreationProgram.checkHost = true := by
  native_decide

def sequentialCreationRoot : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨sequentialCreationProgram, sequentialCreationProgram_checked⟩ rfl

def sequentialCreationWorld : WorldState :=
  Adr0148CreationEndToEndFixture.initialWorld sequentialCreationRoot

def sequentialCreationInstalled :
    InstalledCheckedCoreContract sequentialCreationWorld creator
      sequentialCreationRoot :=
  Adr0148CreationEndToEndFixture.rootInstalled sequentialCreationRoot

def successfulInitializerOutcome : CheckedCoreWordOutcome :=
  .returned initializerInput

def sequentialCreationEnvironment : ExecutionEnvironment := {
  callRegistry := {
    lookup := fun address =>
      if address = created ∨ address = secondCreated then some runtime else none
  }
  creationTemplates := (environmentFor
    (initializerContract successfulInitializerOutcome)).creationTemplates
  creationAddressPolicy := {
    derive := fun actualCreator nonce =>
      if actualCreator = creator ∧ nonce = oldNonce then created
      else if actualCreator = creator ∧ nonce = ⟨8, by decide⟩ then
        secondCreated
      else unrelated
  }
}

def runSequentialCreations (fuel : Nat) :
    Result sequentialCreationWorld sequentialCreationRoot invocation :=
  runWithEnvironment sequentialCreationRoot invocation
    sequentialCreationInstalled sequentialCreationEnvironment fuel

def secondInitializerLogFirst : CheckedCoreWordLog :=
  ⟨secondCreated, initializerTopicFirst, initializerPayloadFirst⟩

def secondInitializerLogSecond : CheckedCoreWordLog :=
  ⟨secondCreated, initializerTopicSecond, initializerPayloadSecond⟩

def sequentialInitializerLogs : List CheckedCoreWordLog :=
  [initializerLogFirst, initializerLogSecond,
    secondInitializerLogFirst, secondInitializerLogSecond]

end Tests.Adr0149CreationLogExecutionFixture
end

section
-- leanmerge: from Solcore.Test.Adr0149EmitLogWordBoundary
/-! Executable and proof-contract checks for the append-only log boundary. -/

set_option autoImplicit false

namespace Tests.Adr0149EmitLogWordBoundary

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

example := HostFunction.parameterType_emitLogWord
example := HostFunction.resultType_emitLogWord
example := HostFunction.index_emitLogWord
example := hostContext_emitLogWord
example := hostEnvironment_emitLogWord
example := HostRequest.responseType_emitLogWord
example := HostRequest.responseValue_emitLogWord
example := HostSuspension.resume_emitLogWord
example := hostAdvance_begin_emitLogWord
example := hostAdvance_suspend_emitLogWord
example := hostAdvance_invalid_emitLogWord_argument
example := @typed_emitLogWord_emits

private def topic : Word := ⟨0x149, by decide⟩
private def payload : Word := ⟨0xfeed, by decide⟩

private def emitProgram : Program := {
  resultType := .unit
  body :=
    .apply
      (.var HostFunction.emitLogWord.index)
      (.pair (.word topic) (.word payload))
}

private theorem emitProgram_checked : emitProgram.checkHost = true := by
  decide

private def illTypedEmitProgram : Program := {
  resultType := .unit
  body :=
    .apply
      (.var HostFunction.emitLogWord.index)
      (.pair (.word topic) (.bool true))
}

private theorem illTypedEmitProgram_rejected :
    illTypedEmitProgram.checkHost = false := by
  decide

private def emitsExactRequestAndResumes : Bool :=
  match emitProgram.runHostStateful 32 with
  | .suspended
      ⟨.emitLogWord actualTopic actualPayload, continuation, store⟩
      remainingFuel =>
      actualTopic == topic && actualPayload == payload &&
        match hostRun remainingFuel
            ((HostSuspension.mk
              (.emitLogWord actualTopic actualPayload)
              continuation store).resume ()) with
        | .done returned finalStore =>
            returned == .unit && finalStore == []
        | _ => false
  | _ => false

private def appendOnlyRegistryExact : Bool :=
  HostFunction.emitLogWord.index == 13 &&
    HostFunction.all.length == 14 &&
    HostFunction.all[13]? == some .emitLogWord &&
    hostContext[13]? == some (HostFunction.functionType .emitLogWord) &&
    hostEnvironment[13]? == some (.hostFunction .emitLogWord) &&
    hostContext[14]? == none && hostEnvironment[14]? == none

private theorem compileTimeBoundaryExact :
    emitsExactRequestAndResumes && appendOnlyRegistryExact = true := by
  native_decide

def testAdr0149EmitLogWordBoundary : IO Unit := do
  assertTrue emitsExactRequestAndResumes
    "checked emit-log did not preserve topic/payload order and unit resumption"
  assertTrue appendOnlyRegistryExact
    "emit-log did not occupy the append-only host index 13"

end Tests.Adr0149EmitLogWordBoundary
end

section
-- leanmerge: from Solcore.Test.Adr0149NestedLogExecutionFixture
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
end

section
-- leanmerge: from Solcore.Test.Adr0149TopLevelLogsFixture
/-! Checked root fixture for executable transaction-log finalization. -/

set_option autoImplicit false

namespace Tests.Adr0149TopLevelLogsFixture

open Solcore.Core
open Solcore.ContractRuntime

def targetAddress : Address := ⟨0x1490, by decide⟩
def callerAddress : Address := ⟨0x1491, by decide⟩

def returnSelector : Word := Word.zero
def revertSelector : Word := ⟨1, by decide⟩
def trapSelector : Word := ⟨2, by decide⟩

def firstTopic : Word := ⟨0x11, by decide⟩
def firstPayload : Word := ⟨0xa1, by decide⟩
/-- Deliberately duplicate the first entry to make multiplicity observable. -/
def secondTopic : Word := firstTopic
def secondPayload : Word := firstPayload

def returnPayload : Word := ⟨0xc3, by decide⟩
def revertPayload : Word := ⟨0xd4, by decide⟩
def trapReason : Word := ⟨0xe5, by decide⟩

def returnedExpr : Expr :=
  .inLeft (.sum .word .word) (.word returnPayload)

def revertedExpr : Expr :=
  .inRight .word (.inLeft .word (.word revertPayload))

def trappedExpr : Expr :=
  .inRight .word (.inRight .word (.word trapReason))

def emitExpr (environmentOffset : Nat) (topic payload : Word) : Expr :=
  .apply
    (.var (HostFunction.emitLogWord.index + environmentOffset))
    (.pair (.word topic) (.word payload))

/-- Emit two ordered word logs, then select the root outcome from call value. -/
def program : Program := {
  resultType := .sum .word (.sum .word .word)
  body :=
    .letE (emitExpr 0 firstTopic firstPayload)
      (.letE (emitExpr 1 secondTopic secondPayload)
        (.letE
          (.apply (.var (HostFunction.callValue.index + 2)) .unit)
          (.ifE
            (.binary .wordEq (.var 0) (.word returnSelector))
            returnedExpr
            (.ifE
              (.binary .wordEq (.var 0) (.word revertSelector))
              revertedExpr
              trappedExpr))))
}

theorem program_host_checked : program.checkHost = true := by
  decide

def code : CheckedHostCoreProgram :=
  ⟨program, program_host_checked⟩

def contract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 code rfl

def targetAccount : Account :=
  Account.empty.withCode code

def initialWorld : WorldState :=
  WorldState.empty.putAccount targetAddress targetAccount

def emptyInputData : HostStorageDriver.InputData := {
  bytes := [].toByteArray
  size_lt_wordModulus := by decide
}

def installed :
    InstalledCheckedCoreContract initialWorld targetAddress contract := {
  account := targetAccount
  account_present := by
    exact WorldState.account?_putAccount_same
      WorldState.empty targetAddress targetAccount
  code_present := by
    change targetAccount.code? = some code
    simp [targetAccount]
}

def invocationWith (selector : Word) : TopLevelInvocation := {
  target := targetAddress
  caller := callerAddress
  callValue := selector
  inputData := emptyInputData
}

def runWith (selector : Word) (fuel : Nat) :=
  TopLevelExecution.run contract (invocationWith selector) installed fuel

def firstLog : CheckedCoreWordLog := {
  emitter := targetAddress
  topic := firstTopic
  payload := firstPayload
}

def secondLog : CheckedCoreWordLog := {
  emitter := targetAddress
  topic := secondTopic
  payload := secondPayload
}

def expectedLogs : List CheckedCoreWordLog := [firstLog, secondLog]

end Tests.Adr0149TopLevelLogsFixture
end

section
-- leanmerge: from Solcore.Test.Adr0149BalancedTopLevelLogs
/-! Balance preflight combined with root log commit, rollback, and resumption. -/

set_option autoImplicit false

namespace Tests.Adr0149BalancedTopLevelLogs

open Solcore.Core
open Solcore.ContractRuntime

open Tests.Adr0147BalancedTopLevelExecutionFixture
open Tests.Adr0149TopLevelLogsFixture

private def executionTargetAddress : Address :=
  Tests.TopLevelExecutionFixture.targetAddress

private def executionCallerAddress : Address :=
  Tests.TopLevelExecutionFixture.callerAddress

private def returningProgram : Program := {
  resultType := .sum .word (.sum .word .word)
  body :=
    .letE (emitExpr 0 firstTopic firstPayload)
      (.letE (emitExpr 1 secondTopic secondPayload)
        returnedExpr)
}

private theorem returningProgram_checked :
    returningProgram.checkHost = true := by
  decide

private def returningCode : CheckedHostCoreProgram :=
  ⟨returningProgram, returningProgram_checked⟩

private def returningContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 returningCode rfl

private def expectedFirstLog : CheckedCoreWordLog := {
  emitter := executionTargetAddress
  topic := firstTopic
  payload := firstPayload
}

private def expectedSecondLog : CheckedCoreWordLog := {
  emitter := executionTargetAddress
  topic := secondTopic
  payload := secondPayload
}

private def expectedLogs : List CheckedCoreWordLog :=
  [expectedFirstLog, expectedSecondLog]

private def runReturning (callerBalance value : Word) (fuel : Nat) :=
  BalancedTopLevelExecution.run returningContract
    (invocationFrom executionCallerAddress value)
    (installedWithBalances returningContract callerBalance three)
    emptyRegistry fuel

private def runExisting (value : Word) (fuel : Nat) :=
  BalancedTopLevelExecution.run contract
    (invocationFrom executionCallerAddress value)
    (installedWithBalances contract ten three)
    emptyRegistry fuel

private def workingLogs?
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation) :
    Option (List CheckedCoreWordLog) :=
  result.workingJournal?.map TransactionJournal.logList

private def committedLogs?
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation) :
    Option (List CheckedCoreWordLog) :=
  result.committedJournal?.map TransactionJournal.logList

private def terminalBalances?
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation) :
    Option (Option Word × Option Word) :=
  result.finalWorld?.map fun world =>
    (world.balance? executionCallerAddress,
      world.balance? executionTargetAddress)

private def terminalOutcome?
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation) :
    Option (FrameOutcome Word) :=
  match result.terminalStatus? with
  | some (.ok outcome) => some outcome
  | _ => none

private def nonzeroReturnCommitsLogs : Bool :=
  let result := runReturning ten one completionFuel
  terminalOutcome? result ==
      some (.returned (encodeWordBytesBE returnPayload)) &&
    workingLogs? result == some expectedLogs &&
    committedLogs? result == some expectedLogs &&
    terminalBalances? result == some (some nine, some four)

private def rootFailureRollsBackLogs : Bool :=
  let reverted := runExisting one completionFuel
  let trapped := runExisting two completionFuel
  terminalOutcome? reverted ==
      some (.reverted (encodeWordBytesBE revertPayload)) &&
    workingLogs? reverted == some expectedLogs &&
    committedLogs? reverted == some [] &&
    terminalBalances? reverted == some (some ten, some three) &&
    terminalOutcome? trapped == some (.trapped trapReason) &&
    workingLogs? trapped == some expectedLogs &&
    committedLogs? trapped == some [] &&
    terminalBalances? trapped == some (some ten, some three)

private def rejectionIsIdentityWithEmptyJournal : Bool :=
  let result := runReturning zero one completionFuel
  match result.view with
  | .execution _ => false
  | .rejected rejected =>
      rejected.failure == .insufficientBalance &&
        rejected.finalWorld.balance? executionCallerAddress == some zero &&
        rejected.finalWorld.balance? executionTargetAddress == some three &&
        rejected.committedDelta.balanceChange? executionCallerAddress == none &&
        rejected.committedDelta.balanceChange? executionTargetAddress == none &&
        rejected.committedJournal.logList == [] &&
        workingLogs? result == some [] && committedLogs? result == some []

private def zeroValuePreservesJournalExecution : Bool :=
  let result :=
    BalancedTopLevelExecution.run returningContract
      (invocationFrom executionCallerAddress zero)
      (installedWithoutCaller returningContract three)
      emptyRegistry completionFuel
  terminalOutcome? result ==
      some (.returned (encodeWordBytesBE returnPayload)) &&
    workingLogs? result == some expectedLogs &&
    committedLogs? result == some expectedLogs &&
    terminalBalances? result == some (none, some three)

private def inFlightLogs?
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation) :
    Option (List CheckedCoreWordLog) :=
  match result.view with
  | .rejected _ => none
  | .execution execution =>
      match execution.view with
      | .completed _ => none
      | .outOfFuel _ (.root frame) _ =>
          some frame.context.workingJournal.logList
      | .outOfFuel _ (.child _) _ => none
      | .outOfFuel _ (.initializer _) _ => none

private def findOneLogSplit : Nat → Nat → Option Nat
  | _, 0 => none
  | fuel, remaining + 1 =>
      if inFlightLogs? (runReturning ten one fuel) ==
          some [expectedFirstLog]
      then some fuel
      else findOneLogSplit (fuel + 1) remaining

private def splitResumeIsExactlyOnce : Bool :=
  match findOneLogSplit 0 256 with
  | none => false
  | some splitFuel =>
      let prefixRun := runReturning ten one splitFuel
      let resumed :=
        BalancedTopLevelExecution.resumeWithFuel prefixRun completionFuel
      let oneShot :=
        runReturning ten one completionFuel
      prefixRun.workingJournal?.isNone && prefixRun.committedJournal?.isNone &&
        inFlightLogs? prefixRun == some [expectedFirstLog] &&
        workingLogs? resumed == some expectedLogs &&
        committedLogs? resumed == some expectedLogs &&
        workingLogs? resumed == workingLogs? oneShot &&
        committedLogs? resumed == committedLogs? oneShot &&
        terminalBalances? resumed == some (some nine, some four)

private theorem allScenarios_exact :
    nonzeroReturnCommitsLogs && rootFailureRollsBackLogs &&
      rejectionIsIdentityWithEmptyJournal &&
      zeroValuePreservesJournalExecution && splitResumeIsExactlyOnce = true := by
  native_decide

def testAdr0149BalancedTopLevelLogs : IO Unit := do
  unless nonzeroReturnCommitsLogs do
    throw (IO.userError "nonzero root return did not commit ordered logs")
  unless rootFailureRollsBackLogs do
    throw (IO.userError "root failure did not roll logs and balances back")
  unless rejectionIsIdentityWithEmptyJournal do
    throw (IO.userError "transfer rejection did not expose an empty journal")
  unless zeroValuePreservesJournalExecution do
    throw (IO.userError "zero-value journal execution diverged from the nested path")
  unless splitResumeIsExactlyOnce do
    throw (IO.userError "balanced log resumption duplicated transfer or logs")

end Tests.Adr0149BalancedTopLevelLogs
end

section
-- leanmerge: from Solcore.Test.Adr0149CreationLogExecution
/-! Runtime regressions for creation-scoped logs and creation observations. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.ContractRuntime.OneLevelNestedExecution
open Adr0148CreationEndToEndFixture
open Adr0149CreationLogExecutionFixture

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def completionFuel : Nat := 512

private def successfulInitializer : CheckedCoreWordOutcome :=
  .returned initializerInput

private def revertedInitializer : CheckedCoreWordOutcome :=
  .reverted initializerInput

private def trappedInitializer : CheckedCoreWordOutcome :=
  .trapped initializerInput

private def successfulCreationJournals : Bool :=
  match (runScenario .commit successfulInitializer completionFuel).view with
  | .outOfFuel _ _ _ => false
  | .completed terminal =>
      terminal.outcome ==
          .returned (encodeWordBytesBE (addressToWord created)) &&
        terminal.workingJournal.logList == successfulLogs &&
        terminal.committedJournal.logList == successfulLogs &&
        terminal.workingJournal.createdContractList == [created] &&
        terminal.committedJournal.createdContractList == [created] &&
        terminal.finalWorld.nonce? creator == some ⟨8, by decide⟩

private def failedInitializerRollsBack
    (outcome : CheckedCoreWordOutcome) : Bool :=
  match (runScenario .catchFailure outcome completionFuel).view with
  | .outOfFuel _ _ _ => false
  | .completed terminal =>
      terminal.workingJournal.logList == failedInitializerLogs &&
        terminal.committedJournal.logList == failedInitializerLogs &&
        terminal.workingJournal.createdContractList == [] &&
        terminal.committedJournal.createdContractList == [] &&
        terminal.finalWorld.nonce? creator == some ⟨8, by decide⟩ &&
        (terminal.finalWorld.account? created).isNone

private def revertedInitializerRollsBack : Bool :=
  failedInitializerRollsBack revertedInitializer

private def trappedInitializerRollsBack : Bool :=
  failedInitializerRollsBack trappedInitializer

private def laterRootRollback
    (disposition : RootDisposition)
    (expected : FrameOutcome Word) : Bool :=
  match (runScenario disposition successfulInitializer completionFuel).view with
  | .outOfFuel _ _ _ => false
  | .completed terminal =>
      terminal.outcome == expected &&
        terminal.workingJournal.logList == successfulLogs &&
        terminal.workingJournal.createdContractList == [created] &&
        terminal.committedJournal.logList == [] &&
        terminal.committedJournal.createdContractList == [] &&
        terminal.finalWorld.nonce? creator == some oldNonce &&
        (terminal.finalWorld.account? created).isNone

private def laterRootRevertRollsBack : Bool :=
  laterRootRollback .revert
    (.reverted (encodeWordBytesBE rootRevertReason))

private def laterRootTrapRollsBack : Bool :=
  laterRootRollback .trap (.trapped rootTrapReason)

private def retainedJournal
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation} :
    Mode initialWorld rootContract rootInvocation → TransactionJournal
  | .root frame => frame.context.workingJournal
  | .child frame => frame.childContext.workingJournal
  | .initializer frame => frame.initializerContext.workingJournal

private def validSuccessfulPrefix (journal : TransactionJournal) : Bool :=
  let logs := journal.logList
  let creations := journal.createdContractList
  successfulLogs.take logs.length == logs &&
    (creations == [] || creations == [created]) &&
    (creations.isEmpty || decide (3 ≤ logs.length))

private def resumedJournalExact (prefixFuel : Nat) : Bool :=
  let prefixResult := runScenario .commit successfulInitializer prefixFuel
  match prefixResult.view with
  | .completed terminal =>
      terminal.workingJournal.logList == successfulLogs &&
        terminal.workingJournal.createdContractList == [created] &&
        terminal.committedJournal.logList == successfulLogs &&
        terminal.committedJournal.createdContractList == [created]
  | .outOfFuel _ mode _ =>
      validSuccessfulPrefix (retainedJournal mode) &&
        (match (resumeWithFuel prefixResult completionFuel).view with
        | .outOfFuel _ _ _ => false
        | .completed terminal =>
            terminal.workingJournal.logList == successfulLogs &&
              terminal.workingJournal.createdContractList == [created] &&
              terminal.committedJournal.logList == successfulLogs &&
              terminal.committedJournal.createdContractList == [created])

private def everyOutOfFuelBoundaryIsExactlyOnce : Bool :=
  (List.range 180).all resumedJournalExact

private def initializerPrefixVisible (fuel : Nat) : Bool :=
  match (runScenario .commit successfulInitializer fuel).view with
  | .outOfFuel _ (.initializer frame) _ =>
      frame.initializerContext.workingJournal.logList ==
        [rootLogBefore, initializerLogFirst, initializerLogSecond]
  | _ => false

private def completedCreationVisibleBeforeRootLog (fuel : Nat) : Bool :=
  match (runScenario .commit successfulInitializer fuel).view with
  | .outOfFuel _ (.root frame) _ =>
      frame.context.workingJournal.createdContractList == [created] &&
        frame.context.workingJournal.logList ==
          [rootLogBefore, initializerLogFirst, initializerLogSecond]
  | _ => false

private def criticalBoundariesAreVisible : Bool :=
  (List.range 180).any initializerPrefixVisible &&
    (List.range 180).any completedCreationVisibleBeforeRootLog

private def sequentialCreationsPreserveCompletionOrder : Bool :=
  match (runSequentialCreations completionFuel).view with
  | .outOfFuel _ _ _ => false
  | .completed terminal =>
      terminal.outcome ==
          .returned (encodeWordBytesBE (addressToWord secondCreated)) &&
        terminal.workingJournal.logList == sequentialInitializerLogs &&
        terminal.committedJournal.logList == sequentialInitializerLogs &&
        terminal.workingJournal.createdContractList ==
          [created, secondCreated] &&
        terminal.committedJournal.createdContractList ==
          [created, secondCreated] &&
        terminal.finalWorld.nonce? creator == some ⟨9, by decide⟩ &&
        (terminal.finalWorld.code? created).isSome &&
        (terminal.finalWorld.code? secondCreated).isSome

private def preflightFailureLeavesJournalIdentity
    (environment : ExecutionEnvironment) : Bool :=
  match (runWithSelectedEnvironment .catchFailure environment
      completionFuel).view with
  | .outOfFuel _ _ _ => false
  | .completed terminal =>
      terminal.workingJournal.logList == failedInitializerLogs &&
        terminal.committedJournal.logList == failedInitializerLogs &&
        terminal.workingJournal.createdContractList == [] &&
        terminal.committedJournal.createdContractList == [] &&
        terminal.finalWorld.nonce? creator == some oldNonce &&
        (terminal.finalWorld.account? created).isNone

private def checkedPreflightFailuresLeaveJournalIdentity : Bool :=
  [unavailableCreationEnvironment, collisionCreationEnvironment].all
    preflightFailureLeavesJournalIdentity

private def insufficientBalanceLeavesJournalIdentity : Bool :=
  match (runWithInsufficientBalance completionFuel).view with
  | .outOfFuel _ _ _ => false
  | .completed terminal =>
      terminal.workingJournal.logList == failedInitializerLogs &&
        terminal.committedJournal.logList == failedInitializerLogs &&
        terminal.workingJournal.createdContractList == [] &&
        terminal.committedJournal.createdContractList == [] &&
        terminal.finalWorld.nonce? creator == some oldNonce &&
        terminal.finalWorld.balance? creator ==
          some insufficientCreatorBalance &&
        (terminal.finalWorld.account? created).isNone

private theorem compileTimeCreationJournals :
    successfulCreationJournals && revertedInitializerRollsBack &&
      trappedInitializerRollsBack && laterRootRevertRollsBack &&
      laterRootTrapRollsBack = true := by
  native_decide

private theorem compileTimeCreationResumption :
    everyOutOfFuelBoundaryIsExactlyOnce && criticalBoundariesAreVisible = true := by
  native_decide

private theorem compileTimeSequentialCreationOrder :
    sequentialCreationsPreserveCompletionOrder = true := by
  native_decide

private theorem compileTimePreflightJournalIdentity :
    checkedPreflightFailuresLeaveJournalIdentity &&
      insufficientBalanceLeavesJournalIdentity = true := by
  native_decide

def testAdr0149CreationLogExecution : IO Unit := do
  assertTrue successfulCreationJournals
    "initializer logs or the successful creation observation were not committed"
  assertTrue revertedInitializerRollsBack
    "initializer revert retained logs or a successful-creation observation"
  assertTrue trappedInitializerRollsBack
    "initializer trap retained logs or a successful-creation observation"
  assertTrue laterRootRevertRollsBack
    "root revert committed speculative initializer observations"
  assertTrue laterRootTrapRollsBack
    "root trap committed speculative initializer observations"
  assertTrue everyOutOfFuelBoundaryIsExactlyOnce
    "creation resumption duplicated, lost, or reordered transaction observations"
  assertTrue criticalBoundariesAreVisible
    "initializer/completion boundaries did not expose their retained journal"
  assertTrue sequentialCreationsPreserveCompletionOrder
    "sequential creations lost completion-order logs or created addresses"
  assertTrue checkedPreflightFailuresLeaveJournalIdentity
    "a checked creation preflight failure changed transaction observations"
  assertTrue insufficientBalanceLeavesJournalIdentity
    "insufficient creation balance changed journal, nonce, or world state"

end Tests
end

section
-- leanmerge: from Solcore.Test.Adr0149NestedLogExecution
/-! Runtime regressions for nested transaction-log ordering and rollback. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open Adr0149NestedLogExecutionFixture

private def returnedChild : CheckedCoreWordOutcome :=
  .returned returnPayload

private def revertedChild : CheckedCoreWordOutcome :=
  .reverted revertPayload

private def trappedChild : CheckedCoreWordOutcome :=
  .trapped trapReason

private def allLogs : List CheckedCoreWordLog :=
  [rootBeforeLog, childLog, rootAfterLog]

private def parentOnlyLogs : List CheckedCoreWordLog :=
  [rootBeforeLog, rootAfterLog]

private def logsMatch
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : OneLevelNestedExecution.Result
      initialWorld rootContract rootInvocation)
    (outcome : FrameOutcome Word)
    (working committed : List CheckedCoreWordLog) : Bool :=
  match result.view with
  | .completed terminal =>
      terminal.outcome == outcome &&
        terminal.workingJournal.logList == working &&
        terminal.committedJournal.logList == committed
  | .outOfFuel _ _ _ => false

private def parentChildParentOrder : Bool :=
  logsMatch
    (runScenario .returned returnedChild completionFuel)
    (.returned (encodeWordBytesBE returnPayload)) allLogs allLogs

private def revertedChildLogsRollBack : Bool :=
  logsMatch
    (runScenario .returned revertedChild completionFuel)
    (.returned (encodeWordBytesBE returnPayload))
    parentOnlyLogs parentOnlyLogs

private def trappedChildLogsRollBack : Bool :=
  logsMatch
    (runScenario .returned trappedChild completionFuel)
    (.returned (encodeWordBytesBE returnPayload))
    parentOnlyLogs parentOnlyLogs

private def laterRootRevertRollsBackAllLogs : Bool :=
  logsMatch
    (runScenario .reverted returnedChild completionFuel)
    (.reverted (encodeWordBytesBE revertPayload))
    allLogs []

private def laterRootTrapRollsBackAllLogs : Bool :=
  logsMatch
    (runScenario .trapped returnedChild completionFuel)
    (.trapped trapReason) allLogs []

private def retainedLogs
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation} :
    OneLevelNestedExecution.Mode
      initialWorld rootContract rootInvocation →
      List CheckedCoreWordLog
  | .root frame => frame.context.workingJournal.logList
  | .child frame => frame.childContext.workingJournal.logList
  | .initializer frame => frame.initializerContext.workingJournal.logList

private def isExpectedPrefix (logs : List CheckedCoreWordLog) : Bool :=
  allLogs.take logs.length == logs

private def resumedLogsExact (prefixFuel : Nat) : Bool :=
  let prefixResult := runScenario .returned returnedChild prefixFuel
  match prefixResult.view with
  | .completed terminal =>
      terminal.workingJournal.logList == allLogs &&
        terminal.committedJournal.logList == allLogs
  | .outOfFuel _ mode _ =>
      isExpectedPrefix (retainedLogs mode) &&
        logsMatch
          (OneLevelNestedExecution.resumeWithFuel prefixResult completionFuel)
          (.returned (encodeWordBytesBE returnPayload)) allLogs allLogs

private def everyOutOfFuelBoundaryIsExactlyOnce_variant : Bool :=
  (List.range 160).all resumedLogsExact

private def childOutOfFuelAfterItsLog (fuel : Nat) : Bool :=
  match (runScenario .returned returnedChild fuel).view with
  | .outOfFuel _ (.child frame) _ =>
      frame.childContext.workingJournal.logList ==
        [rootBeforeLog, childLog]
  | _ => false

private def loggedChildOutOfFuelIsVisible : Bool :=
  (List.range 160).any childOutOfFuelAfterItsLog

private theorem compileTimeParentChildParentOrder :
    parentChildParentOrder = true := by
  native_decide

private theorem compileTimeRevertedChildRollback :
    revertedChildLogsRollBack = true := by
  native_decide

private theorem compileTimeTrappedChildRollback :
    trappedChildLogsRollBack = true := by
  native_decide

private theorem compileTimeLaterRootRevertRollback :
    laterRootRevertRollsBackAllLogs = true := by
  native_decide

private theorem compileTimeLaterRootTrapRollback :
    laterRootTrapRollsBackAllLogs = true := by
  native_decide

private theorem compileTimeEveryOutOfFuelBoundaryExactlyOnce :
    everyOutOfFuelBoundaryIsExactlyOnce_variant = true := by
  native_decide

private theorem compileTimeLoggedChildOutOfFuelVisible :
    loggedChildOutOfFuelIsVisible = true := by
  native_decide

def testAdr0149NestedLogExecution : IO Unit := do
  assertTrue parentChildParentOrder
    "root/child/root logs were not preserved in chronological order"
  assertTrue revertedChildLogsRollBack
    "a reverted child's log survived its call checkpoint"
  assertTrue trappedChildLogsRollBack
    "a trapped child's log survived its call checkpoint"
  assertTrue laterRootRevertRollsBackAllLogs
    "root revert committed speculative parent and child logs"
  assertTrue laterRootTrapRollsBackAllLogs
    "root trap committed speculative parent and child logs"
  assertTrue everyOutOfFuelBoundaryIsExactlyOnce_variant
    "resumption duplicated, lost, or reordered a retained log prefix"
  assertTrue loggedChildOutOfFuelIsVisible
    "no retained child state exposed its already-recorded log"

end Tests
end

section
-- leanmerge: from Solcore.Test.Adr0149TopLevelLogs
/-! Executable root commit/rollback and resumption tests for ADR-0149 logs. -/

set_option autoImplicit false

namespace Tests.Adr0149TopLevelLogs

open Solcore.Core
open Solcore.ContractRuntime
open Adr0149TopLevelLogsFixture

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def assertExactWorkingLogs
    (result : TopLevelTerminalResult initialWorld targetAddress)
    (message : String) : IO Unit := do
  assertTrue (result.workingJournal.logList == expectedLogs) message
  assertTrue
    (result.terminalContext.workingJournal.logList == expectedLogs)
    "terminal context and exposed speculative logs must agree exactly"
  assertTrue (result.workingJournal.createdContractList == [])
    "word-log execution must not invent contract-creation observations"
  assertTrue
    (result.workingJournal.logList.length == 2 && firstLog == secondLog)
    "two identical emissions must remain two ordered journal entries"

private def testReturnedLogs : IO Unit := do
  match runWith returnSelector 256 with
  | .outOfFuel _ _ _ _ _ _ =>
      throw (IO.userError "returning log program must complete")
  | .completed result =>
      assertTrue
        (result.outcome == .returned (encodeWordBytesBE returnPayload))
        "returning log program produced the wrong root outcome"
      assertExactWorkingLogs result
        "return must expose emitter/topic/payload in chronological order"
      assertTrue (result.committedJournal.logList == expectedLogs)
        "return must commit both emitted logs in exact order"

private def testRevertedLogs : IO Unit := do
  match runWith revertSelector 256 with
  | .outOfFuel _ _ _ _ _ _ =>
      throw (IO.userError "reverting log program must complete")
  | .completed result =>
      assertTrue
        (result.outcome == .reverted (encodeWordBytesBE revertPayload))
        "reverting log program produced the wrong root outcome"
      assertExactWorkingLogs result
        "revert must retain the exact speculative log sequence"
      assertTrue (result.committedJournal.logList == [])
        "revert must select the empty root checkpoint journal"

private def testTrappedLogs : IO Unit := do
  match runWith trapSelector 256 with
  | .outOfFuel _ _ _ _ _ _ =>
      throw (IO.userError "trapping log program must complete")
  | .completed result =>
      assertTrue (result.outcome == .trapped trapReason)
        "trapping log program produced the wrong root outcome"
      assertExactWorkingLogs result
        "trap must retain the exact speculative log sequence"
      assertTrue (result.committedJournal.logList == [])
        "trap must select the empty root checkpoint journal"

private def legacyFuel : Nat := 256
private def resumedFuel : Nat := 37

private def sameJournal
    (left right : TransactionJournal) : Bool :=
  left.logList == right.logList &&
    left.createdContractList == right.createdContractList

private def testLegacyLogIsExplicitlyUnsupported : IO Unit := do
  let initialContext := TopLevelExecution.initialTransactionContext installed
  let inputs := (invocationWith returnSelector).executionInputs
  let initialState := State.initial code.program.body hostEnvironment
  let coreResult := hostRun legacyFuel initialState
  let legacyResult := code.runWithStorage initialContext inputs legacyFuel
  match coreResult, legacyResult with
  | .suspended emitted emittedRemainingFuel,
      ⟨rejectedContext, .unsupported rejected rejectedRemainingFuel⟩ =>
      assertTrue (emitted == rejected)
        "legacy rejection must preserve the exact Core suspension"
      assertTrue (rejected.request == .emitLogWord firstTopic firstPayload)
        "legacy rejection must expose the exact log request"
      assertTrue (emittedRemainingFuel == rejectedRemainingFuel)
        "legacy rejection must preserve Core's remaining fuel"
      assertTrue
        (rejectedContext.context.storageAddress ==
          initialContext.context.storageAddress)
        "legacy rejection must preserve the selected storage address"
      assertTrue
        (sameJournal
          (TransactionHostStorageDriver.Context.workingJournal rejectedContext)
          initialContext.workingJournal)
        "legacy rejection must leave the working journal unchanged"
      assertTrue
        (sameJournal
          rejectedContext.context.values.checkpoint.effects.rollback
          initialContext.context.values.checkpoint.effects.rollback)
        "legacy rejection must leave the checkpoint journal unchanged"
      let resumed := legacyResult.resumeWithFuel
        (TransactionHostStorageDriver.handler inputs) resumedFuel
      match resumed with
      | ⟨resumedContext,
          .unsupported resumedSuspension resumedRemainingFuel⟩ =>
          assertTrue (resumedSuspension == rejected)
            "resumption must retain the unsupported suspension"
          assertTrue
            (resumedRemainingFuel == rejectedRemainingFuel + resumedFuel)
            "resumption must retain and extend the unused fuel exactly"
          assertTrue
            (sameJournal
              (TransactionHostStorageDriver.Context.workingJournal
                resumedContext)
              initialContext.workingJournal)
            "resumption must not invoke even a log-capable handler"
      | _ =>
          throw (IO.userError
            "resumption must not cross an unsupported legacy boundary")
  | _, _ =>
      throw (IO.userError
        "legacy checked execution must stop explicitly at its first log")

private def testSameCodeRecordsLogsTransactionally : IO Unit := do
  let initialContext := TopLevelExecution.initialTransactionContext installed
  let inputs := (invocationWith returnSelector).executionInputs
  match code.runWithTransactionStorage initialContext inputs legacyFuel with
  | ⟨finalContext, .done _ _⟩ =>
      assertTrue (finalContext.workingJournal.logList == expectedLogs)
        "transaction execution must record every log from the same code"
  | _ =>
      throw (IO.userError
        "transaction execution of the checked log program must complete")

/-- Find a genuine exhaustion point after exactly the first log was handled. -/
private def findOneLogSplit : Nat → Nat → Option Nat
  | _, 0 => none
  | fuel, remaining + 1 =>
      match runWith returnSelector fuel with
      | .completed _ => none
      | .outOfFuel context _ _ _ _ _ =>
          if context.workingJournal.logList == [firstLog]
            then some fuel
            else findOneLogSplit (fuel + 1) remaining

private def testOutOfFuelExactlyOnce : IO Unit := do
  let splitFuel ←
    match findOneLogSplit 0 256 with
    | some fuel => pure fuel
    | none =>
        throw (IO.userError
          "no exhausted boundary retained exactly the first emitted log")
  let prefixRun := runWith returnSelector splitFuel
  match prefixRun with
  | .completed _ =>
      throw (IO.userError "selected log split must remain exhausted")
  | .outOfFuel context _ _ _ _ _ =>
      assertTrue (context.workingJournal.logList == [firstLog])
        "exhausted context must retain the first log exactly once"
      match TopLevelExecution.resumeWithFuel prefixRun 256 with
      | .outOfFuel _ _ _ _ _ _ =>
          throw (IO.userError "resumed log program must complete")
      | .completed resumed =>
          assertTrue (resumed.workingJournal.logList == expectedLogs)
            "resumption must append only the second log without replay"
          assertTrue (resumed.committedJournal.logList == expectedLogs)
            "resumed return must commit the exact once-only log sequence"
          match runWith returnSelector 256 with
          | .outOfFuel _ _ _ _ _ _ =>
              throw (IO.userError "one-shot comparison must complete")
          | .completed oneShot =>
              assertTrue
                (resumed.outcome == oneShot.outcome &&
                  resumed.workingJournal.logList ==
                    oneShot.workingJournal.logList &&
                  resumed.committedJournal.logList ==
                    oneShot.committedJournal.logList)
                "split and one-shot log executions must be observationally exact"

def testAdr0149TopLevelLogs : IO Unit := do
  testLegacyLogIsExplicitlyUnsupported
  testSameCodeRecordsLogsTransactionally
  testReturnedLogs
  testRevertedLogs
  testTrappedLogs
  testOutOfFuelExactlyOnce

end Tests.Adr0149TopLevelLogs
end
