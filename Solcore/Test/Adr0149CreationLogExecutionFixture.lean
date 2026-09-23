import Solcore.ContractRuntime.OneLevelNestedExecution
import Solcore.Test.Adr0148CreationEndToEndFixture

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
