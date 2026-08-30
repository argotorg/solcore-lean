import Solcore.Semantics.OneLevelNestedExecutionResumption
import Solcore.Test.Adr0148CreationEndToEndFixture

/-! Checked creation programs with logs on both sides of the initializer. -/

set_option autoImplicit false

namespace Tests.Adr0149CreationLogExecutionFixture

open Solcore.Core
open Solcore.Semantics
open Solcore.Semantics.OneLevelNestedExecution
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

def successfulLogs : List CheckedCoreWordLog :=
  [rootLogBefore, initializerLogFirst, initializerLogSecond, rootLogAfter]

def failedInitializerLogs : List CheckedCoreWordLog :=
  [rootLogBefore, rootLogAfter]

end Tests.Adr0149CreationLogExecutionFixture
