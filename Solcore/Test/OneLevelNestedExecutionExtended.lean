import Solcore.ContractRuntime.WorldStateDeltaProperties
import Solcore.Test.OneLevelNestedExecutionFixture

/-! Extended executable regressions for the depth-one nested scheduler. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open OneLevelNestedExecutionFixture

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def completionFuel : Nat := 768
private def one : Word := ⟨1, by decide⟩
private def two : Word := ⟨2, by decide⟩
private def sequentialSlot : Word := ⟨0x91, by decide⟩
private def selfLeafPayload : Word := ⟨0x92, by decide⟩
private def selfWrittenValue : Word := ⟨0x93, by decide⟩
private def rootWrittenValue : Word := ⟨0x94, by decide⟩
private def untouchedAddress : Address := ⟨0x99, by decide⟩
private def untouchedSlot : Word := ⟨0x9a, by decide⟩

/-!
The same code runs as root and child. The root receives `returned` and reads
the slot. Its child receives the depth-limit `failed` branch, writes the slot,
and returns. The root read therefore observes whether self-call rebasing
refreshed the cached storage Account.
-/
private def consumeSelfCall (call : Expr) : Expr :=
  .caseE call
    (returnedExpr
      (.apply (.var (HostFunction.storageRead.index + 1))
        (.word rootSlot)))
    (.caseE (.var 0)
      (revertedExpr (.var 0))
      (.caseE (.var 0)
        (trappedExpr (.var 0))
        (.letE
          (.apply (.var (HostFunction.storageWrite.index + 3))
            (.pair (.word rootSlot) (.word selfWrittenValue)))
          (returnedExpr (.word selfLeafPayload)))))

private def selfCallProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body := consumeSelfCall
    (.apply (.var HostFunction.callContractWord.index)
      (.pair (.word rootTargetWord) (.word callInput)))
}

private theorem selfCallProgram_checked :
    selfCallProgram.checkHost = true := by
  decide

private def selfCallContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨selfCallProgram, selfCallProgram_checked⟩ rfl

private def selfCallRebasesStorage : Bool :=
  match (runScenario selfCallContract selfCallContract completionFuel).view with
  | .completed terminal =>
      terminal.outcome ==
          FrameOutcome.returned (encodeWordBytesBE selfWrittenValue) &&
        rootStorageValue?
          terminal.terminalContext.context.values.working.1 ==
            some selfWrittenValue &&
        rootStorageValue? terminal.finalWorld == some selfWrittenValue
  | .outOfFuel _ _ _ => false

private theorem compileTimeSelfCallRebase :
    selfCallRebasesStorage = true := by
  native_decide

/-! One leaf call increments a persistent slot and returns its new value. -/
private def incrementChildProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE
      (.apply (.var HostFunction.storageRead.index)
        (.word sequentialSlot))
      (.letE
        (.apply (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word sequentialSlot)
            (.binary .wordAdd (.var 0) (.word one))))
        (returnedExpr (.binary .wordAdd (.var 1) (.word one))))
}

private theorem incrementChildProgram_checked :
    incrementChildProgram.checkHost = true := by
  decide

private def incrementChildContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨incrementChildProgram, incrementChildProgram_checked⟩ rfl

/-! Ignore the first typed result, then issue a second call in sequence. -/
private def sequentialRootProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE
      (.apply (.var HostFunction.callContractWord.index)
        (.pair (.word childTargetWord) (.word callInput)))
      (consumeCallResult .commit
        (.apply (.var (HostFunction.callContractWord.index + 1))
          (.pair (.word childTargetWord) (.word callInput))))
}

private theorem sequentialRootProgram_checked :
    sequentialRootProgram.checkHost = true := by
  decide

private def sequentialRootContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨sequentialRootProgram, sequentialRootProgram_checked⟩ rfl

private def sequentialCallsShareWorkingWorld : Bool :=
  match (runScenario sequentialRootContract incrementChildContract
      completionFuel).view with
  | .completed terminal =>
      terminal.outcome == FrameOutcome.returned (encodeWordBytesBE two) &&
        terminal.finalWorld.readStorage? childAddress sequentialSlot ==
          some two &&
        terminal.committedDelta.storageEndpoints childAddress sequentialSlot ==
          (some Word.zero, some two)
  | .outOfFuel _ _ _ => false

private theorem compileTimeSequentialCalls :
    sequentialCallsShareWorkingWorld = true := by
  native_decide

/-! The registry advertises code different from the code installed in world. -/
private def mismatchRootContract : CheckedCoreContract :=
  rootContract .commit childTargetWord

private def mismatchWorld : WorldState :=
  initialWorld mismatchRootContract childReturnContract

private def mismatchRegistry : CheckedContractRegistry := {
  lookup := fun address =>
    if address = rootAddress then some mismatchRootContract
    else if address = childAddress then some childRevertContract
    else none
}

private def mismatchRun :
    OneLevelNestedExecution.Result mismatchWorld mismatchRootContract invocation :=
  OneLevelNestedExecution.run mismatchRootContract invocation
    (installedRoot mismatchRootContract childReturnContract)
    mismatchRegistry completionFuel

private def registryCodeMismatchFails : Bool :=
  (mismatchRegistry.resolve? mismatchWorld childAddress).isNone &&
    match mismatchRun.view with
    | .completed terminal =>
        terminal.outcome ==
            FrameOutcome.trapped ContractCallFailure.unavailable.code &&
          childStorageValue? terminal.finalWorld == some childOldValue
    | .outOfFuel _ _ _ => false

private theorem compileTimeRegistryCodeMismatch :
    registryCodeMismatchFails = true := by
  native_decide

private def missingAccountRoot : CheckedCoreContract :=
  rootContract .commit unavailableTargetWord

private def missingAccountRegistry : CheckedContractRegistry := {
  lookup := fun address =>
    if address = rootAddress then some missingAccountRoot
    else if address = unavailableAddress then some childReturnContract
    else none
}

private def missingAccountRun :=
  OneLevelNestedExecution.run missingAccountRoot invocation
    (installedRoot missingAccountRoot childReturnContract)
    missingAccountRegistry completionFuel

private def registeredMissingAccountFails : Bool :=
  match missingAccountRun.view with
  | .completed terminal =>
      terminal.outcome ==
        FrameOutcome.trapped ContractCallFailure.unavailable.code
  | .outOfFuel _ _ _ => false

private theorem compileTimeRegisteredMissingAccount :
    registeredMissingAccountFails = true := by
  native_decide

private def missingCodeRoot : CheckedCoreContract :=
  rootContract .commit childTargetWord

private def missingCodeWorld : WorldState :=
  WorldState.empty
    |>.putAccount rootAddress (rootAccount missingCodeRoot)
    |>.putAccount childAddress Account.empty

private def missingCodeInstalled :
    InstalledCheckedCoreContract missingCodeWorld rootAddress missingCodeRoot := {
  account := rootAccount missingCodeRoot
  account_present := by rfl
  code_present := by rfl
}

private def missingCodeRun :=
  OneLevelNestedExecution.run missingCodeRoot invocation missingCodeInstalled
    (registry missingCodeRoot childReturnContract) completionFuel

private def registeredMissingCodeFails : Bool :=
  match missingCodeRun.view with
  | .completed terminal =>
      terminal.outcome ==
        FrameOutcome.trapped ContractCallFailure.unavailable.code
  | .outOfFuel _ _ _ => false

private theorem compileTimeRegisteredMissingCode :
    registeredMissingCodeFails = true := by
  native_decide

/-! Write root storage, commit a child write speculatively, then root-revert. -/
private def rollbackRootProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE
      (.apply (.var HostFunction.storageWrite.index)
        (.pair (.word rootSlot) (.word rootWrittenValue)))
      (consumeCallResult .revert
        (.apply (.var (HostFunction.callContractWord.index + 1))
          (.pair (.word childTargetWord) (.word callInput))))
}

private theorem rollbackRootProgram_checked :
    rollbackRootProgram.checkHost = true := by
  decide

private def rollbackRootContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨rollbackRootProgram, rollbackRootProgram_checked⟩ rfl

private def rollbackDeltaQueriesExact : Bool :=
  match (runScenario rollbackRootContract childReturnContract completionFuel).view with
  | .completed terminal =>
      terminal.outcome ==
          FrameOutcome.reverted (encodeWordBytesBE rootRevertPayload) &&
        terminal.workingDelta.storageEndpoints rootAddress rootSlot ==
          (some Word.zero, some rootWrittenValue) &&
        terminal.workingDelta.slotChange? rootAddress rootSlot ==
          some (some Word.zero, some rootWrittenValue) &&
        terminal.workingDelta.storageEndpoints childAddress childSlot ==
          (some childOldValue, some childNewValue) &&
        terminal.workingDelta.slotChange? childAddress childSlot ==
          some (some childOldValue, some childNewValue) &&
        terminal.workingDelta.storageEndpoints untouchedAddress untouchedSlot ==
          (none, none) &&
        terminal.workingDelta.slotChange? untouchedAddress untouchedSlot == none &&
        terminal.committedDelta.storageEndpoints rootAddress rootSlot ==
          (some Word.zero, some Word.zero) &&
        terminal.committedDelta.slotChange? rootAddress rootSlot == none &&
        terminal.committedDelta.storageEndpoints childAddress childSlot ==
          (some childOldValue, some childOldValue) &&
        terminal.committedDelta.slotChange? childAddress childSlot == none &&
        terminal.committedDelta.storageEndpoints untouchedAddress untouchedSlot ==
          (none, none) &&
        terminal.committedDelta.slotChange? untouchedAddress untouchedSlot == none
  | .outOfFuel _ _ _ => false

private theorem compileTimeRollbackDeltaQueries :
    rollbackDeltaQueriesExact = true := by
  native_decide

/-- Runtime counterparts for all extended nested-execution regressions. -/
def testOneLevelNestedExecutionExtended : IO Unit := do
  assertTrue selfCallRebasesStorage
    "self-call return did not refresh the root storage Account"
  assertTrue sequentialCallsShareWorkingWorld
    "sequential child calls did not share the committed working world"
  assertTrue registryCodeMismatchFails
    "registry/world code mismatch did not produce unavailable"
  assertTrue registeredMissingAccountFails
    "registered target with no Account did not produce unavailable"
  assertTrue registeredMissingCodeFails
    "registered Account with no code did not produce unavailable"
  assertTrue rollbackDeltaQueriesExact
    "root rollback did not expose exact root/child/untouched delta queries"

end Tests
