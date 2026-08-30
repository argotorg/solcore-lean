import Solcore.Semantics.HostStorageDriverProperties
import Solcore.Semantics.HostStorageDriverSafetyProperties
import Solcore.Semantics.TopLevelExecutionContextProperties
import Solcore.Semantics.TopLevelExecutionResult

/-! Executable checked-Core top-level run and terminal state selection. -/

set_option autoImplicit false

namespace Solcore.Semantics

namespace TopLevelExecution

/-- The exact checked storage run underlying one initial top-level invocation. -/
def rawRun
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel : Nat) :
    HostDriverResult (HostStorageDriver.Context Unit Unit) :=
  contract.code.runWithStorage
    (initialContext installed) invocation.executionInputs fuel

/-- Every initial run has an exact queryable delta for its speculative world. -/
def workingDelta
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel : Nat) :
    TopLevelStorageDelta initialWorld
      (rawRun contract invocation installed fuel).context.context.values.working.1
      invocation.target := {
  initialAccount := installed.account
  finalAccount :=
    (rawRun contract invocation installed fuel).context.storageAccount
  initialAccount_present := installed.account_present
  finalAccount_present := by
    simpa [rawRun, CheckedHostCoreProgram.runWithStorage] using
      (rawRun contract invocation installed fuel).context.storageAccount_present
  code_preserved := by
    have finalPresent :
        (rawRun contract invocation installed fuel).context.context.values.working.1.account?
            invocation.target =
          some (rawRun contract invocation installed fuel).context.storageAccount := by
      simpa [rawRun, CheckedHostCoreProgram.runWithStorage] using
        (rawRun contract invocation installed fuel).context.storageAccount_present
    have preserved := HostStorageDriver.run_workingCode?
      (initialContext installed) invocation.executionInputs fuel
      (Core.State.initial contract.code.program.body Core.hostEnvironment)
      invocation.target
    change
      (rawRun contract invocation installed fuel).context.context.values.working.1.code?
          invocation.target =
        initialWorld.code? invocation.target at preserved
    have preserved' := preserved
    simp [WorldState.code?, finalPresent, installed.account_present] at preserved'
    exact preserved'
  otherAccounts_preserved := by
    intro address different
    have preserved := HostStorageDriver.run_workingAccount?_of_ne_storageAddress
      (initialContext installed) invocation.executionInputs fuel
      (Core.State.initial contract.code.program.body Core.hostEnvironment)
      address (by simpa using different)
    simpa [rawRun, CheckedHostCoreProgram.runWithStorage] using preserved
}

/-- Select the committed or rolled-back world from a decoded terminal outcome. -/
def finalize
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : HostStorageDriver.Context Unit Unit)
    (value : Core.Value)
    (store : Core.Store)
    (outcome : FrameOutcome Core.Word)
    (workingDelta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target) :
    TopLevelTerminalResult initialWorld invocation.target :=
  match outcome with
  | .returned data => {
      terminalContext := context
      coreValue := value
      coreStore := store
      outcome := .returned data
      finalWorld := context.context.values.working.1
      workingDelta := workingDelta
      committedDelta := workingDelta
    }
  | .reverted data => {
      terminalContext := context
      coreValue := value
      coreStore := store
      outcome := .reverted data
      finalWorld := initialWorld
      workingDelta := workingDelta
      committedDelta :=
        TopLevelStorageDelta.identity initialWorld invocation.target
          installedAccount installedAccount_present
    }
  | .trapped reason => {
      terminalContext := context
      coreValue := value
      coreStore := store
      outcome := .trapped reason
      finalWorld := initialWorld
      workingDelta := workingDelta
      committedDelta :=
        TopLevelStorageDelta.identity initialWorld invocation.target
          installedAccount installedAccount_present
    }

/-- Run one installed checked Core contract with a bounded fuel budget. -/
def run
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel : Nat) :
    TopLevelRunResult initialWorld contract invocation :=
  let result := rawRun contract invocation installed fuel
  match outcomeEq : result.outcome with
  | .done value store =>
      have typed := contract.code.runWithStorage_done_hasType
        (initialContext installed) invocation.executionInputs (by
          simpa [result, rawRun] using outcomeEq)
      have decodedNeNone :
          contract.entryProfile.decode? value ≠ none := by
        obtain ⟨world, _storeTyping, valueTyping⟩ := typed
        apply contract.entryProfile.decode?_ne_none_of_hasType
        rw [← contract.resultType_eq]
        exact valueTyping
      match decodedEq : contract.entryProfile.decode? value with
      | some outcome =>
          .completed
            (finalize invocation installed.account installed.account_present
              result.context value store outcome
              (workingDelta contract invocation installed fuel))
      | none => False.elim (decodedNeNone decodedEq)
  | .outOfFuel state =>
      have stateTyping := contract.code.runWithStorage_outOfFuel_hasType
        (initialContext installed) invocation.executionInputs (by
          simpa [result, rawRun] using outcomeEq)
      .outOfFuel result.context state stateTyping
        (workingDelta contract invocation installed fuel)
  | .fault error state =>
      False.elim
        (contract.code.runWithStorage_ne_fault
          (initialContext installed) invocation.executionInputs fuel error state
          (by simpa [result, rawRun] using outcomeEq))

end TopLevelExecution

end Solcore.Semantics
