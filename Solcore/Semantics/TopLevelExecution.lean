import Solcore.Semantics.TopLevelExecutionContextProperties
import Solcore.Semantics.TopLevelExecutionResult
import Solcore.Semantics.TransactionHostStorageDriverProperties

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
    HostDriverResult TransactionHostStorageDriver.Context :=
  contract.code.runWithTransactionStorage
    (initialTransactionContext installed) invocation.executionInputs fuel

/-- Build the speculative delta from the already evaluated raw run. -/
def workingDeltaOfRawRun
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel : Nat)
    (result : HostDriverResult TransactionHostStorageDriver.Context)
    (result_eq : rawRun contract invocation installed fuel = result) :
    TopLevelStorageDelta initialWorld
      result.context.context.values.working.1
      invocation.target := {
  initialAccount := installed.account
  finalAccount := result.context.storageAccount
  initialAccount_present := installed.account_present
  finalAccount_present := by
    subst result
    simpa [rawRun, CheckedHostCoreProgram.runWithTransactionStorage] using
      (rawRun contract invocation installed fuel).context.storageAccount_present
  code_preserved := by
    subst result
    have finalPresent :
        (rawRun contract invocation installed fuel).context.context.values.working.1.account?
            invocation.target =
          some (rawRun contract invocation installed fuel).context.storageAccount := by
      simpa [rawRun, CheckedHostCoreProgram.runWithTransactionStorage] using
        (rawRun contract invocation installed fuel).context.storageAccount_present
    have preserved := TransactionHostStorageDriver.run_workingCode?
      (initialTransactionContext installed) invocation.executionInputs fuel
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
    subst result
    intro address different
    have preserved :=
      TransactionHostStorageDriver.run_workingAccount?_of_ne_storageAddress
      (initialTransactionContext installed) invocation.executionInputs fuel
      (Core.State.initial contract.code.program.body Core.hostEnvironment)
      address (by simpa using different)
    simpa [rawRun, CheckedHostCoreProgram.runWithTransactionStorage] using
      preserved
}

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
      invocation.target :=
  workingDeltaOfRawRun contract invocation installed fuel
    (rawRun contract invocation installed fuel) rfl

/-- A raw driver result together with all evidence needed for total decoding. -/
structure ValidatedRawResult
    (initialWorld : WorldState)
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation) where
  result : HostDriverResult TransactionHostStorageDriver.Context
  resultTyping :
    result.outcome.HasType contract.code.program.resultType
      contract.code.program.dataDefinitions
  storageAddress_eq :
    result.context.context.storageAddress = invocation.target
  workingDelta :
    TopLevelStorageDelta initialWorld
      result.context.context.values.working.1 invocation.target

/-- Package one initial raw run with its checked invariants and exact delta. -/
def validatedRawRun
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel : Nat) :
    ValidatedRawResult initialWorld contract invocation :=
  let result := rawRun contract invocation installed fuel
  have resultTyping :
      result.outcome.HasType contract.code.program.resultType
        contract.code.program.dataDefinitions := by
    exact contract.code.runWithTransactionStorage_hasType
      (initialTransactionContext installed) invocation.executionInputs fuel
  have storageAddress_eq :
      result.context.context.storageAddress = invocation.target := by
    have preserved := TransactionHostStorageDriver.run_storageAddress
      (initialTransactionContext installed) invocation.executionInputs fuel
      (Core.State.initial contract.code.program.body Core.hostEnvironment)
    change result.context.context.storageAddress = invocation.target at preserved
    exact preserved
  {
    result := result
    resultTyping := resultTyping
    storageAddress_eq := storageAddress_eq
    workingDelta :=
      workingDeltaOfRawRun contract invocation installed fuel result rfl
  }

/-- Select the committed or rolled-back world from a decoded terminal outcome. -/
def finalize
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : TransactionHostStorageDriver.Context)
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
      workingJournal := context.workingJournal
      committedJournal := context.workingJournal
      workingDelta := workingDelta
      committedDelta := workingDelta
    }
  | .reverted data => {
      terminalContext := context
      coreValue := value
      coreStore := store
      outcome := .reverted data
      finalWorld := initialWorld
      workingJournal := context.workingJournal
      committedJournal :=
        context.context.values.checkpoint.effects.rollback
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
      workingJournal := context.workingJournal
      committedJournal :=
        context.context.values.checkpoint.effects.rollback
      workingDelta := workingDelta
      committedDelta :=
        TopLevelStorageDelta.identity initialWorld invocation.target
          installedAccount installedAccount_present
    }

/-- Classify one typed raw result with its exact root-relative working delta. -/
def classifyRawResult
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (raw : ValidatedRawResult initialWorld contract invocation) :
    TopLevelRunResult initialWorld contract invocation :=
  match outcomeEq : raw.result.outcome with
  | .done value store =>
      have decodedNeNone :
          contract.decodeCompletion? value ≠ none := by
        have resultTyping := raw.resultTyping
        rw [outcomeEq] at resultTyping
        obtain ⟨world, _storeTyping, valueTyping⟩ := resultTyping
        apply contract.entryProfile.decode?_ne_none_of_hasType
        rw [← contract.resultType_eq]
        exact valueTyping
      match decodedEq : contract.decodeCompletion? value with
      | some outcome =>
          .completed
            (finalize invocation raw.workingDelta.initialAccount
              raw.workingDelta.initialAccount_present
              raw.result.context value store outcome
              raw.workingDelta)
      | none => False.elim (decodedNeNone decodedEq)
  | .outOfFuel state =>
      have stateTyping :
          Core.HostStateHasType state contract.code.program.resultType
            contract.code.program.dataDefinitions := by
        have resultTyping := raw.resultTyping
        rw [outcomeEq] at resultTyping
        exact resultTyping
      .outOfFuel raw.result.context state raw.storageAddress_eq stateTyping
        raw.workingDelta
  | .fault _error _state =>
      have impossible : False := by
        have resultTyping := raw.resultTyping
        rw [outcomeEq] at resultTyping
        exact resultTyping
      False.elim impossible

/-- Run one installed checked Core contract with a bounded fuel budget. -/
def run
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel : Nat) :
    TopLevelRunResult initialWorld contract invocation :=
  classifyRawResult contract invocation
    (validatedRawRun contract invocation installed fuel)

end TopLevelExecution

end Solcore.Semantics
