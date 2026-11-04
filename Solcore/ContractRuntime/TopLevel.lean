import Solcore.ContractRuntime.RuntimeScalars
import Solcore.ContractRuntime.WorldState
import Solcore.Core.Syntax
import Solcore.ContractRuntime.Frames
import Solcore.ContractRuntime.Transactions
import Solcore.ContractRuntime.StorageDriver
import Solcore.ContractRuntime.Contracts
import Solcore.Core.HostTyping
import Solcore.Core.Machine
import Solcore.ContractRuntime.Driver
import Solcore.ContractRuntime.Internal.TransactionLaws
import Solcore.Core.Host
import Solcore.Core.HostMachine
import Solcore.Core.LanguageResult
import Solcore.Core.Data
import Solcore.Core.Typing

/-!
# Top-level execution

One checked invocation of an installed contract. `TopLevelExecution.rawRun` is the exact storage
run, `TopLevelExecution.finalize` selects the committed or rolled-back world, and
`TopLevelExecution.run` is the bounded run. `TopLevelRunResult` either completes with a
`TopLevelTerminalResult` or keeps the exact typed state, and `TopLevelExecution.resumeWithFuel`
continues from it. `TopLevelStorageDelta` queries what storage
changed. `CoreLanguageResult` reads Core language results at the contract boundary.

Main theorems: `TopLevelExecution.rawRun_ne_fault` says a checked run cannot fault.
`TopLevelExecution.resumeWithFuel_run`, `TopLevelExecution.resumeWithFuel_run_add` and
`TopLevelExecution.resumeWithFuel_run_zero` say resuming is one run with the summed budget.
`CoreLanguageResult.run_hasType` types the outcome.
-/

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsTopLevelStorageDelta
/-! Exact queryable target-storage change across top-level finalization. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/--
An exact single-Account storage delta. The delta is queried slot by slot;
`Account.storageEntries` enumerates either endpoint account's whole storage.
-/
structure TopLevelStorageDelta
    (initialWorld finalWorld : WorldState)
    (target : Address) where
  initialAccount : Account
  finalAccount : Account
  initialAccount_present :
    initialWorld.account? target = some initialAccount
  finalAccount_present :
    finalWorld.account? target = some finalAccount
  code_preserved : finalAccount.code? = initialAccount.code?
  otherAccounts_preserved :
    ∀ address, address ≠ target →
      finalWorld.account? address = initialWorld.account? address

namespace TopLevelStorageDelta

/-- Return exact old/new values only when the queried target slot changed. -/
def slotChange?
    {initialWorld finalWorld : WorldState}
    {target : Address}
    (delta : TopLevelStorageDelta initialWorld finalWorld target)
    (slot : Core.Word) : Option (Core.Word × Core.Word) :=
  let before := delta.initialAccount.storageRead slot
  let after := delta.finalAccount.storageRead slot
  if before = after then none else some (before, after)

/-- The identity finalization has an exact empty queryable delta. -/
def identity
    (world : WorldState)
    (target : Address)
    (account : Account)
    (present : world.account? target = some account) :
    TopLevelStorageDelta world world target := {
  initialAccount := account
  finalAccount := account
  initialAccount_present := present
  finalAccount_present := present
  code_preserved := rfl
  otherAccounts_preserved := by
    intro _ _
    rfl
}

end TopLevelStorageDelta

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.TopLevelStorageDeltaProperties`
-/

/-! Exact endpoint laws for queryable top-level storage deltas. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.TopLevelStorageDelta

/-- The endpoint worlds and target determine the storage-delta witness. -/
theorem unique
    {initialWorld finalWorld : WorldState}
    {target : Address}
    (left right : TopLevelStorageDelta initialWorld finalWorld target) :
    left = right := by
  have initialAccount_eq : left.initialAccount = right.initialAccount := by
    apply Option.some.inj
    exact left.initialAccount_present.symm.trans right.initialAccount_present
  have finalAccount_eq : left.finalAccount = right.finalAccount := by
    apply Option.some.inj
    exact left.finalAccount_present.symm.trans right.finalAccount_present
  cases left
  cases right
  simp_all

end Solcore.ContractRuntime.TopLevelStorageDelta
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsTopLevelExecution
/-! Root storage context derived from explicit top-level execution inputs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace TopLevelExecution

/-- Root execution currently has no separate rollback payload or event trace. -/
def initialEffects : FrameEffectJournal Unit Unit :=
  ⟨(), ()⟩

/-- Empty rollback-scoped observations for a direct transaction root. -/
def initialTransactionEffects :
    FrameEffectJournal TransactionJournal Unit :=
  ⟨TransactionJournal.empty, ()⟩

/-- Use the same explicit world and empty effects as checkpoint and working data. -/
def initialValues
    (initialWorld : WorldState) :
    FrameCheckpointedWorkingPair Unit Unit :=
  let working := (initialWorld, initialEffects)
  ⟨FrameCheckpointSnapshot.fromWorkingPair working, working⟩

/--
Pair an original transaction checkpoint with a separately prepared working
world. This is the root context shape used after a successful call-value
transfer: execution sees the transferred world, while rollback retains the
exact caller-supplied world.
-/
def preparedValues
    (checkpointWorld workingWorld : WorldState) :
    FrameCheckpointedWorkingPair Unit Unit :=
  let checkpoint :=
    FrameCheckpointSnapshot.fromWorkingPair
      (checkpointWorld, initialEffects)
  ⟨checkpoint, (workingWorld, initialEffects)⟩

/--
Pair explicit checkpoint and working worlds with their exact transaction
journals. This general constructor lets nested frames inherit observations
without weakening the empty-journal direct-root boundary.
-/
def preparedTransactionValuesWithJournals
    (checkpointWorld : WorldState)
    (checkpointJournal : TransactionJournal)
    (workingWorld : WorldState)
    (workingJournal : TransactionJournal) :
    FrameCheckpointedWorkingPair TransactionJournal Unit :=
  let checkpointEffects : FrameEffectJournal TransactionJournal Unit :=
    ⟨checkpointJournal, ()⟩
  let workingEffects : FrameEffectJournal TransactionJournal Unit :=
    ⟨workingJournal, ()⟩
  ⟨⟨checkpointWorld, checkpointEffects⟩, (workingWorld, workingEffects)⟩

/-- Direct transaction roots start with one empty checkpoint/working journal. -/
def initialTransactionValues
    (initialWorld : WorldState) :
    FrameCheckpointedWorkingPair TransactionJournal Unit :=
  preparedTransactionValuesWithJournals initialWorld TransactionJournal.empty
    initialWorld TransactionJournal.empty

/--
Prepare a direct transaction root after preflight while retaining the original
world and empty transaction observations as its rollback checkpoint.
-/
def preparedTransactionValues
    (checkpointWorld workingWorld : WorldState) :
    FrameCheckpointedWorkingPair TransactionJournal Unit :=
  preparedTransactionValuesWithJournals checkpointWorld
    TransactionJournal.empty workingWorld TransactionJournal.empty

/-- Build the exact root storage context certified by contract installation. -/
def initialContext
    {initialWorld : WorldState}
    {target : Address}
    {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract initialWorld target contract) :
    HostStorageDriver.Context Unit Unit := {
  context := {
    storageAddress := target
    values := initialValues initialWorld
  }
  storageAccount := installed.account
  storageAccount_present := installed.account_present
}

/-- Build a root context with distinct checkpoint and working worlds. -/
def preparedContext
    {checkpointWorld workingWorld : WorldState}
    {target : Address}
    {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    HostStorageDriver.Context Unit Unit := {
  context := {
    storageAddress := target
    values := preparedValues checkpointWorld workingWorld
  }
  storageAccount := installed.account
  storageAccount_present := installed.account_present
}

/-- Build the observable direct-root context certified by installation. -/
def initialTransactionContext
    {initialWorld : WorldState}
    {target : Address}
    {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract initialWorld target contract) :
    TransactionHostStorageDriver.Context := {
  context := {
    storageAddress := target
    values := initialTransactionValues initialWorld
  }
  storageAccount := installed.account
  storageAccount_present := installed.account_present
}

/-- Build an observable prepared root with empty transaction observations. -/
def preparedTransactionContext
    {checkpointWorld workingWorld : WorldState}
    {target : Address}
    {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    TransactionHostStorageDriver.Context := {
  context := {
    storageAddress := target
    values := preparedTransactionValues checkpointWorld workingWorld
  }
  storageAccount := installed.account
  storageAccount_present := installed.account_present
}

/--
Build an observable prepared context carrying caller-selected checkpoint and
working journals. Nested schedulers use this boundary to preserve log order.
-/
def preparedTransactionContextWithJournals
    {checkpointWorld workingWorld : WorldState}
    {target : Address}
    {contract : CheckedCoreContract}
    (checkpointJournal workingJournal : TransactionJournal)
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    TransactionHostStorageDriver.Context := {
  context := {
    storageAddress := target
    values := preparedTransactionValuesWithJournals checkpointWorld
      checkpointJournal workingWorld workingJournal
  }
  storageAccount := installed.account
  storageAccount_present := installed.account_present
}

end TopLevelExecution

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.TopLevelExecutionContextProperties`
-/

/-! Exact projections from the root top-level context and direct-call input. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace TopLevelExecution

@[simp] theorem initialTransactionContext_storageAddress
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialTransactionContext installed).context.storageAddress = target := by
  rfl

@[simp] theorem initialTransactionContext_workingState
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialTransactionContext installed).context.values.working.1 =
      initialWorld := by
  rfl

end TopLevelExecution

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.TopLevelExecutionResult`
-/

/-! Total results for one bounded checked-Core top-level execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- A terminal result after contract-owned decoding and root state selection. -/
structure TopLevelTerminalResult
    (initialWorld : WorldState)
    (target : Address) where
  terminalContext : TransactionHostStorageDriver.Context
  checkpointJournal_eq :
    terminalContext.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty
  coreValue : Core.Value
  coreStore : Core.Store
  outcome : FrameOutcome Core.Word
  finalWorld : WorldState
  /-- All rollback-scoped observations produced by speculative execution. -/
  workingJournal : TransactionJournal
  workingJournal_eq : workingJournal = terminalContext.workingJournal
  /-- Root-selected observations: committed on return, checkpoint on failure. -/
  committedJournal : TransactionJournal
  committedJournal_eq :
    committedJournal =
      match outcome with
      | .returned _ => terminalContext.workingJournal
      | .reverted _ =>
          terminalContext.context.values.checkpoint.effects.rollback
      | .trapped _ =>
          terminalContext.context.values.checkpoint.effects.rollback
  workingDelta :
    TopLevelStorageDelta initialWorld
      terminalContext.context.values.working.1 target
  committedDelta :
    TopLevelStorageDelta initialWorld finalWorld target

/--
One bounded run either completes or retains the exact typed machine state needed
to continue. Checked execution has no raw-fault constructor here.
-/
inductive TopLevelRunResult
    (initialWorld : WorldState)
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation) where
  | completed
      (result :
        TopLevelTerminalResult initialWorld invocation.target)
  | outOfFuel
      (context : TransactionHostStorageDriver.Context)
      (state : Core.State)
      (storageAddress_eq :
        context.context.storageAddress = invocation.target)
      (stateTyping :
        Core.HostStateHasType state contract.code.program.resultType
          contract.code.program.dataDefinitions)
      (workingDelta :
        TopLevelStorageDelta initialWorld
          context.context.values.working.1 invocation.target)
      (checkpointJournal_eq :
        context.context.values.checkpoint.effects.rollback =
          TransactionJournal.empty)

namespace TopLevelRunResult

/-- The root rollback journal retained by either terminal or resumable output. -/
def rootCheckpointJournal
    {initialWorld : WorldState}
    {contract : CheckedCoreContract}
    {invocation : TopLevelInvocation} :
    TopLevelRunResult initialWorld contract invocation → TransactionJournal
  | .completed result =>
      result.terminalContext.context.values.checkpoint.effects.rollback
  | .outOfFuel context _ _ _ _ _ =>
      context.context.values.checkpoint.effects.rollback

end TopLevelRunResult

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.TopLevelExecution`
-/

/-! Executable checked-Core top-level run and terminal state selection. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

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
  resultSupported :
    ∀ suspension remainingFuel,
      result.outcome ≠ .unsupported suspension remainingFuel
  storageAddress_eq :
    result.context.context.storageAddress = invocation.target
  workingDelta :
    TopLevelStorageDelta initialWorld
      result.context.context.values.working.1 invocation.target
  checkpointJournal_eq :
    result.context.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty

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
    resultSupported := by
      intro suspension remainingFuel
      exact contract.code.runWithTransactionStorage_ne_unsupported
        (initialTransactionContext installed) invocation.executionInputs fuel
        suspension remainingFuel
    storageAddress_eq := storageAddress_eq
    workingDelta :=
      workingDeltaOfRawRun contract invocation installed fuel result rfl
    checkpointJournal_eq := by
      calc
        result.context.context.values.checkpoint.effects.rollback =
            (initialTransactionContext installed).context.values.checkpoint.effects.rollback :=
          congrArg
            (fun checkpoint => checkpoint.effects.rollback)
            (TransactionHostStorageDriver.run_checkpoint
              (initialTransactionContext installed) invocation.executionInputs fuel
              (Core.State.initial contract.code.program.body Core.hostEnvironment))
        _ = TransactionJournal.empty := rfl
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
        context.context.values.working.1 invocation.target)
    (checkpointJournal_eq :
      context.context.values.checkpoint.effects.rollback =
        TransactionJournal.empty) :
    TopLevelTerminalResult initialWorld invocation.target :=
  match outcome with
  | .returned data => {
      terminalContext := context
      checkpointJournal_eq := checkpointJournal_eq
      coreValue := value
      coreStore := store
      outcome := .returned data
      finalWorld := context.context.values.working.1
      workingJournal := context.workingJournal
      workingJournal_eq := rfl
      committedJournal := context.workingJournal
      committedJournal_eq := rfl
      workingDelta := workingDelta
      committedDelta := workingDelta
    }
  | .reverted data => {
      terminalContext := context
      checkpointJournal_eq := checkpointJournal_eq
      coreValue := value
      coreStore := store
      outcome := .reverted data
      finalWorld := initialWorld
      workingJournal := context.workingJournal
      workingJournal_eq := rfl
      committedJournal :=
        context.context.values.checkpoint.effects.rollback
      committedJournal_eq := rfl
      workingDelta := workingDelta
      committedDelta :=
        TopLevelStorageDelta.identity initialWorld invocation.target
          installedAccount installedAccount_present
    }
  | .trapped reason => {
      terminalContext := context
      checkpointJournal_eq := checkpointJournal_eq
      coreValue := value
      coreStore := store
      outcome := .trapped reason
      finalWorld := initialWorld
      workingJournal := context.workingJournal
      workingJournal_eq := rfl
      committedJournal :=
        context.context.values.checkpoint.effects.rollback
      committedJournal_eq := rfl
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
              raw.workingDelta raw.checkpointJournal_eq)
      | none => False.elim (decodedNeNone decodedEq)
  | .outOfFuel state =>
      have stateTyping :
          Core.HostStateHasType state contract.code.program.resultType
            contract.code.program.dataDefinitions := by
        have resultTyping := raw.resultTyping
        rw [outcomeEq] at resultTyping
        exact resultTyping
      .outOfFuel raw.result.context state raw.storageAddress_eq stateTyping
        raw.workingDelta raw.checkpointJournal_eq
  | .fault _error _state =>
      have impossible : False := by
        have resultTyping := raw.resultTyping
        rw [outcomeEq] at resultTyping
        exact resultTyping
      False.elim impossible
  | .unsupported suspension remainingFuel =>
      False.elim (raw.resultSupported suspension remainingFuel outcomeEq)

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

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.TopLevelExecutionProperties`
-/

/-! Root-context and terminal-selection laws for top-level checked execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.TopLevelExecution

/-- The checked raw execution hidden by the total runner cannot fault. -/
theorem rawRun_ne_fault
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    (rawRun contract invocation installed fuel).outcome ≠
      .fault error faultState := by
  simpa [rawRun] using
    contract.code.runWithTransactionStorage_ne_fault
      (initialTransactionContext installed) invocation.executionInputs fuel
      error faultState

end Solcore.ContractRuntime.TopLevelExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.TopLevelExecutionResumption`
-/

/-! Fixed-input resumption for exhausted checked-Core top-level execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.TopLevelExecution

/-- Extend an exact initial-to-working delta through one handled execution suffix. -/
def extendWorkingDelta
    {initialWorld : WorldState}
    {target : Address}
    (context : TransactionHostStorageDriver.Context)
    (storageAddress_eq : context.context.storageAddress = target)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 target)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    TopLevelStorageDelta initialWorld
      (TransactionHostStorageDriver.run context inputs fuel state).context.context.values.working.1
      target := {
  initialAccount := delta.initialAccount
  finalAccount :=
    (TransactionHostStorageDriver.run context inputs fuel state).context.storageAccount
  initialAccount_present := delta.initialAccount_present
  finalAccount_present := by
    have finalAddress := TransactionHostStorageDriver.run_storageAddress
      context inputs fuel state
    have present :=
      (TransactionHostStorageDriver.run context inputs fuel state).context.storageAccount_present
    rw [finalAddress, storageAddress_eq] at present
    exact present
  code_preserved := by
    have currentPresent :
        context.context.values.working.1.account? target =
          some context.storageAccount := by
      simpa [storageAddress_eq] using context.storageAccount_present
    have finalAddress := TransactionHostStorageDriver.run_storageAddress
      context inputs fuel state
    have finalPresent :=
      (TransactionHostStorageDriver.run context inputs fuel state).context.storageAccount_present
    rw [finalAddress, storageAddress_eq] at finalPresent
    have currentAccount_eq :
        delta.finalAccount = context.storageAccount := by
      apply Option.some.inj
      exact delta.finalAccount_present.symm.trans currentPresent
    have suffix := TransactionHostStorageDriver.run_workingCode?
      context inputs fuel state target
    have suffix' :
        (TransactionHostStorageDriver.run context inputs fuel state).context.storageAccount.code? =
          context.storageAccount.code? := by
      change
        (TransactionHostStorageDriver.run context inputs fuel state).context.context.values.working.1.code?
            target =
          context.context.values.working.1.code? target at suffix
      simp [WorldState.code?, finalPresent, currentPresent] at suffix
      exact suffix
    exact suffix'.trans (by
      rw [← currentAccount_eq]
      exact delta.code_preserved)
  otherAccounts_preserved := by
    intro address different
    have differentCurrent : address ≠ context.context.storageAddress := by
      intro same
      apply different
      rw [← storageAddress_eq]
      exact same
    exact
      (TransactionHostStorageDriver.run_workingAccount?_of_ne_storageAddress
        context inputs fuel state address differentCurrent).trans
        (delta.otherAccounts_preserved address different)
}

/-- Package one resumed suffix with the invariants retained by exhaustion. -/
def validatedResumedRawResult
    {initialWorld : WorldState}
    {contract : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (context : TransactionHostStorageDriver.Context)
    (state : Core.State)
    (storageAddress_eq : context.context.storageAddress = invocation.target)
    (stateTyping :
      Core.HostStateHasType state contract.code.program.resultType
        contract.code.program.dataDefinitions)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target)
    (checkpointJournal_eq :
      context.context.values.checkpoint.effects.rollback =
        TransactionJournal.empty)
    (additional : Nat) :
    ValidatedRawResult initialWorld contract invocation :=
  let result :=
    TransactionHostStorageDriver.run context invocation.executionInputs additional state
  {
    result := result
    resultTyping := by
      exact TransactionHostStorageDriver.run_hasType
        context invocation.executionInputs additional state stateTyping
    resultSupported := by
      intro suspension remainingFuel
      exact TransactionHostStorageDriver.run_ne_unsupported
        context invocation.executionInputs additional state suspension
        remainingFuel
    storageAddress_eq := by
      have preserved := TransactionHostStorageDriver.run_storageAddress
        context invocation.executionInputs additional state
      change result.context.context.storageAddress = invocation.target
      exact preserved.trans storageAddress_eq
    workingDelta :=
      extendWorkingDelta context storageAddress_eq delta
        invocation.executionInputs additional state
    checkpointJournal_eq := by
      calc
        result.context.context.values.checkpoint.effects.rollback =
            context.context.values.checkpoint.effects.rollback :=
          congrArg
            (fun checkpoint => checkpoint.effects.rollback)
            (TransactionHostStorageDriver.run_checkpoint context
              invocation.executionInputs additional state)
        _ = TransactionJournal.empty := checkpointJournal_eq
  }

/-- Resume only the out-of-fuel branch under the same contract invocation. -/
def resumeWithFuel
    {initialWorld : WorldState}
    {contract : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (execution : TopLevelRunResult initialWorld contract invocation)
    (additional : Nat) :
    TopLevelRunResult initialWorld contract invocation :=
  match execution with
  | .completed result => .completed result
  | .outOfFuel context state storageAddress_eq stateTyping delta
      checkpointJournal_eq =>
      classifyRawResult contract invocation
        (validatedResumedRawResult context state storageAddress_eq stateTyping
          delta checkpointJournal_eq additional)

end Solcore.ContractRuntime.TopLevelExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.TopLevelExecutionResumptionProperties`
-/

/-! Exact split-fuel laws for executable checked-Core top-level runs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.TopLevelExecution

namespace ValidatedRawResult

/-- A validated raw result is uniquely determined by its driver result. -/
theorem eq_of_result_eq
    {initialWorld : WorldState}
    {contract : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (left right : ValidatedRawResult initialWorld contract invocation)
    (result_eq : left.result = right.result) :
    left = right := by
  cases left with
  | mk leftResult leftTyping leftSupported leftAddress leftDelta
      leftCheckpointJournal =>
      cases right with
      | mk rightResult rightTyping rightSupported rightAddress rightDelta
          rightCheckpointJournal =>
          dsimp only at result_eq
          subst rightResult
          have delta_eq := TopLevelStorageDelta.unique leftDelta rightDelta
          subst rightDelta
          rfl

end ValidatedRawResult

/-- Resuming an initial run agrees exactly with one summed-fuel run. -/
theorem resumeWithFuel_run
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel additional : Nat) :
    resumeWithFuel (run contract invocation installed fuel) additional =
      run contract invocation installed (fuel + additional) := by
  cases prefixEq : validatedRawRun contract invocation installed fuel with
  | mk result resultTyping resultSupported storageAddress_eq delta
      checkpointJournal_eq =>
      cases result with
      | mk context outcome =>
          cases outcome with
          | done value store =>
              have rawPrefixEq :
                  rawRun contract invocation installed fuel =
                    ⟨context, .done value store⟩ := by
                simpa [validatedRawRun] using
                  congrArg ValidatedRawResult.result prefixEq
              have summedEq :
                  rawRun contract invocation installed (fuel + additional) =
                    ⟨context, .done value store⟩ := by
                apply contract.code.runWithTransactionStorage_done_stable
                  (context := initialTransactionContext installed)
                  (inputs := invocation.executionInputs)
                  (by simpa [rawRun] using rawPrefixEq)
                omega
              have validatedEq :
                  validatedRawRun contract invocation installed fuel =
                    validatedRawRun contract invocation installed
                      (fuel + additional) := by
                apply ValidatedRawResult.eq_of_result_eq
                simpa [validatedRawRun] using rawPrefixEq.trans summedEq.symm
              have decodedNeNone :
                  contract.decodeCompletion? value ≠ none := by
                obtain ⟨_world, _storeTyping, valueTyping⟩ := resultTyping
                apply contract.entryProfile.decode?_ne_none_of_hasType
                rw [← contract.resultType_eq]
                exact valueTyping
              unfold run
              rw [← validatedEq, prefixEq]
              unfold classifyRawResult
              dsimp only [ValidatedRawResult.result,
                ValidatedRawResult.workingDelta]
              split
              · rfl
              · rename_i decodedEq
                exact False.elim (decodedNeNone decodedEq)
          | outOfFuel exhausted =>
              have rawPrefixEq :
                  rawRun contract invocation installed fuel =
                    ⟨context, .outOfFuel exhausted⟩ := by
                simpa [validatedRawRun] using
                  congrArg ValidatedRawResult.result prefixEq
              have summedEq :
                  rawRun contract invocation installed (fuel + additional) =
                    TransactionHostStorageDriver.run context
                      invocation.executionInputs
                      additional exhausted := by
                apply TransactionHostStorageDriver.run_additional_of_outOfFuel
                  (context := initialTransactionContext installed)
                  (nextContext := context)
                  (inputs := invocation.executionInputs)
                  (fuel := fuel)
                  (additional := additional)
                  (state := Core.State.initial contract.code.program.body
                    Core.hostEnvironment)
                  (exhausted := exhausted)
                simpa [rawRun,
                  CheckedHostCoreProgram.runWithTransactionStorage] using
                  rawPrefixEq
              have resumedEq :
                  validatedResumedRawResult context exhausted storageAddress_eq
                      resultTyping delta checkpointJournal_eq additional =
                    validatedRawRun contract invocation installed
                      (fuel + additional) := by
                apply ValidatedRawResult.eq_of_result_eq
                simpa [validatedResumedRawResult, validatedRawRun] using
                  summedEq.symm
              unfold run
              rw [prefixEq]
              change
                classifyRawResult contract invocation
                    (validatedResumedRawResult context exhausted
                      storageAddress_eq resultTyping delta checkpointJournal_eq
                      additional) =
                  classifyRawResult contract invocation
                    (validatedRawRun contract invocation installed
                      (fuel + additional))
              rw [resumedEq]
          | fault error faultState =>
              exact False.elim resultTyping
          | unsupported suspension remainingFuel =>
              exact False.elim
                (resultSupported suspension remainingFuel rfl)

/-- Adding zero fuel to an actual initial run leaves its total result unchanged. -/
@[simp] theorem resumeWithFuel_run_zero
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel : Nat) :
    resumeWithFuel (run contract invocation installed fuel) 0 =
      run contract invocation installed fuel := by
  simpa using resumeWithFuel_run contract invocation installed fuel 0

/-- Repeated resumptions of an initial run agree with one total fuel budget. -/
theorem resumeWithFuel_run_add
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel first second : Nat) :
    resumeWithFuel
        (resumeWithFuel (run contract invocation installed fuel) first)
        second =
      run contract invocation installed (fuel + first + second) := by
  rw [resumeWithFuel_run, resumeWithFuel_run]

end Solcore.ContractRuntime.TopLevelExecution
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsCoreLanguageResult
/-! Decode the ordinary Core language-result sum at the contract boundary.
The success callback keeps the existing entry codec. Language failures become
frame traps; malformed carriers, machine faults and fuel checkpoints stay
distinct. This adapter does not interpret source syntax or add machine states. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.CoreLanguageResult

universe u v w

/-- Decode only the outer language envelope. Typed callers certify its type
annotations and the success payload; the existing success codec is unchanged. -/
def decodeDone? {Context : Type u}
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (context : Context) (value : Core.Value) (store : Core.Store) :
    Option (FrameOutcome Core.Word) :=
  (Core.LanguageResult.decode? value).map fun
    | .succeeded payload => success context payload store
    | .failed reason => .trapped reason

/-- Preserve unfinished execution and raw internal faults without turning
either into a terminal language outcome. -/
inductive Outcome where
  | completed (carrier : Core.Value) (store : Core.Store)
      (frame : FrameOutcome Core.Word)
  | invalidCarrier (carrier : Core.Value) (store : Core.Store)
  | outOfFuel (state : Core.State)
  | fault (error : Core.MachineFault) (state : Core.State)
  | unsupported (suspension : Core.HostSuspension) (remainingFuel : Nat)

structure Result (Context : Type u) where
  context : Context
  outcome : Outcome

def decode {Context : Type u}
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (result : HostDriverResult Context) : Result Context :=
  ⟨result.context, match result.outcome with
    | .done value store => match decodeDone? success result.context value store with
      | some frame => .completed value store frame
      | none => .invalidCarrier value store
    | .outOfFuel state => .outOfFuel state
    | .fault error state => .fault error state
    | .unsupported suspension remaining => .unsupported suspension remaining⟩

/-- The existing host driver performs all requests and fuel accounting. -/
def run {Context : Type u} (handler : HostHandler Context)
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (context : Context) (fuel : Nat) (state : Core.State) : Result Context :=
  decode success (HostDriver.run handler context fuel state)

/-- Every host-typed language result has an envelope the adapter accepts. -/
theorem decodeDone?_ne_none_of_hasType {Context : Type u}
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (context : Context) (store : Core.Store)
    {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
    {value : Core.Value} {type : Core.Ty}
    (typed : Core.HostRuntimeValueHasType world value
      (Core.LanguageResult.resultType type) definitions) :
    decodeDone? success context value store ≠ none := by
  cases typed with
  | inLeft payload =>
      cases payload
      simp [decodeDone?]
  | inRight payload => simp [decodeDone?]

/-- The adapter retains the underlying host typing and rejects both malformed
envelopes and internal faults at typed entry points. The caller owns its codec. -/
def Outcome.HasType (outcome : Outcome) (type : Core.Ty)
    (definitions : Core.DataEnvironment := []) : Prop :=
  match outcome with
  | .completed carrier store _ =>
      ∃ world, Core.HostStoreHasTypes world store definitions ∧
        Core.HostRuntimeValueHasType world carrier (Core.LanguageResult.resultType type) definitions
  | .outOfFuel state => Core.HostStateHasType state (Core.LanguageResult.resultType type) definitions
  | .unsupported suspension _ =>
      Core.HostSuspensionHasType suspension (Core.LanguageResult.resultType type) definitions
  | .invalidCarrier _ _ | .fault _ _ => False

theorem decode_hasType {Context : Type u}
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (result : HostDriverResult Context)
    {definitions : Core.DataEnvironment} {type : Core.Ty}
    (typed : result.outcome.HasType (Core.LanguageResult.resultType type) definitions) :
    (decode success result).outcome.HasType type definitions := by
  cases result with
  | mk context outcome =>
      cases outcome with
      | done carrier store =>
          obtain ⟨world, storeTyped, carrierTyped⟩ := typed
          have accepted := decodeDone?_ne_none_of_hasType success context store carrierTyped
          cases decoded : decodeDone? success context carrier store with
          | none => exact False.elim (accepted decoded)
          | some frame =>
              simp only [decode, decoded, Outcome.HasType]
              exact ⟨world, storeTyped, carrierTyped⟩
      | outOfFuel | fault | unsupported => exact typed

theorem run_hasType {Context : Type u}
    (handler : HostHandler Context)
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (context : Context) (fuel : Nat) (state : Core.State)
    {definitions : Core.DataEnvironment} {type : Core.Ty}
    (typed : Core.HostStateHasType state (Core.LanguageResult.resultType type) definitions) :
    (run handler success context fuel state).outcome.HasType type definitions :=
  decode_hasType success _ (HostDriver.run_hasType handler context fuel state typed)

def Result.toFrame? {Context : Type u} {RollbackState : Type v} {TraceState : Type w}
    (result : Result Context)
    (values : Context → FrameCheckpointedWorkingPair RollbackState TraceState) :
    Option (FrameContinuationContext RollbackState TraceState Core.Word) :=
  match result.outcome with
  | .completed _ _ frame =>
      some (FrameContinuationContext.fromCheckpointedWorkingPair (values result.context) frame)
  | _ => none

/-- Reuse the established root finalizer only for decoded completed values.
The caller supplies the same working-world and checkpoint evidence as before. -/
def Result.finalize? {initialWorld : WorldState}
    (result : Result TransactionHostStorageDriver.Context)
    (invocation : TopLevelInvocation) (account : Account)
    (present : initialWorld.account? invocation.target = some account)
    (delta : TopLevelStorageDelta initialWorld
      result.context.context.values.working.1 invocation.target)
    (checkpoint : result.context.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty) :
    Option (TopLevelTerminalResult initialWorld invocation.target) :=
  match result.outcome with
  | .completed carrier store frame => some (TopLevelExecution.finalize invocation
      account present result.context carrier store frame delta checkpoint)
  | _ => none

end Solcore.ContractRuntime.CoreLanguageResult
end
