import Solcore.ContractRuntime.CheckedCoreContract
import Solcore.ContractRuntime.FrameCheckpointSnapshot
import Solcore.ContractRuntime.HostStorageContext
import Solcore.ContractRuntime.TransactionHostStorage
import Solcore.ContractRuntime.WorldStateCode
import Solcore.ContractRuntime.HostDriver
import Solcore.ContractRuntime.TopLevelStorageDelta

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

@[simp] theorem initialContext_storageAddress
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialContext installed).context.storageAddress = target := by
  rfl

@[simp] theorem initialContext_storageAccount
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialContext installed).storageAccount = installed.account := by
  rfl

@[simp] theorem initialContext_checkpointState
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialContext installed).context.values.checkpoint.state =
      initialWorld := by
  rfl

@[simp] theorem initialContext_workingState
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialContext installed).context.values.working.1 = initialWorld := by
  rfl

@[simp] theorem initialContext_checkpointEffects
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialContext installed).context.values.checkpoint.effects =
      initialEffects := by
  rfl

@[simp] theorem initialContext_workingEffects
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialContext installed).context.values.working.2 = initialEffects := by
  rfl

theorem initialWorld_code?
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    initialWorld.code? target = some contract.code := by
  simp [WorldState.code?, installed.account_present, installed.code_present]

@[simp] theorem preparedContext_storageAddress
    {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (preparedContext (checkpointWorld := checkpointWorld) installed).context.storageAddress =
      target := by
  rfl

@[simp] theorem preparedContext_storageAccount
    {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (preparedContext (checkpointWorld := checkpointWorld) installed).storageAccount =
      installed.account := by
  rfl

@[simp] theorem preparedContext_checkpointState
    {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (preparedContext (checkpointWorld := checkpointWorld) installed).context.values.checkpoint.state =
      checkpointWorld := by
  rfl

@[simp] theorem preparedContext_workingState
    {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (preparedContext (checkpointWorld := checkpointWorld) installed).context.values.working.1 =
      workingWorld := by
  rfl

@[simp] theorem preparedContext_checkpointEffects
    {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (preparedContext (checkpointWorld := checkpointWorld) installed).context.values.checkpoint.effects =
      initialEffects := by
  rfl

@[simp] theorem preparedContext_workingEffects
    {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (preparedContext (checkpointWorld := checkpointWorld) installed).context.values.working.2 =
      initialEffects := by
  rfl

@[simp] theorem initialTransactionContext_storageAddress
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialTransactionContext installed).context.storageAddress = target := by
  rfl

@[simp] theorem initialTransactionContext_storageAccount
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialTransactionContext installed).storageAccount = installed.account := by
  rfl

@[simp] theorem initialTransactionContext_checkpointState
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialTransactionContext installed).context.values.checkpoint.state =
      initialWorld := by
  rfl

@[simp] theorem initialTransactionContext_workingState
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialTransactionContext installed).context.values.working.1 =
      initialWorld := by
  rfl

@[simp] theorem initialTransactionContext_checkpointJournal
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialTransactionContext installed).context.values.checkpoint.effects.rollback =
      TransactionJournal.empty := by
  rfl

@[simp] theorem initialTransactionContext_workingJournal
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialTransactionContext installed).workingJournal =
      TransactionJournal.empty := by
  rfl

@[simp] theorem preparedTransactionContextWithJournals_checkpointJournal
    {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (checkpointJournal workingJournal : TransactionJournal)
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (preparedTransactionContextWithJournals
      (checkpointWorld := checkpointWorld) checkpointJournal workingJournal
      installed).context.values.checkpoint.effects.rollback =
        checkpointJournal := by
  rfl

@[simp] theorem preparedTransactionContextWithJournals_workingJournal
    {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (checkpointJournal workingJournal : TransactionJournal)
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (preparedTransactionContextWithJournals
      (checkpointWorld := checkpointWorld) checkpointJournal workingJournal
      installed).workingJournal = workingJournal := by
  rfl

end TopLevelExecution

namespace TopLevelInvocation

@[simp] theorem executionInputs_codeAddress
    (invocation : TopLevelInvocation) :
    invocation.executionInputs.codeAddress = invocation.target := by
  rfl

@[simp] theorem executionInputs_currentAddress
    (invocation : TopLevelInvocation) :
    invocation.executionInputs.currentAddress = invocation.target := by
  rfl

@[simp] theorem executionInputs_callValue
    (invocation : TopLevelInvocation) :
    invocation.executionInputs.callValue = invocation.callValue := by
  rfl

@[simp] theorem executionInputs_callerAddress
    (invocation : TopLevelInvocation) :
    invocation.executionInputs.callerAddress = invocation.caller := by
  rfl

@[simp] theorem executionInputs_inputData
    (invocation : TopLevelInvocation) :
    invocation.executionInputs.inputData = invocation.inputData := by
  rfl

end TopLevelInvocation

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

/-- Every public top-level result retains the empty root rollback checkpoint. -/
@[simp] theorem rootCheckpointJournal_eq_empty
    {initialWorld : WorldState}
    {contract : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (execution : TopLevelRunResult initialWorld contract invocation) :
    execution.rootCheckpointJournal = TransactionJournal.empty := by
  cases execution with
  | completed result =>
      exact result.checkpointJournal_eq
  | outOfFuel context state address typing delta checkpointJournal_eq =>
      exact checkpointJournal_eq

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

@[simp] theorem outcome_finalize
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : TransactionHostStorageDriver.Context)
    (value : Core.Value)
    (store : Core.Store)
    (outcome : FrameOutcome Core.Word)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target)
    (checkpointJournal_eq :
      context.context.values.checkpoint.effects.rollback =
        TransactionJournal.empty) :
    (finalize invocation installedAccount installedAccount_present
      context value store outcome delta checkpointJournal_eq).outcome = outcome := by
  cases outcome <;> rfl

@[simp] theorem terminalContext_finalize
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : TransactionHostStorageDriver.Context)
    (value : Core.Value)
    (store : Core.Store)
    (outcome : FrameOutcome Core.Word)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target)
    (checkpointJournal_eq :
      context.context.values.checkpoint.effects.rollback =
        TransactionJournal.empty) :
    (finalize invocation installedAccount installedAccount_present
      context value store outcome delta checkpointJournal_eq).terminalContext = context := by
  cases outcome <;> rfl

@[simp] theorem workingJournal_finalize
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : TransactionHostStorageDriver.Context)
    (value : Core.Value)
    (store : Core.Store)
    (outcome : FrameOutcome Core.Word)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target)
    (checkpointJournal_eq :
      context.context.values.checkpoint.effects.rollback =
        TransactionJournal.empty) :
    (finalize invocation installedAccount installedAccount_present
      context value store outcome delta checkpointJournal_eq).workingJournal =
        context.workingJournal := by
  cases outcome <;> rfl

@[simp] theorem committedJournal_finalize_returned
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : TransactionHostStorageDriver.Context)
    (value : Core.Value) (store : Core.Store) (data : Bytes)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target)
    (checkpointJournal_eq :
      context.context.values.checkpoint.effects.rollback =
        TransactionJournal.empty) :
    (finalize invocation installedAccount installedAccount_present
      context value store (.returned data) delta
        checkpointJournal_eq).committedJournal =
        context.workingJournal := by
  rfl

@[simp] theorem committedJournal_finalize_reverted
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : TransactionHostStorageDriver.Context)
    (value : Core.Value) (store : Core.Store) (data : Bytes)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target)
    (checkpointJournal_eq :
      context.context.values.checkpoint.effects.rollback =
        TransactionJournal.empty) :
    (finalize invocation installedAccount installedAccount_present
      context value store (.reverted data) delta
        checkpointJournal_eq).committedJournal =
        context.context.values.checkpoint.effects.rollback := by
  rfl

@[simp] theorem committedJournal_finalize_trapped
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : TransactionHostStorageDriver.Context)
    (value : Core.Value) (store : Core.Store) (reason : Core.Word)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target)
    (checkpointJournal_eq :
      context.context.values.checkpoint.effects.rollback =
        TransactionJournal.empty) :
    (finalize invocation installedAccount installedAccount_present
      context value store (.trapped reason) delta
        checkpointJournal_eq).committedJournal =
        context.context.values.checkpoint.effects.rollback := by
  rfl

@[simp] theorem finalWorld_finalize_returned
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : TransactionHostStorageDriver.Context)
    (value : Core.Value)
    (store : Core.Store)
    (data : Bytes)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target)
    (checkpointJournal_eq :
      context.context.values.checkpoint.effects.rollback =
        TransactionJournal.empty) :
    (finalize invocation installedAccount installedAccount_present
      context value store (.returned data) delta
        checkpointJournal_eq).finalWorld =
        context.context.values.working.1 := by
  rfl

@[simp] theorem finalWorld_finalize_reverted
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : TransactionHostStorageDriver.Context)
    (value : Core.Value)
    (store : Core.Store)
    (data : Bytes)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target)
    (checkpointJournal_eq :
      context.context.values.checkpoint.effects.rollback =
        TransactionJournal.empty) :
    (finalize invocation installedAccount installedAccount_present
      context value store (.reverted data) delta
        checkpointJournal_eq).finalWorld = initialWorld := by
  rfl

@[simp] theorem finalWorld_finalize_trapped
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : TransactionHostStorageDriver.Context)
    (value : Core.Value)
    (store : Core.Store)
    (reason : Core.Word)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target)
    (checkpointJournal_eq :
      context.context.values.checkpoint.effects.rollback =
        TransactionJournal.empty) :
    (finalize invocation installedAccount installedAccount_present
      context value store (.trapped reason) delta
        checkpointJournal_eq).finalWorld = initialWorld := by
  rfl

@[simp] theorem committedSlotChange?_finalize_returned
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : TransactionHostStorageDriver.Context)
    (value : Core.Value) (store : Core.Store) (data : Bytes)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target)
    (checkpointJournal_eq :
      context.context.values.checkpoint.effects.rollback =
        TransactionJournal.empty)
    (slot : Core.Word) :
    (finalize invocation installedAccount installedAccount_present
      context value store (.returned data) delta
        checkpointJournal_eq).committedDelta.slotChange? slot =
        delta.slotChange? slot := by
  rfl

@[simp] theorem committedSlotChange?_finalize_reverted
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : TransactionHostStorageDriver.Context)
    (value : Core.Value) (store : Core.Store) (data : Bytes)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target)
    (checkpointJournal_eq :
      context.context.values.checkpoint.effects.rollback =
        TransactionJournal.empty)
    (slot : Core.Word) :
    (finalize invocation installedAccount installedAccount_present
      context value store (.reverted data) delta
        checkpointJournal_eq).committedDelta.slotChange? slot =
        none := by
  exact TopLevelStorageDelta.slotChange?_identity _ _ _ _ _

@[simp] theorem committedSlotChange?_finalize_trapped
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : TransactionHostStorageDriver.Context)
    (value : Core.Value) (store : Core.Store) (reason : Core.Word)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target)
    (checkpointJournal_eq :
      context.context.values.checkpoint.effects.rollback =
        TransactionJournal.empty)
    (slot : Core.Word) :
    (finalize invocation installedAccount installedAccount_present
      context value store (.trapped reason) delta
        checkpointJournal_eq).committedDelta.slotChange? slot =
        none := by
  exact TopLevelStorageDelta.slotChange?_identity _ _ _ _ _

theorem rawRun_working_code?
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel : Nat) :
    (rawRun contract invocation installed fuel).context.context.values.working.1.code?
        invocation.target = some contract.code := by
  exact
    (workingDelta contract invocation installed fuel).finalWorld_code?_target.trans
      (initialWorld_code? installed)

@[simp] theorem rawRun_checkpointJournal
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel : Nat) :
    (rawRun contract invocation installed fuel).context.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty := by
  simp [rawRun, CheckedHostCoreProgram.runWithTransactionStorage]

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

/-- Classifying one driver result is independent of invariant witnesses. -/
theorem classifyRawResult_unique
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (left right : ValidatedRawResult initialWorld contract invocation)
    (result_eq : left.result = right.result) :
    classifyRawResult contract invocation left =
      classifyRawResult contract invocation right := by
  have raw_eq := ValidatedRawResult.eq_of_result_eq left right result_eq
  subst right
  rfl

/-- A terminal total result remains terminal under every additional budget. -/
@[simp] theorem resumeWithFuel_completed
    {initialWorld : WorldState}
    {contract : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : TopLevelTerminalResult initialWorld invocation.target)
    (additional : Nat) :
    resumeWithFuel
        (TopLevelRunResult.completed (contract := contract) result)
        additional =
      TopLevelRunResult.completed result := by
  rfl

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
