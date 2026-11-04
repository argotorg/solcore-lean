import Solcore.ContractRuntime.TopLevel
import Solcore.ContractRuntime.Internal.WorldStateLaws
import Solcore.ContractRuntime.Internal.ContractLaws
import Solcore.ContractRuntime.Internal.FrameLaws
import Solcore.ContractRuntime.Internal.StorageDriverLaws
import Solcore.ContractRuntime.Internal.TransactionLaws
import Solcore.ContractRuntime.Internal.DriverLaws
import Solcore.Core.LanguageResult

/-!
# Laws of top-level execution

`TopLevelExecution.run` and `TopLevelExecution.rawRun`, storage deltas, and language results at the
boundary.
-/

section
-- leanmerge: from Solcore.ContractRuntime.TopLevelStorageDelta
/-! Exact queryable target-storage change across top-level finalization. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace TopLevelStorageDelta

@[simp] theorem slotChange?_identity
    (world : WorldState)
    (target : Address)
    (account : Account)
    (present : world.account? target = some account)
    (slot : Core.Word) :
    (identity world target account present).slotChange? slot = none := by
  simp [slotChange?, identity]

end TopLevelStorageDelta

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.TopLevelStorageDeltaProperties`
-/

/-! Exact endpoint laws for queryable top-level storage deltas. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.TopLevelStorageDelta

theorem slotChange?_eq_none_iff
    {initialWorld finalWorld : WorldState}
    {target : Address}
    (delta : TopLevelStorageDelta initialWorld finalWorld target)
    (slot : Core.Word) :
    delta.slotChange? slot = none ↔
      delta.initialAccount.storageRead slot =
        delta.finalAccount.storageRead slot := by
  simp [slotChange?]

theorem slotChange?_eq_some_iff
    {initialWorld finalWorld : WorldState}
    {target : Address}
    (delta : TopLevelStorageDelta initialWorld finalWorld target)
    (slot before after : Core.Word) :
    delta.slotChange? slot = some (before, after) ↔
      delta.initialAccount.storageRead slot = before ∧
      delta.finalAccount.storageRead slot = after ∧
      before ≠ after := by
  unfold slotChange?
  by_cases same :
      delta.initialAccount.storageRead slot =
        delta.finalAccount.storageRead slot
  · simp [same]
    intro beforeEq afterEq
    exact beforeEq.symm.trans afterEq
  · simp only [if_neg same, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨beforeEq, afterEq⟩
      refine ⟨beforeEq, afterEq, ?_⟩
      intro valuesEqual
      apply same
      exact beforeEq.trans (valuesEqual.trans afterEq.symm)
    · rintro ⟨beforeEq, afterEq, _different⟩
      exact ⟨beforeEq, afterEq⟩

theorem finalWorld_code?_target
    {initialWorld finalWorld : WorldState}
    {target : Address}
    (delta : TopLevelStorageDelta initialWorld finalWorld target) :
    finalWorld.code? target = initialWorld.code? target := by
  simp [WorldState.code?, delta.initialAccount_present,
    delta.finalAccount_present, delta.code_preserved]

theorem initialWorld_readStorage?_target
    {initialWorld finalWorld : WorldState}
    {target : Address}
    (delta : TopLevelStorageDelta initialWorld finalWorld target)
    (slot : Core.Word) :
    initialWorld.readStorage? target slot =
      some (delta.initialAccount.storageRead slot) := by
  simp [WorldState.readStorage?, delta.initialAccount_present]

theorem finalWorld_readStorage?_target
    {initialWorld finalWorld : WorldState}
    {target : Address}
    (delta : TopLevelStorageDelta initialWorld finalWorld target)
    (slot : Core.Word) :
    finalWorld.readStorage? target slot =
      some (delta.finalAccount.storageRead slot) := by
  simp [WorldState.readStorage?, delta.finalAccount_present]

end Solcore.ContractRuntime.TopLevelStorageDelta
end

section
-- leanmerge: from Solcore.ContractRuntime.TopLevelExecution
/-! Root storage context derived from explicit top-level execution inputs. -/

set_option autoImplicit false

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

namespace TopLevelRunResult

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

end Solcore.ContractRuntime.TopLevelExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.TopLevelExecutionResumption`
-/

/-! Fixed-input resumption for exhausted checked-Core top-level execution. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.TopLevelExecutionResumptionProperties`
-/

/-! Exact split-fuel laws for executable checked-Core top-level runs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.TopLevelExecution

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

end Solcore.ContractRuntime.TopLevelExecution
end

section
-- leanmerge: from Solcore.ContractRuntime.CoreLanguageResult
/-! Decode the ordinary Core language-result sum at the contract boundary.
The success callback keeps the existing entry codec. Language failures become
frame traps; malformed carriers, machine faults and fuel checkpoints stay
distinct. This adapter does not interpret source syntax or add machine states. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.CoreLanguageResult

universe u v w

@[simp] theorem decodeDone?_success {Context : Type u}
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (context : Context) (value : Core.Value) (store : Core.Store) :
    decodeDone? success context (.inRight .word value) store =
      some (success context value store) := rfl

@[simp] theorem decodeDone?_failure {Context : Type u}
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (context : Context) (type : Core.Ty) (reason : Core.Word) (store : Core.Store) :
    decodeDone? success context (.inLeft type (.word reason)) store =
      some (.trapped reason) := rfl

/-- The success payload retains the host-runtime typing of the outer sum. -/
theorem decode?_host_typed
    {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
    {value : Core.Value} {type : Core.Ty}
    (typed : Core.HostRuntimeValueHasType world value
      (Core.LanguageResult.resultType type) definitions) :
    ∃ outcome, Core.LanguageResult.decode? value = some outcome ∧
      match outcome with
      | .succeeded payload => Core.HostRuntimeValueHasType world payload type definitions
      | .failed _ => True := by
  cases typed with
  | inLeft payload =>
      cases payload with
      | word => exact ⟨_, rfl, trivial⟩
  | inRight payload => exact ⟨_, rfl, payload⟩

theorem decode_ne_invalidCarrier_of_hasType {Context : Type u}
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (result : HostDriverResult Context)
    {definitions : Core.DataEnvironment} {type : Core.Ty}
    (typed : result.outcome.HasType (Core.LanguageResult.resultType type) definitions)
    (value : Core.Value) (store : Core.Store) :
    (decode success result).outcome ≠ .invalidCarrier value store := by
  cases result with
  | mk context outcome =>
      cases outcome with
      | done carrier localStore =>
          obtain ⟨world, _, carrierTyped⟩ := typed
          have accepted := decodeDone?_ne_none_of_hasType success context localStore
            carrierTyped
          cases decoded : decodeDone? success context carrier localStore with
          | none => exact False.elim (accepted decoded)
          | some frame => simp [decode, decoded]
      | outOfFuel | fault | unsupported => simp [decode]

@[simp] theorem decode_outOfFuel {Context : Type u}
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (context : Context) (state : Core.State) :
    decode success ⟨context, .outOfFuel state⟩ =
      ⟨context, .outOfFuel state⟩ := rfl

/-- The exact host-run completion is decoded after the unchanged driver step. -/
theorem run_of_host_done {Context : Type u}
    (handler : HostHandler Context)
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (context : Context) {fuel : Nat} {state : Core.State}
    {value : Core.Value} {store : Core.Store}
    (done : Core.hostRun fuel state = .done value store) :
    run handler success context fuel state = decode success ⟨context, .done value store⟩ := by
  unfold run
  rw [HostDriver.run, done]

@[simp] theorem toFrame?_outOfFuel {Context : Type u}
    {RollbackState : Type v} {TraceState : Type w}
    (context : Context) (state : Core.State)
    (values : Context → FrameCheckpointedWorkingPair RollbackState TraceState) :
    (Result.mk context (.outOfFuel state)).toFrame? values = none := rfl

theorem failure_resolves_trapped {Context : Type u}
    {RollbackState : Type v} {TraceState : Type w}
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (context : Context) (type : Core.Ty) (reason : Core.Word) (store : Core.Store)
    (values : Context → FrameCheckpointedWorkingPair RollbackState TraceState) :
    ((decode success ⟨context, .done (.inLeft type (.word reason)) store⟩).toFrame? values).map
        FrameContinuationContext.resolve = some (.trapped reason) := rfl

/-- A language failure follows the existing trap rollback policy, including
rollback-scoped observations; speculative state is still retained for inspection. -/
theorem failure_finalizes_rollback {initialWorld : WorldState}
    (success : TransactionHostStorageDriver.Context → Core.Value → Core.Store →
      FrameOutcome Core.Word)
    (context : TransactionHostStorageDriver.Context)
    (type : Core.Ty) (reason : Core.Word) (store : Core.Store)
    (invocation : TopLevelInvocation) (account : Account)
    (present : initialWorld.account? invocation.target = some account)
    (delta : TopLevelStorageDelta initialWorld
      context.context.values.working.1 invocation.target)
    (checkpoint : context.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty) :
    let finalized := (decode success
      ⟨context, .done (.inLeft type (.word reason)) store⟩).finalize?
        invocation account present delta checkpoint
    finalized.map (·.finalWorld) = some initialWorld ∧
      finalized.map (·.committedJournal) = some TransactionJournal.empty ∧
      finalized.map (·.workingJournal) = some context.workingJournal := by
  dsimp [decode, decodeDone?, Core.LanguageResult.decode?, Result.finalize?,
    TopLevelExecution.finalize]
  exact ⟨rfl, congrArg some checkpoint, rfl⟩

@[simp] theorem finalize?_outOfFuel {initialWorld : WorldState}
    (context : TransactionHostStorageDriver.Context) (state : Core.State)
    (invocation : TopLevelInvocation) (account : Account)
    (present : initialWorld.account? invocation.target = some account)
    (delta : TopLevelStorageDelta initialWorld
      context.context.values.working.1 invocation.target)
    (checkpoint : context.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty) :
    (Result.mk context (.outOfFuel state)).finalize?
      invocation account present delta checkpoint = none := rfl

end Solcore.ContractRuntime.CoreLanguageResult
end
