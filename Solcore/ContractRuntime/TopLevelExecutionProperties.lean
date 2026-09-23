import Solcore.ContractRuntime.TopLevelExecution
import Solcore.ContractRuntime.TopLevelStorageDeltaProperties

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
