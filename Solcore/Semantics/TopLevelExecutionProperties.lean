import Solcore.Semantics.TopLevelExecution
import Solcore.Semantics.TopLevelStorageDeltaProperties

/-! Root-context and terminal-selection laws for top-level checked execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.TopLevelExecution

@[simp] theorem outcome_finalize
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : HostStorageDriver.Context Unit Unit)
    (value : Core.Value)
    (store : Core.Store)
    (outcome : FrameOutcome Core.Word)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target) :
    (finalize invocation installedAccount installedAccount_present
      context value store outcome delta).outcome = outcome := by
  cases outcome <;> rfl

@[simp] theorem terminalContext_finalize
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : HostStorageDriver.Context Unit Unit)
    (value : Core.Value)
    (store : Core.Store)
    (outcome : FrameOutcome Core.Word)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target) :
    (finalize invocation installedAccount installedAccount_present
      context value store outcome delta).terminalContext = context := by
  cases outcome <;> rfl

@[simp] theorem finalWorld_finalize_returned
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : HostStorageDriver.Context Unit Unit)
    (value : Core.Value)
    (store : Core.Store)
    (data : Bytes)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target) :
    (finalize invocation installedAccount installedAccount_present
      context value store (.returned data) delta).finalWorld =
        context.context.values.working.1 := by
  rfl

@[simp] theorem finalWorld_finalize_reverted
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : HostStorageDriver.Context Unit Unit)
    (value : Core.Value)
    (store : Core.Store)
    (data : Bytes)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target) :
    (finalize invocation installedAccount installedAccount_present
      context value store (.reverted data) delta).finalWorld = initialWorld := by
  rfl

@[simp] theorem finalWorld_finalize_trapped
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : HostStorageDriver.Context Unit Unit)
    (value : Core.Value)
    (store : Core.Store)
    (reason : Core.Word)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target) :
    (finalize invocation installedAccount installedAccount_present
      context value store (.trapped reason) delta).finalWorld = initialWorld := by
  rfl

@[simp] theorem committedSlotChange?_finalize_returned
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : HostStorageDriver.Context Unit Unit)
    (value : Core.Value) (store : Core.Store) (data : Bytes)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target)
    (slot : Core.Word) :
    (finalize invocation installedAccount installedAccount_present
      context value store (.returned data) delta).committedDelta.slotChange? slot =
        delta.slotChange? slot := by
  rfl

@[simp] theorem committedSlotChange?_finalize_reverted
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : HostStorageDriver.Context Unit Unit)
    (value : Core.Value) (store : Core.Store) (data : Bytes)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target)
    (slot : Core.Word) :
    (finalize invocation installedAccount installedAccount_present
      context value store (.reverted data) delta).committedDelta.slotChange? slot =
        none := by
  exact TopLevelStorageDelta.slotChange?_identity _ _ _ _ _

@[simp] theorem committedSlotChange?_finalize_trapped
    {initialWorld : WorldState}
    (invocation : TopLevelInvocation)
    (installedAccount : Account)
    (installedAccount_present :
      initialWorld.account? invocation.target = some installedAccount)
    (context : HostStorageDriver.Context Unit Unit)
    (value : Core.Value) (store : Core.Store) (reason : Core.Word)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target)
    (slot : Core.Word) :
    (finalize invocation installedAccount installedAccount_present
      context value store (.trapped reason) delta).committedDelta.slotChange? slot =
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

end Solcore.Semantics.TopLevelExecution
