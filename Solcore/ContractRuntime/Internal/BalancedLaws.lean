import Solcore.ContractRuntime.BalancedExecution
import Solcore.ContractRuntime.Internal.CreationLaws
import Solcore.ContractRuntime.Internal.NestedLaws
import Solcore.ContractRuntime.Internal.WorldStateDeltaLaws

/-!
# Laws of balanced execution

Projections of `BalancedTopLevelExecution.Result` on completed runs.
-/

section
-- leanmerge: from Solcore.ContractRuntime.BalancedTopLevelExecution
/-! Total top-level value preflight wrapped around the nested checked runner. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.BalancedTopLevelExecutionProperties`
-/

/-! Branch and exact resumption laws for balance-aware root execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.BalancedTopLevelExecution

namespace RejectedResult

@[simp] theorem ofFailure_failure
    (initialWorld : WorldState)
    (failure : BalanceTransferFailure) :
    (ofFailure initialWorld failure).failure = failure := by
  rfl

@[simp] theorem ofFailure_finalWorld
    (initialWorld : WorldState)
    (failure : BalanceTransferFailure) :
    (ofFailure initialWorld failure).finalWorld = initialWorld := by
  rfl

@[simp] theorem ofFailure_committedDelta
    (initialWorld : WorldState)
    (failure : BalanceTransferFailure) :
    (ofFailure initialWorld failure).committedDelta = .exact := by
  rfl

@[simp] theorem ofFailure_committedJournal
    (initialWorld : WorldState)
    (failure : BalanceTransferFailure) :
    (ofFailure initialWorld failure).committedJournal =
      TransactionJournal.empty := by
  rfl

@[simp] theorem committedJournal_eq_empty
    {initialWorld : WorldState}
    (rejected : RejectedResult initialWorld) :
    rejected.committedJournal = TransactionJournal.empty :=
  rejected.committedJournal_empty

theorem committedDelta_accountEndpoints_identity
    {initialWorld : WorldState}
    (rejected : RejectedResult initialWorld)
    (address : Address) :
    rejected.committedDelta.accountEndpoints address =
      (initialWorld.account? address, initialWorld.account? address) := by
  simp [WorldStateDelta.accountEndpoints, rejected.finalWorld_eq]

theorem committedDelta_storageEndpoints_identity
    {initialWorld : WorldState}
    (rejected : RejectedResult initialWorld)
    (address : Address)
    (slot : Core.Word) :
    rejected.committedDelta.storageEndpoints address slot =
      (initialWorld.readStorage? address slot,
        initialWorld.readStorage? address slot) := by
  simp [WorldStateDelta.storageEndpoints, rejected.finalWorld_eq]

theorem committedDelta_balanceEndpoints_identity
    {initialWorld : WorldState}
    (rejected : RejectedResult initialWorld)
    (address : Address) :
    rejected.committedDelta.balanceEndpoints address =
      (initialWorld.balance? address, initialWorld.balance? address) := by
  simp [WorldStateDelta.balanceEndpoints, rejected.finalWorld_eq]

theorem committedDelta_balanceChange?_identity
    {initialWorld : WorldState}
    (rejected : RejectedResult initialWorld)
    (address : Address) :
    rejected.committedDelta.balanceChange? address = none := by
  simp [WorldStateDelta.balanceChange?,
    committedDelta_balanceEndpoints_identity]

end RejectedResult

namespace Result

theorem finalWorld?_rejected
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (rejected : RejectedResult initialWorld)
    (observed : result.view = .rejected rejected) :
    result.finalWorld? = some rejected.finalWorld := by
  simp [finalWorld?, observed]

theorem terminalStatus?_rejected
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (rejected : RejectedResult initialWorld)
    (observed : result.view = .rejected rejected) :
    result.terminalStatus? = some (.error rejected.failure) := by
  simp [terminalStatus?, observed]

theorem committedWorld?_rejected
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (rejected : RejectedResult initialWorld)
    (observed : result.view = .rejected rejected) :
    result.committedWorld? =
      some ⟨rejected.finalWorld, rejected.committedDelta⟩ := by
  simp [committedWorld?, observed]

theorem workingJournal?_rejected
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (rejected : RejectedResult initialWorld)
    (observed : result.view = .rejected rejected) :
    result.workingJournal? = some TransactionJournal.empty := by
  simp [workingJournal?, observed]

theorem committedJournal?_rejected
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (rejected : RejectedResult initialWorld)
    (observed : result.view = .rejected rejected) :
    result.committedJournal? = some TransactionJournal.empty := by
  simp [committedJournal?, observed]

theorem finalWorld?_completed
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (execution : OneLevelNestedExecution.Result initialWorld rootContract rootInvocation)
    (terminal : OneLevelNestedExecution.TerminalResult initialWorld rootContract rootInvocation)
    (outer : result.view = .execution execution)
    (inner : execution.view = .completed terminal) :
    result.finalWorld? = some terminal.finalWorld := by
  simp [finalWorld?, outer, inner]

theorem terminalStatus?_completed
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (execution : OneLevelNestedExecution.Result initialWorld rootContract rootInvocation)
    (terminal : OneLevelNestedExecution.TerminalResult initialWorld rootContract rootInvocation)
    (outer : result.view = .execution execution)
    (inner : execution.view = .completed terminal) :
    result.terminalStatus? = some (.ok terminal.outcome) := by
  simp [terminalStatus?, outer, inner]

theorem committedWorld?_completed
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (execution : OneLevelNestedExecution.Result initialWorld rootContract rootInvocation)
    (terminal : OneLevelNestedExecution.TerminalResult initialWorld rootContract rootInvocation)
    (outer : result.view = .execution execution)
    (inner : execution.view = .completed terminal) :
    result.committedWorld? = some ⟨terminal.finalWorld, terminal.committedDelta⟩ := by
  simp [committedWorld?, outer, inner]

theorem workingJournal?_completed
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (execution : OneLevelNestedExecution.Result initialWorld rootContract rootInvocation)
    (terminal : OneLevelNestedExecution.TerminalResult initialWorld rootContract rootInvocation)
    (outer : result.view = .execution execution)
    (inner : execution.view = .completed terminal) :
    result.workingJournal? = some terminal.workingJournal := by
  simp [workingJournal?, outer, inner]

theorem committedJournal?_completed
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (execution : OneLevelNestedExecution.Result initialWorld rootContract rootInvocation)
    (terminal : OneLevelNestedExecution.TerminalResult initialWorld rootContract rootInvocation)
    (outer : result.view = .execution execution)
    (inner : execution.view = .completed terminal) :
    result.committedJournal? = some terminal.committedJournal := by
  simp [committedJournal?, outer, inner]

theorem observations_outOfFuel
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (execution : OneLevelNestedExecution.Result initialWorld rootContract rootInvocation)
    (registry : ExecutionEnvironment)
    (mode : OneLevelNestedExecution.Mode initialWorld rootContract rootInvocation)
    (reachable : OneLevelNestedExecution.Reachable registry mode)
    (outer : result.view = .execution execution)
    (inner : execution.view = .outOfFuel registry mode reachable) :
    result.finalWorld? = none ∧ result.terminalStatus? = none ∧
      result.committedWorld? = none ∧ result.workingJournal? = none ∧
      result.committedJournal? = none := by
  simp [finalWorld?, terminalStatus?, committedWorld?, workingJournal?,
    committedJournal?, outer, inner]

end Result

end Solcore.ContractRuntime.BalancedTopLevelExecution
end
