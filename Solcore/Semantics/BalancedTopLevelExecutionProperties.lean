import Solcore.Semantics.BalancedTopLevelExecution
import Solcore.Semantics.OneLevelNestedExecutionResumptionProperties

/-! Branch and exact resumption laws for balance-aware root execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.BalancedTopLevelExecution

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
      result.committedWorld? = none := by
  simp [finalWorld?, terminalStatus?, committedWorld?, outer, inner]

end Result

theorem run_of_zero_value
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (registry : CheckedContractRegistry)
    (fuel : Nat)
    (zero : rootInvocation.callValue = Core.Word.zero) :
    (run rootContract rootInvocation installed registry fuel).view =
      .execution
        (OneLevelNestedExecution.run rootContract rootInvocation installed
          registry fuel) := by
  simp [run, runWithEnvironment, OneLevelNestedExecution.run, zero]

theorem run_of_transfer_failure
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (registry : CheckedContractRegistry)
    (fuel : Nat)
    (failure : BalanceTransferFailure)
    (nonzero : rootInvocation.callValue ≠ Core.Word.zero)
    (failed :
      initialWorld.transferBalance rootInvocation.caller
          rootInvocation.target rootInvocation.callValue =
      .error failure) :
    (run rootContract rootInvocation installed registry fuel).view =
      .rejected (RejectedResult.ofFailure initialWorld failure) := by
  unfold run runWithEnvironment
  split
  · contradiction
  · split
    · rename_i actualFailure branchEq
      have equal : actualFailure = failure := by
        exact Except.error.inj (branchEq.symm.trans failed)
      subst actualFailure
      rfl
    · rename_i actualWorld branchEq
      have impossible : False := by
        cases failed.symm.trans branchEq
      contradiction

theorem run_of_transfer_success
    {initialWorld workingWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (registry : CheckedContractRegistry)
    (fuel : Nat)
    (nonzero : rootInvocation.callValue ≠ Core.Word.zero)
    (transferred :
      initialWorld.transferBalance rootInvocation.caller
          rootInvocation.target rootInvocation.callValue =
        .ok workingWorld) :
    (run rootContract rootInvocation installed registry fuel).view =
      .execution
        (OneLevelNestedExecution.runMode (.callsOnly registry) fuel
          (OneLevelNestedExecution.Mode.preparedRoot rootContract
            rootInvocation
            (WorldState.transferBalance_preserves_installed transferred
              installed))
          (.balancedInitial installed transferred)) := by
  unfold run runWithEnvironment
  split
  · contradiction
  · split
    · rename_i actualFailure branchEq
      have impossible : False := by
        cases transferred.symm.trans branchEq
      contradiction
    · rename_i actualWorld branchEq
      have equal : actualWorld = workingWorld := by
        exact Except.ok.inj (branchEq.symm.trans transferred)
      subst actualWorld
      rfl

@[simp] theorem resumeWithFuel_rejected
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (rejected : RejectedResult initialWorld)
    (observed : result.view = .rejected rejected)
    (additional : Nat) :
    resumeWithFuel result additional = result := by
  simp [resumeWithFuel, observed]

theorem resumeWithFuel_execution
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (execution :
      OneLevelNestedExecution.Result initialWorld rootContract
        rootInvocation)
    (observed : result.view = .execution execution)
    (additional : Nat) :
    (resumeWithFuel result additional).view =
      .execution
        (OneLevelNestedExecution.resumeWithFuel execution additional) := by
  simp [resumeWithFuel, observed]

/-- Splitting fuel never repeats top-level transfer preflight. -/
theorem resumeWithFuel_run
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (registry : CheckedContractRegistry)
    (fuel additional : Nat) :
    resumeWithFuel
        (run rootContract rootInvocation installed registry fuel) additional =
      run rootContract rootInvocation installed registry
        (fuel + additional) := by
  unfold run runWithEnvironment
  split
  · apply Result.eq_of_view_eq
    simp [resumeWithFuel,
      OneLevelNestedExecution.resumeWithFuel_runWithEnvironment]
  · split
    · rfl
    · apply Result.eq_of_view_eq
      simp [resumeWithFuel,
        OneLevelNestedExecution.resumeWithFuel_runMode]

@[simp] theorem resumeWithFuel_run_zero
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (registry : CheckedContractRegistry)
    (fuel : Nat) :
    resumeWithFuel
        (run rootContract rootInvocation installed registry fuel) 0 =
      run rootContract rootInvocation installed registry fuel := by
  rw [resumeWithFuel_run]
  simp

end Solcore.Semantics.BalancedTopLevelExecution
