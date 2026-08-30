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

end RejectedResult

namespace Result

@[simp] theorem ofExecution_view
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (execution :
      OneLevelNestedExecution.Result initialWorld rootContract
        rootInvocation) :
    (ofExecution execution).view = .execution execution := by
  rfl

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
  simp [run, zero]

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
  unfold run
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
        (OneLevelNestedExecution.runMode registry fuel
          (OneLevelNestedExecution.Mode.preparedRoot rootContract
            rootInvocation
            (WorldState.transferBalance_preserves_installed transferred
              installed))
          (.balancedInitial installed transferred)) := by
  unfold run
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
    resumeWithFuel result additional =
      Result.ofExecution
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
  unfold run
  split
  · apply Result.eq_of_view_eq
    simp [resumeWithFuel,
      OneLevelNestedExecution.resumeWithFuel_run]
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
