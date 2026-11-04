import Solcore.ContractRuntime.Creation
import Solcore.ContractRuntime.Transactions
import Solcore.ContractRuntime.WorldState
import Solcore.ContractRuntime.Contracts
import Solcore.ContractRuntime.NestedExecution
import Solcore.ContractRuntime.Frames
import Solcore.Core.Syntax
import Solcore.ContractRuntime.Internal.NestedLaws

/-!
# Balanced top-level execution

The public entry point: the value transfer of the call, then nested execution.
`BalancedTopLevelExecution.run`, `BalancedTopLevelExecution.runWithEnvironment` and
`BalancedTopLevelExecution.resumeWithFuel` give a `BalancedTopLevelExecution.Result`.

Main theorems: `BalancedTopLevelExecution.run_of_zero_value`,
`BalancedTopLevelExecution.run_of_transfer_failure` and
`BalancedTopLevelExecution.run_of_transfer_success` say what the preflight does, and
`BalancedTopLevelExecution.resumeWithFuel_run` and `BalancedTopLevelExecution.resumeWithFuel_run_zero`
that splitting fuel never repeats it. They stay here because the constructor of
`BalancedTopLevelExecution.Result` is private.
-/

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsBalancedTopLevelExecution
/-! Total top-level value preflight wrapped around the nested checked runner. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.BalancedTopLevelExecution

/-- A pre-execution transfer rejection with an exact identity commit. -/
structure RejectedResult (initialWorld : WorldState) where
  failure : BalanceTransferFailure
  finalWorld : WorldState
  finalWorld_eq : finalWorld = initialWorld
  committedDelta : WorldStateDelta initialWorld finalWorld
  /-- A rejected preflight commits no rollback-scoped observations. -/
  committedJournal : TransactionJournal
  committedJournal_empty : committedJournal = TransactionJournal.empty

namespace RejectedResult

/-- Build the canonical no-execution rejection for one explicit world. -/
def ofFailure
    (initialWorld : WorldState)
    (failure : BalanceTransferFailure) : RejectedResult initialWorld := {
  failure := failure
  finalWorld := initialWorld
  finalWorld_eq := rfl
  committedDelta := .exact
  committedJournal := .empty
  committedJournal_empty := rfl
}

end RejectedResult

/-- Observable classification of a sealed balance-aware root result. -/
inductive ResultView
    (initialWorld : WorldState)
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation) where
  | rejected (result : RejectedResult initialWorld)
  | execution
      (result :
        OneLevelNestedExecution.Result initialWorld rootContract
          rootInvocation)

/--
A sealed balance-aware run. Rejections can only come from `run`; successful
preflight wraps an already sealed nested execution result.
-/
structure Result
    (initialWorld : WorldState)
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation) where
  private mk ::
  view : ResultView initialWorld rootContract rootInvocation

namespace Result

/-- Internally lift an already sealed nested execution result. -/
private abbrev ofExecution
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result :
      OneLevelNestedExecution.Result initialWorld rootContract
        rootInvocation) :
    Result initialWorld rootContract rootInvocation :=
  ⟨.execution result⟩

/-- The public view determines the sealed wrapper. -/
theorem eq_of_view_eq
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {left right : Result initialWorld rootContract rootInvocation}
    (equal : left.view = right.view) : left = right := by
  cases left
  cases right
  cases equal
  rfl

/-- Observe a terminal or rejected final world; exhaustion has no final world. -/
def finalWorld?
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation) :
    Option WorldState :=
  match result.view with
  | .rejected rejected => some rejected.finalWorld
  | .execution execution =>
      match execution.view with
      | .completed terminal => some terminal.finalWorld
      | .outOfFuel _registry _mode _reachable => none

/--
Observe a preflight failure or a terminal root disposition. Exhaustion remains
`none`, because it is resumable rather than a terminal status.
-/
def terminalStatus?
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation) :
    Option (Except BalanceTransferFailure (FrameOutcome Core.Word)) :=
  match result.view with
  | .rejected rejected => some (.error rejected.failure)
  | .execution execution =>
      match execution.view with
      | .completed terminal => some (.ok terminal.outcome)
      | .outOfFuel _registry _mode _reachable => none

/-- Observe the exact committed endpoint whenever the result is terminal. -/
def committedWorld?
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation) :
    Option (Sigma fun finalWorld =>
      WorldStateDelta initialWorld finalWorld) :=
  match result.view with
  | .rejected rejected =>
      some ⟨rejected.finalWorld, rejected.committedDelta⟩
  | .execution execution =>
      match execution.view with
      | .completed terminal =>
          some ⟨terminal.finalWorld, terminal.committedDelta⟩
      | .outOfFuel _registry _mode _reachable => none

/-- Observe the speculative journal whenever execution is terminal. -/
def workingJournal?
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation) :
    Option TransactionJournal :=
  match result.view with
  | .rejected rejected => some rejected.committedJournal
  | .execution execution =>
      match execution.view with
      | .completed terminal => some terminal.workingJournal
      | .outOfFuel _environment _mode _reachable => none

/-- Observe the root-selected journal whenever the result is terminal. -/
def committedJournal?
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation) :
    Option TransactionJournal :=
  match result.view with
  | .rejected rejected => some rejected.committedJournal
  | .execution execution =>
      match execution.view with
      | .completed terminal => some terminal.committedJournal
      | .outOfFuel _environment _mode _reachable => none

end Result

/--
Execute one checked root with atomic top-level call-value preflight.

Zero value preserves the legacy boundary and does not require a present caller.
Nonzero value either rejects before Core starts or prepares a working world
whose original world remains the scheduler checkpoint.
-/
def runWithEnvironment
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (environment : ExecutionEnvironment)
    (fuel : Nat) :
    Result initialWorld rootContract rootInvocation :=
  if _zero : rootInvocation.callValue = Core.Word.zero then
    Result.ofExecution
      (OneLevelNestedExecution.runWithEnvironment rootContract rootInvocation
        installed environment fuel)
  else
    match transferred :
        initialWorld.transferBalance rootInvocation.caller
          rootInvocation.target rootInvocation.callValue with
    | .error failure =>
        ⟨.rejected (RejectedResult.ofFailure initialWorld failure)⟩
    | .ok _workingWorld =>
        let workingInstalled :=
          WorldState.transferBalance_preserves_installed transferred installed
        Result.ofExecution <|
          OneLevelNestedExecution.runMode environment fuel
            (OneLevelNestedExecution.Mode.preparedRoot rootContract
              rootInvocation workingInstalled)
            (.balancedInitial installed transferred)

/-- Preserve the original calls-only balanced execution API. -/
def run
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (registry : CheckedContractRegistry)
    (fuel : Nat) :
    Result initialWorld rootContract rootInvocation :=
  runWithEnvironment rootContract rootInvocation installed
    (.callsOnly registry) fuel

/-- Resume only the sealed nested execution branch; rejection is terminal. -/
def resumeWithFuel
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (additional : Nat) :
    Result initialWorld rootContract rootInvocation :=
  match result.view with
  | .rejected _rejected => result
  | .execution execution =>
      Result.ofExecution
        (OneLevelNestedExecution.resumeWithFuel execution additional)

end Solcore.ContractRuntime.BalancedTopLevelExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.BalancedTopLevelExecutionProperties`
-/

/-! Branch and exact resumption laws for balance-aware root execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.BalancedTopLevelExecution

/-- Zero value enters the scheduler under the exact fixed environment. -/
theorem runWithEnvironment_of_zero_value
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (environment : ExecutionEnvironment)
    (fuel : Nat)
    (zero : rootInvocation.callValue = Core.Word.zero) :
    (runWithEnvironment rootContract rootInvocation installed environment fuel).view =
      .execution
        (OneLevelNestedExecution.runWithEnvironment rootContract rootInvocation
          installed environment fuel) := by
  simp [runWithEnvironment, zero]

/-- A failed preflight rejects without replacing or consulting the environment. -/
theorem runWithEnvironment_of_transfer_failure
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (environment : ExecutionEnvironment)
    (fuel : Nat)
    (failure : BalanceTransferFailure)
    (nonzero : rootInvocation.callValue ≠ Core.Word.zero)
    (failed :
      initialWorld.transferBalance rootInvocation.caller
          rootInvocation.target rootInvocation.callValue =
        .error failure) :
    (runWithEnvironment rootContract rootInvocation installed environment fuel).view =
      .rejected (RejectedResult.ofFailure initialWorld failure) := by
  unfold runWithEnvironment
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

/-- A successful preflight enters the prepared root under the same environment. -/
theorem runWithEnvironment_of_transfer_success
    {initialWorld workingWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (environment : ExecutionEnvironment)
    (fuel : Nat)
    (nonzero : rootInvocation.callValue ≠ Core.Word.zero)
    (transferred :
      initialWorld.transferBalance rootInvocation.caller
          rootInvocation.target rootInvocation.callValue =
        .ok workingWorld) :
    (runWithEnvironment rootContract rootInvocation installed environment fuel).view =
      .execution
        (OneLevelNestedExecution.runMode environment fuel
          (OneLevelNestedExecution.Mode.preparedRoot rootContract
            rootInvocation
            (WorldState.transferBalance_preserves_installed transferred
              installed))
          (.balancedInitial installed transferred)) := by
  unfold runWithEnvironment
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

/-- Splitting fuel preserves one fixed environment and never repeats preflight. -/
theorem resumeWithFuel_runWithEnvironment
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (environment : ExecutionEnvironment)
    (fuel additional : Nat) :
    resumeWithFuel
        (runWithEnvironment rootContract rootInvocation installed environment fuel)
        additional =
      runWithEnvironment rootContract rootInvocation installed environment
        (fuel + additional) := by
  unfold runWithEnvironment
  split
  · apply Result.eq_of_view_eq
    simp [resumeWithFuel,
      OneLevelNestedExecution.resumeWithFuel_runWithEnvironment]
  · split
    · rfl
    · apply Result.eq_of_view_eq
      simp [resumeWithFuel,
        OneLevelNestedExecution.resumeWithFuel_runMode]

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

end Solcore.ContractRuntime.BalancedTopLevelExecution
end
