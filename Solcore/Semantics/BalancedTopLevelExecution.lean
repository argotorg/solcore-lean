import Solcore.Semantics.BalanceTransferInstallationProperties
import Solcore.Semantics.OneLevelNestedExecutionResumption
import Solcore.Semantics.WorldStateDelta

/-! Total top-level value preflight wrapped around the nested checked runner. -/

set_option autoImplicit false

namespace Solcore.Semantics.BalancedTopLevelExecution

/-- A pre-execution transfer rejection with an exact identity commit. -/
structure RejectedResult (initialWorld : WorldState) where
  failure : BalanceTransferFailure
  finalWorld : WorldState
  finalWorld_eq : finalWorld = initialWorld
  committedDelta : WorldStateDelta initialWorld finalWorld

namespace RejectedResult

/-- Build the canonical no-execution rejection for one explicit world. -/
def ofFailure
    (initialWorld : WorldState)
    (failure : BalanceTransferFailure) : RejectedResult initialWorld := {
  failure := failure
  finalWorld := initialWorld
  finalWorld_eq := rfl
  committedDelta := .exact
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

end Solcore.Semantics.BalancedTopLevelExecution
