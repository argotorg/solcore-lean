import Solcore.Core.HostRunnerProperties
import Solcore.Semantics.OneLevelNestedExecutionResult
import Solcore.Semantics.OneLevelNestedExecutionReachabilityProperties
import Solcore.Semantics.OneLevelNestedExecutionTransitions

/-! Shared-fuel execution for one root and one active leaf child. -/

set_option autoImplicit false

namespace Solcore.Semantics.OneLevelNestedExecution

namespace RootFrame

/-- Finalize one typed root value under the root-owned completion convention. -/
def finalize
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (value : Core.Value)
    (store : Core.Store)
    (outcome : FrameOutcome Core.Word) :
    TerminalResult initialWorld rootContract rootInvocation :=
  let workingWorld := frame.context.context.values.working.1
  let finalWorld :=
    match outcome with
    | .returned _ => workingWorld
    | .reverted _ => initialWorld
    | .trapped _ => initialWorld
  let workingJournal := frame.context.workingJournal
  let committedJournal :=
    match outcome with
    | .returned _ => workingJournal
    | .reverted _ => frame.context.context.values.checkpoint.effects.rollback
    | .trapped _ => frame.context.context.values.checkpoint.effects.rollback
  {
    terminalContext := frame.context
    coreValue := value
    coreStore := store
    outcome := outcome
    finalWorld := finalWorld
    workingJournal := workingJournal
    workingJournal_eq := rfl
    committedJournal := committedJournal
    committedJournal_eq := by cases outcome <;> rfl
    workingDelta := .exact
    committedDelta := .exact
  }

/-- A typed root state reported done has the exact data needed for finalization. -/
def finalizeDone
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (value : Core.Value)
    (advanced : Core.hostAdvance frame.state = .done value) :
    TerminalResult initialWorld rootContract rootInvocation := by
  have decodedNeNone : rootContract.decodeCompletion? value ≠ none := by
    obtain ⟨store, stateEq⟩ := Core.hostAdvance_done_iff.mp advanced
    have typing := frame.stateTyping
    rw [stateEq] at typing
    cases typing with
    | ret _storeTyping valueTyping continuationTyping =>
        cases continuationTyping with
        | nil =>
            apply rootContract.entryProfile.decode?_ne_none_of_hasType
            rw [← rootContract.resultType_eq]
            exact valueTyping
  match decodedEq : rootContract.decodeCompletion? value with
  | some outcome =>
      exact frame.finalize value frame.state.store outcome
  | none => exact False.elim (decodedNeNone decodedEq)

end RootFrame

/--
One bounded execution result. The private constructor makes `run` and
`resumeWithFuel` the only production paths; callers can inspect `view` but
cannot wrap an arbitrary terminal value or replace a retained environment.
-/
structure Result
    (initialWorld : WorldState)
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation) where
  private mk ::
  view : ResultView initialWorld rootContract rootInvocation

/-- The observable view determines a sealed result without exposing its constructor. -/
theorem Result.eq_of_view_eq
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {left right : Result initialWorld rootContract rootInvocation}
    (equal : left.view = right.view) : left = right := by
  cases left
  cases right
  cases equal
  rfl

/-- Run both modes with one budget; no child-local fuel is hidden. -/
def runMode
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (environment : ExecutionEnvironment) :
    (fuel : Nat) →
    (mode : Mode initialWorld rootContract rootInvocation) →
    Reachable environment mode →
    Result initialWorld rootContract rootInvocation
  | fuel, .root frame, reachable =>
      match advanced : Core.hostAdvance frame.state with
      | .done value => ⟨.completed (frame.finalizeDone value advanced)⟩
      | .fault error =>
          False.elim
            (Core.well_typed_host_state_never_faults
              frame.stateTyping advanced)
      | .next next =>
          match fuel with
          | 0 => ⟨.outOfFuel environment (.root frame) reachable⟩
          | remaining + 1 =>
              runMode environment remaining
                (.root (frame.afterNext next advanced))
                (.rootNext reachable advanced)
      | .suspended suspension =>
          match fuel with
          | 0 => ⟨.outOfFuel environment (.root frame) reachable⟩
          | remaining + 1 =>
              have creatorAddress_eq :
                  rootInvocation.executionInputs.currentAddress =
                    frame.context.context.storageAddress := by
                rw [TopLevelInvocation.executionInputs_currentAddress]
                exact reachable.root_storageAddress.symm
              runMode environment remaining
                (frame.afterSuspensionWithEnvironment environment
                  creatorAddress_eq suspension advanced)
                (.rootSuspended reachable creatorAddress_eq advanced)
  | fuel, .child frame, reachable =>
      match advanced : Core.hostAdvance frame.childState with
      | .done value =>
          runMode environment fuel
            (.root (frame.resumeRoot (frame.outcomeDone value advanced)))
            (.childDone reachable advanced)
      | .fault error =>
          False.elim
            (Core.well_typed_host_state_never_faults
              frame.childStateTyping advanced)
      | .next next =>
          match fuel with
          | 0 => ⟨.outOfFuel environment (.child frame) reachable⟩
          | remaining + 1 =>
              runMode environment remaining
                (.child (frame.afterNext next advanced))
                (.childNext reachable advanced)
      | .suspended suspension =>
          match fuel with
          | 0 => ⟨.outOfFuel environment (.child frame) reachable⟩
          | remaining + 1 =>
              runMode environment remaining
                (.child (frame.afterHandledSuspension suspension advanced))
                (.childSuspended reachable advanced)
  | fuel, .initializer frame, reachable =>
      match advanced : Core.hostAdvance frame.initializerState with
      | .done value =>
          let completion := frame.complete (frame.outcomeDone value advanced)
          runMode environment fuel (.root completion.root)
            (.initializerDone reachable advanced)
      | .fault error =>
          False.elim
            (Core.well_typed_host_state_never_faults
              frame.initializerStateTyping advanced)
      | .next next =>
          match fuel with
          | 0 => ⟨.outOfFuel environment (.initializer frame) reachable⟩
          | remaining + 1 =>
              runMode environment remaining
                (.initializer (frame.afterNext next advanced))
                (.initializerNext reachable advanced)
      | .suspended suspension =>
          match fuel with
          | 0 => ⟨.outOfFuel environment (.initializer frame) reachable⟩
          | remaining + 1 =>
              runMode environment remaining
                (.initializer
                  (frame.afterHandledSuspension suspension advanced))
                (.initializerSuspended reachable advanced)
termination_by fuel mode _ => fuel * 2 + mode.rank
decreasing_by
  · simp [Mode.rank]
  · have bounded :=
      Mode.rank_le_one
        (frame.afterSuspensionWithEnvironment environment creatorAddress_eq
          suspension advanced)
    simp [Mode.rank] at bounded ⊢
    omega
  · simp [Mode.rank]
  · simp [Mode.rank]
  · simp [Mode.rank]
  · simp [Mode.rank]
  · simp [Mode.rank]
  · simp [Mode.rank]

/-- Execute an installed checked root with dynamic depth-one child dispatch. -/
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
  runMode environment fuel
    (Mode.initialRoot rootContract rootInvocation installed)
    (.initial installed)

/-- Low-level calls-only compatibility wrapper. -/
def runModeCallsOnly
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : CheckedContractRegistry)
    (fuel : Nat)
    (mode : Mode initialWorld rootContract rootInvocation)
    (reachable : Reachable (.callsOnly registry) mode) :
    Result initialWorld rootContract rootInvocation :=
  runMode (.callsOnly registry) fuel mode reachable

/-- Explicit name for the canonical fixed-environment scheduler. -/
abbrev runModeWithEnvironment := @runMode

/-- Preserve the original calls-only execution API. -/
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

end Solcore.Semantics.OneLevelNestedExecution
