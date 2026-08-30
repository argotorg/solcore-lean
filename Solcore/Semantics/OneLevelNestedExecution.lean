import Solcore.Core.HostRunnerProperties
import Solcore.Semantics.OneLevelNestedExecutionResult
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
  {
    terminalContext := frame.context
    coreValue := value
    coreStore := store
    outcome := outcome
    finalWorld := finalWorld
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

/-- Administrative rank used with shared fuel to justify mode switching. -/
def Mode.rank
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation} :
    Mode initialWorld rootContract rootInvocation → Nat
  | .root _ => 0
  | .child _ => 1

theorem Mode.rank_le_one
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (mode : Mode initialWorld rootContract rootInvocation) :
    mode.rank ≤ 1 := by
  cases mode <;> simp [Mode.rank]

/-- Run both modes with one budget; no child-local fuel is hidden. -/
def runMode
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : CheckedContractRegistry) :
    (fuel : Nat) →
    (mode : Mode initialWorld rootContract rootInvocation) →
    Reachable registry mode →
    Result initialWorld rootContract rootInvocation
  | fuel, .root frame, reachable =>
      match advanced : Core.hostAdvance frame.state with
      | .done value => .completed (frame.finalizeDone value advanced)
      | .fault error =>
          False.elim
            (Core.well_typed_host_state_never_faults
              frame.stateTyping advanced)
      | .next next =>
          match fuel with
          | 0 => .outOfFuel registry (.root frame) reachable
          | remaining + 1 =>
              runMode registry remaining
                (.root (frame.afterNext next advanced))
                (.rootNext reachable advanced)
      | .suspended suspension =>
          match fuel with
          | 0 => .outOfFuel registry (.root frame) reachable
          | remaining + 1 =>
              runMode registry remaining
                (frame.afterSuspension registry suspension advanced)
                (.rootSuspended reachable advanced)
  | fuel, .child frame, reachable =>
      match advanced : Core.hostAdvance frame.childState with
      | .done value =>
          runMode registry fuel
            (.root (frame.resumeRoot (frame.outcomeDone value advanced)))
            (.childDone reachable advanced)
      | .fault error =>
          False.elim
            (Core.well_typed_host_state_never_faults
              frame.childStateTyping advanced)
      | .next next =>
          match fuel with
          | 0 => .outOfFuel registry (.child frame) reachable
          | remaining + 1 =>
              runMode registry remaining
                (.child (frame.afterNext next advanced))
                (.childNext reachable advanced)
      | .suspended suspension =>
          match fuel with
          | 0 => .outOfFuel registry (.child frame) reachable
          | remaining + 1 =>
              runMode registry remaining
                (.child (frame.afterHandledSuspension suspension advanced))
                (.childSuspended reachable advanced)
termination_by fuel mode _ => fuel * 2 + mode.rank
decreasing_by
  · simp [Mode.rank]
  · have bounded :=
      Mode.rank_le_one
        (frame.afterSuspension registry suspension advanced)
    simp [Mode.rank] at bounded ⊢
    omega
  · simp [Mode.rank]
  · simp [Mode.rank]
  · simp [Mode.rank]

/-- Execute an installed checked root with dynamic depth-one child dispatch. -/
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
  runMode registry fuel
    (Mode.initialRoot rootContract rootInvocation installed)
    (.initial installed)

end Solcore.Semantics.OneLevelNestedExecution
