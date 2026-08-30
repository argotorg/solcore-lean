import Solcore.Core.HostRunnerProperties
import Solcore.Semantics.CheckedCoreWordOutcomeProperties
import Solcore.Semantics.ContractCallFailure
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

namespace ChildFrame

/-- Strictly decode a typed child state reported done, retaining its Word. -/
def outcomeDone
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : ChildFrame initialWorld rootContract rootInvocation)
    (value : Core.Value)
    (advanced : Core.hostAdvance frame.childState = .done value) :
    CheckedCoreWordOutcome := by
  have decodedNeNone :
      frame.childContract.decodeWordOutcome? value ≠ none := by
    obtain ⟨store, stateEq⟩ := Core.hostAdvance_done_iff.mp advanced
    have typing := frame.childStateTyping
    rw [stateEq] at typing
    cases typing with
    | ret _storeTyping valueTyping continuationTyping =>
        cases continuationTyping with
        | nil =>
            apply CoreContractEntryProfile.decodeWordOutcome?_ne_none_of_hasType
            rw [← frame.childContract.resultType_eq]
            exact valueTyping
  match decodedEq : frame.childContract.decodeWordOutcome? value with
  | some outcome => exact outcome
  | none => exact False.elim (decodedNeNone decodedEq)

end ChildFrame

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

/-- Intercept a root call, or delegate every other request to the flat handler. -/
def RootFrame.afterSuspension
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : CheckedContractRegistry)
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (suspension : Core.HostSuspension)
    (advanced : Core.hostAdvance frame.state = .suspended suspension) :
    Mode initialWorld rootContract rootInvocation := by
  rcases suspension with ⟨request, continuation, store⟩
  cases request with
  | callContractWord target input =>
      let suspended :=
        frame.suspendCall target input continuation store advanced
      match addressEq : wordToAddress? target with
      | none =>
          exact .root
            (suspended.resumeWith suspended.parentContext
              ContractCallFailure.invalidAddress.result)
      | some address =>
          match resolvedEq :
              registry.resolve?
                suspended.parentContext.context.values.working.1 address with
          | none =>
              exact .root
                (suspended.resumeWith suspended.parentContext
                  ContractCallFailure.unavailable.result)
          | some resolved =>
              exact .child (suspended.startChild address addressEq resolved)
  | storageRead slot =>
      exact .root (frame.afterHandledSuspension
        ⟨.storageRead slot, continuation, store⟩ advanced)
  | storageWrite slot value =>
      exact .root (frame.afterHandledSuspension
        ⟨.storageWrite slot value, continuation, store⟩ advanced)
  | storageAddress =>
      exact .root (frame.afterHandledSuspension
        ⟨.storageAddress, continuation, store⟩ advanced)
  | codeAddress =>
      exact .root (frame.afterHandledSuspension
        ⟨.codeAddress, continuation, store⟩ advanced)
  | callValue =>
      exact .root (frame.afterHandledSuspension
        ⟨.callValue, continuation, store⟩ advanced)
  | callerAddress =>
      exact .root (frame.afterHandledSuspension
        ⟨.callerAddress, continuation, store⟩ advanced)
  | inputDataByte? offset =>
      exact .root (frame.afterHandledSuspension
        ⟨.inputDataByte? offset, continuation, store⟩ advanced)
  | inputDataSize =>
      exact .root (frame.afterHandledSuspension
        ⟨.inputDataSize, continuation, store⟩ advanced)
  | inputDataWordBE? offset =>
      exact .root (frame.afterHandledSuspension
        ⟨.inputDataWordBE? offset, continuation, store⟩ advanced)
  | currentAddress =>
      exact .root (frame.afterHandledSuspension
        ⟨.currentAddress, continuation, store⟩ advanced)

/-- Run both modes with one budget; no child-local fuel is hidden. -/
def runMode
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : CheckedContractRegistry) :
    (fuel : Nat) →
    Mode initialWorld rootContract rootInvocation →
    Result initialWorld rootContract rootInvocation
  | fuel, .root frame =>
      match advanced : Core.hostAdvance frame.state with
      | .done value => .completed (frame.finalizeDone value advanced)
      | .fault error =>
          False.elim
            (Core.well_typed_host_state_never_faults
              frame.stateTyping advanced)
      | .next next =>
          match fuel with
          | 0 => .outOfFuel registry (.root frame)
          | remaining + 1 =>
              runMode registry remaining (.root (frame.afterNext next advanced))
      | .suspended suspension =>
          match fuel with
          | 0 => .outOfFuel registry (.root frame)
          | remaining + 1 =>
              runMode registry remaining
                (frame.afterSuspension registry suspension advanced)
  | fuel, .child frame =>
      match advanced : Core.hostAdvance frame.childState with
      | .done value =>
          runMode registry fuel
            (.root (frame.resumeRoot (frame.outcomeDone value advanced)))
      | .fault error =>
          False.elim
            (Core.well_typed_host_state_never_faults
              frame.childStateTyping advanced)
      | .next next =>
          match fuel with
          | 0 => .outOfFuel registry (.child frame)
          | remaining + 1 =>
              runMode registry remaining (.child (frame.afterNext next advanced))
      | .suspended suspension =>
          match fuel with
          | 0 => .outOfFuel registry (.child frame)
          | remaining + 1 =>
              runMode registry remaining
                (.child (frame.afterHandledSuspension suspension advanced))
termination_by fuel mode => fuel * 2 + mode.rank
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

end Solcore.Semantics.OneLevelNestedExecution
