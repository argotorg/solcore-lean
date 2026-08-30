import Solcore.Core.HostRunnerProperties
import Solcore.Core.HostTransitionSafety
import Solcore.Semantics.CheckedCoreWordOutcomeProperties
import Solcore.Semantics.CheckedContractRegistry
import Solcore.Semantics.ContractCallFailure
import Solcore.Semantics.HostStorageAccountPresence
import Solcore.Semantics.OneLevelNestedExecutionState

/-! Proof-preserving local transitions for the one-level nested scheduler. -/

set_option autoImplicit false

namespace Solcore.Semantics.OneLevelNestedExecution

namespace RootFrame

/-- Advance one ordinary typed Core transition without changing host state. -/
def afterNext
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (next : Core.State)
    (advanced : Core.hostAdvance frame.state = .next next) :
    RootFrame initialWorld rootContract rootInvocation := {
  context := frame.context
  state := next
  stateTyping :=
    Core.hostAdvance_next_preserves_state_type frame.stateTyping advanced
}

/-- Handle one non-intercepted root request and resume its exact continuation. -/
def afterHandledSuspension
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (suspension : Core.HostSuspension)
    (advanced : Core.hostAdvance frame.state = .suspended suspension) :
    RootFrame initialWorld rootContract rootInvocation :=
  let requestResult :=
    HostStorageDriver.handleRequest rootInvocation.executionInputs
      frame.context suspension.request
  let suspensionTyping :=
    Core.hostAdvance_suspended_hasType frame.stateTyping advanced
  {
    context := requestResult.1
    state := suspension.resume requestResult.2
    stateTyping := suspensionTyping.resume requestResult.2
  }

/-- Retain an intercepted root call before any response is delivered. -/
def suspendCall
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (target input : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (advanced :
      Core.hostAdvance frame.state =
        .suspended
          ⟨.callContractWord target input, continuation, store⟩) :
    SuspendedRoot initialWorld rootContract rootInvocation := {
  parentContext := frame.context
  callTarget := target
  callInput := input
  continuation := continuation
  store := store
  suspensionTyping :=
    Core.hostAdvance_suspended_hasType frame.stateTyping advanced
}

end RootFrame

namespace SuspendedRoot

/-- Resume the exact root call suspension against a selected parent context. -/
def resumeWith
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (root : SuspendedRoot initialWorld rootContract rootInvocation)
    (context : HostStorageDriver.Context Unit Unit)
    (response : Core.ContractCallWordResult) :
    RootFrame initialWorld rootContract rootInvocation := {
  context := context
  state := root.suspension.resume response
  stateTyping := root.suspensionTyping.resume response
}

/-- Start the exact resolved child at the root's current working world. -/
def startChild
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (root : SuspendedRoot initialWorld rootContract rootInvocation)
    (target : Address)
    (targetAddress_eq : wordToAddress? root.callTarget = some target)
    (resolved :
      CheckedContractRegistry.Resolution
        root.parentContext.context.values.working.1 target) :
    ChildFrame initialWorld rootContract rootInvocation :=
  let invocation :=
    TopLevelInvocation.childWord rootInvocation.executionInputs target
      root.callInput
  let childContext := TopLevelExecution.initialContext resolved.2
  {
    suspendedRoot := root
    childTarget := target
    targetAddress_eq := targetAddress_eq
    childContract := resolved.1
    childInvocation := invocation
    installed := resolved.2
    childInvocation_eq := rfl
    childContext := childContext
    childState :=
      Core.State.initial resolved.1.code.program.body Core.hostEnvironment
    childStateTyping := resolved.1.code.initialState_hasType
    parentStorageAccount := root.parentContext.storageAccount
    parentStorageAccount_present := by
      simpa [childContext, TopLevelExecution.initialContext,
        TopLevelExecution.initialValues] using
          root.parentContext.storageAccount_present
  }

end SuspendedRoot

namespace RootFrame

/-- Intercept a root call, or delegate every other request to the flat handler. -/
def afterSuspension
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

/-- Advance one ordinary child Core transition without changing host state. -/
def afterNext
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : ChildFrame initialWorld rootContract rootInvocation)
    (next : Core.State)
    (advanced : Core.hostAdvance frame.childState = .next next) :
    ChildFrame initialWorld rootContract rootInvocation := {
  frame with
  childState := next
  childStateTyping :=
    Core.hostAdvance_next_preserves_state_type frame.childStateTyping advanced
}

/-- Handle one child request, including the flat handler's depth-limit reply. -/
def afterHandledSuspension
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : ChildFrame initialWorld rootContract rootInvocation)
    (suspension : Core.HostSuspension)
    (advanced : Core.hostAdvance frame.childState = .suspended suspension) :
    ChildFrame initialWorld rootContract rootInvocation :=
  let requestResult :=
    HostStorageDriver.handleRequest frame.childInvocation.executionInputs
      frame.childContext suspension.request
  let suspensionTyping :=
    Core.hostAdvance_suspended_hasType frame.childStateTyping advanced
  let parentPresence :
      PresentAccountAt frame.childContext.context.values.working.1
        frame.suspendedRoot.parentContext.context.storageAddress :=
    ⟨frame.parentStorageAccount, frame.parentStorageAccount_present⟩
  let nextPresence := parentPresence.afterHandleRequest
    frame.childInvocation.executionInputs frame.childContext
      suspension.request
      frame.suspendedRoot.parentContext.context.storageAddress
  {
    frame with
    childContext := requestResult.1
    childState := suspension.resume requestResult.2
    childStateTyping := suspensionTyping.resume requestResult.2
    parentStorageAccount := nextPresence.account
    parentStorageAccount_present := nextPresence.present
  }

/-- Select the child-call checkpoint or returned working world for the parent. -/
def selectedParentContext
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : ChildFrame initialWorld rootContract rootInvocation) :
    CheckedCoreWordOutcome → HostStorageDriver.Context Unit Unit
  | .returned _ =>
      frame.suspendedRoot.parentContext.rebaseWorking
        frame.childContext.context.values.working.1
        frame.parentStorageAccount frame.parentStorageAccount_present
  | .reverted _ => frame.suspendedRoot.parentContext
  | .trapped _ => frame.suspendedRoot.parentContext

/-- Deliver one exact terminal child disposition to the suspended root. -/
def resumeRoot
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : ChildFrame initialWorld rootContract rootInvocation)
    (outcome : CheckedCoreWordOutcome) :
    RootFrame initialWorld rootContract rootInvocation :=
  frame.suspendedRoot.resumeWith (frame.selectedParentContext outcome)
    outcome.toContractCallResult

end ChildFrame

end Solcore.Semantics.OneLevelNestedExecution
