import Solcore.Core.HostRunnerProperties
import Solcore.Core.HostTransitionSafety
import Solcore.Semantics.CheckedCoreWordOutcomeProperties
import Solcore.Semantics.CheckedContractRegistry
import Solcore.Semantics.BalanceTransferCallFailure
import Solcore.Semantics.BalanceTransferInstallationProperties
import Solcore.Semantics.BalanceTransferPresenceProperties
import Solcore.Semantics.ContractCallFailure
import Solcore.Semantics.ExecutionEnvironment
import Solcore.Semantics.HostStorageAccountPresence
import Solcore.Semantics.CheckedCreationPreflightFailure
import Solcore.Semantics.OneLevelNestedCreationTransitions
import Solcore.Semantics.OneLevelNestedExecutionMode

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
    (call : CallProfile)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (advanced :
      Core.hostAdvance frame.state =
        .suspended
          ⟨call.request, continuation, store⟩) :
    SuspendedRoot initialWorld rootContract rootInvocation := {
  parentContext := frame.context
  call := call
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
  state := root.suspension.resume (root.call.response response)
  stateTyping := root.suspensionTyping.resume (root.call.response response)
}

/-- Start the exact resolved child at the root's current working world. -/
def startChild
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (root : SuspendedRoot initialWorld rootContract rootInvocation)
    (target : Address)
    (targetAddress_eq : wordToAddress? root.call.target = some target)
    (childContract : CheckedCoreContract)
    (preTransferInstalled : InstalledCheckedCoreContract
      root.parentContext.context.values.working.1 target childContract)
    (childInitialWorld : WorldState)
    (installed : InstalledCheckedCoreContract childInitialWorld target childContract)
    (parentPresence : PresentAccountAt childInitialWorld
      root.parentContext.context.storageAddress) :
    ChildFrame initialWorld rootContract rootInvocation :=
  let invocation := root.call.invocation rootInvocation.executionInputs target
  let childContext := TopLevelExecution.initialContext installed
  {
    suspendedRoot := root
    childTarget := target
    targetAddress_eq := targetAddress_eq
    childContract := childContract
    preTransferInstalled := preTransferInstalled
    childInitialWorld := childInitialWorld
    childInvocation := invocation
    installed := installed
    childInvocation_eq := rfl
    childContext := childContext
    childState :=
      Core.State.initial childContract.code.program.body Core.hostEnvironment
    childStateTyping := childContract.code.initialState_hasType
    parentStorageAccount := parentPresence.account
    parentStorageAccount_present := by
      simpa [childContext, TopLevelExecution.initialContext,
        TopLevelExecution.initialValues] using
          parentPresence.present
  }

end SuspendedRoot

namespace RootFrame

/-- Intercept a root call, or delegate every other request to the flat handler. -/
def afterSuspensionWithEnvironment
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (environment : ExecutionEnvironment)
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (creatorAddress_eq : rootInvocation.executionInputs.currentAddress =
      frame.context.context.storageAddress)
    (suspension : Core.HostSuspension)
    (advanced : Core.hostAdvance frame.state = .suspended suspension) :
    Mode initialWorld rootContract rootInvocation := by
  rcases suspension with ⟨request, continuation, store⟩
  cases request with
  | callContractWord target input =>
      let suspended :=
        frame.suspendCall (.legacy target input) continuation store advanced
      match addressEq : wordToAddress? target with
      | none =>
          exact .root
            (suspended.resumeWith suspended.parentContext
              ContractCallFailure.invalidAddress.result)
      | some address =>
          match resolvedEq :
              environment.callRegistry.resolve?
                suspended.parentContext.context.values.working.1 address with
          | none =>
              exact .root
                (suspended.resumeWith suspended.parentContext
                  ContractCallFailure.unavailable.result)
          | some resolved =>
              exact .child (suspended.startChild address addressEq resolved.1 resolved.2
                suspended.parentContext.context.values.working.1 resolved.2
                suspended.parentContext.selectedPresence)
  | callContractWordWithValue target value input =>
      let suspended :=
        frame.suspendCall (.withValue target value input)
          continuation store advanced
      match addressEq : wordToAddress? target with
      | none =>
          exact .root
            (suspended.resumeWith suspended.parentContext
              ContractCallFailure.invalidAddress.result)
      | some address =>
          match resolvedEq : environment.callRegistry.resolve?
              suspended.parentContext.context.values.working.1 address with
          | none =>
              exact .root
                (suspended.resumeWith suspended.parentContext
                  ContractCallFailure.unavailable.result)
          | some resolved =>
              match transferred :
                  suspended.parentContext.context.values.working.1.transferBalance
                    suspended.parentContext.context.storageAddress address value with
              | .error failure =>
                  exact .root
                    (suspended.resumeWith suspended.parentContext
                      failure.toContractCallResult)
              | .ok childWorld =>
                  let installed :=
                    WorldState.transferBalance_preserves_installed transferred
                      resolved.2
                  let parentPresence :=
                    WorldState.transferBalance_preserves_present transferred
                      suspended.parentContext.selectedPresence
                  exact .child (suspended.startChild address addressEq resolved.1 resolved.2
                    childWorld installed parentPresence)
  | createContractWord templateId value input =>
      let profile : CreationProfile := ⟨templateId, value, input⟩
      let suspended :=
        frame.suspendCreation profile continuation store advanced
      match prepared : CheckedCreationPreflight.prepare
          suspended.parentContext.context.values.working.1 environment
          rootInvocation.executionInputs.currentAddress templateId value with
      | .error failure =>
          exact .root
            (suspended.resumeWith suspended.parentContext
              failure.toContractCallResult)
      | .ok creation =>
          exact .initializer
            (suspended.startInitializer environment creation creatorAddress_eq)
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

/-- Preserve the calls-only registry boundary while environments are adopted. -/
def afterSuspension
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : CheckedContractRegistry)
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (creatorAddress_eq : rootInvocation.executionInputs.currentAddress =
      frame.context.context.storageAddress)
    (suspension : Core.HostSuspension)
    (advanced : Core.hostAdvance frame.state = .suspended suspension) :
    Mode initialWorld rootContract rootInvocation :=
  frame.afterSuspensionWithEnvironment (.callsOnly registry) creatorAddress_eq
    suspension advanced

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
