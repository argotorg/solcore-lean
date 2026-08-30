import Solcore.Core.HostRunnerProperties
import Solcore.Core.HostTransitionSafety
import Solcore.Semantics.CheckedCoreWordOutcomeProperties
import Solcore.Semantics.BalanceTransferPresenceProperties
import Solcore.Semantics.CheckedAccountCreationProperties
import Solcore.Semantics.HostStorageAccountPresence
import Solcore.Semantics.OneLevelNestedCreationState
import Solcore.Semantics.WorldStateCodeWriteProperties

/-! Lifecycle helpers for one prepared checked contract initializer. -/

set_option autoImplicit false

namespace Solcore.Semantics.OneLevelNestedExecution

private theorem handleRequest_storageAddress
    {RollbackState TraceState : Type}
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (request : Core.HostRequest) :
    (HostStorageDriver.handleRequest inputs context request).1.context.storageAddress =
      context.context.storageAddress := by
  cases request <;> rfl

private theorem handleRequest_checkpointState
    {RollbackState TraceState : Type}
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (request : Core.HostRequest) :
    (HostStorageDriver.handleRequest inputs context request).1.context.values.checkpoint.state =
      context.context.values.checkpoint.state := by
  cases request <;> rfl

namespace RootFrame

def suspendCreation
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (profile : CreationProfile) (continuation : List Core.Frame)
    (store : Core.Store)
    (advanced : Core.hostAdvance frame.state = .suspended
      ⟨profile.request, continuation, store⟩) :
    SuspendedCreationRoot initialWorld rootContract rootInvocation := {
  parentContext := frame.context
  profile := profile
  continuation := continuation
  store := store
  suspensionTyping :=
    Core.hostAdvance_suspended_hasType frame.stateTyping advanced
}

end RootFrame

namespace SuspendedCreationRoot

def resumeWith
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (root : SuspendedCreationRoot initialWorld rootContract rootInvocation)
    (context : TransactionHostStorageDriver.Context)
    (response : Core.ContractCallWordResult) :
    RootFrame initialWorld rootContract rootInvocation := {
  context := context
  state := root.suspension.resume (root.profile.response response)
  stateTyping := root.suspensionTyping.resume (root.profile.response response)
}

def startInitializer
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (root : SuspendedCreationRoot initialWorld rootContract rootInvocation)
    (environment : ExecutionEnvironment)
    (prepared : PreparedCheckedCreation
      root.parentContext.context.values.working.1 environment
      rootInvocation.executionInputs.currentAddress root.profile.templateId
      root.profile.value)
    (creatorAddress_eq : rootInvocation.executionInputs.currentAddress =
      root.parentContext.context.storageAddress) :
    PreparedInitializerFrame initialWorld rootContract rootInvocation := by
  let statePreparation := prepared.statePreparation
  have created_ne_creator :
      statePreparation.createdAddress ≠
        rootInvocation.executionInputs.currentAddress :=
    CheckedAccountCreation.PreparedAccountCreation.created_ne_creator
      statePreparation
  have postNonceCreator :
      statePreparation.postNonceWorld.account?
          rootInvocation.executionInputs.currentAddress =
        some statePreparation.incrementedCreator :=
    CheckedAccountCreation.PreparedAccountCreation.postNonce_creator
      statePreparation
  let postNoncePresence : PresentAccountAt statePreparation.postNonceWorld
      root.parentContext.context.storageAddress :=
    ⟨statePreparation.incrementedCreator, by
      rw [← creatorAddress_eq]
      exact postNonceCreator⟩
  let postNonceContext := root.parentContext.rebaseFromPresence
    statePreparation.postNonceWorld postNoncePresence
  have provisionalCreator :
      statePreparation.provisionalWorld.account?
          rootInvocation.executionInputs.currentAddress =
        some statePreparation.incrementedCreator := by
    rw [statePreparation.provisionalWorld_eq]
    rw [WorldState.account?_putAccount_other _ statePreparation.createdAddress
      rootInvocation.executionInputs.currentAddress _
      (Ne.symm created_ne_creator)]
    exact postNonceCreator
  let provisionalPresence : PresentAccountAt statePreparation.provisionalWorld
      rootInvocation.executionInputs.currentAddress :=
    ⟨statePreparation.incrementedCreator, provisionalCreator⟩
  let initializerParentPresence :=
    WorldState.transferBalance_preserves_present statePreparation.transfer_eq
      provisionalPresence
  let invocation := root.profile.initializerInvocation
    rootInvocation.executionInputs prepared.createdAddress
  let initializerContext := TopLevelExecution.preparedTransactionContext
    (checkpointWorld := statePreparation.postNonceWorld)
    statePreparation.initializerInstalled
  exact {
    suspendedRoot := root
    environment := environment
    prepared := prepared
    creatorAddress_eq := creatorAddress_eq
    initializerInvocation := invocation
    initializerInvocation_eq := rfl
    postNonceParentContext := postNonceContext
    postNonce_storageAddress_eq := rfl
    postNonce_workingWorld_eq := rfl
    postNonce_checkpoint_eq := rfl
    initializerContext := initializerContext
    initializer_storageAddress_eq := by
      simpa [initializerContext,
        TopLevelExecution.preparedTransactionContext,
        TopLevelExecution.preparedTransactionValues] using
        prepared.preparation_address_eq
    initializer_checkpointState_eq := rfl
    initializerState := Core.State.initial
      prepared.template.initializer.code.program.body Core.hostEnvironment
    initializerStateTyping :=
      prepared.template.initializer.code.initialState_hasType
    parentAccount := initializerParentPresence.account
    parentAccount_present := by
      rw [← creatorAddress_eq]
      simpa [initializerContext,
        TopLevelExecution.preparedTransactionContext,
        TopLevelExecution.preparedTransactionValues,
        TopLevelExecution.preparedTransactionValuesWithJournals] using
          initializerParentPresence.present
  }

end SuspendedCreationRoot

namespace PreparedInitializerFrame

def afterNext
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : PreparedInitializerFrame initialWorld rootContract rootInvocation)
    (next : Core.State)
    (advanced : Core.hostAdvance frame.initializerState = .next next) :
    PreparedInitializerFrame initialWorld rootContract rootInvocation := {
  frame with
  initializerState := next
  initializerStateTyping :=
    Core.hostAdvance_next_preserves_state_type frame.initializerStateTyping
      advanced
}

def afterHandledSuspension
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : PreparedInitializerFrame initialWorld rootContract rootInvocation)
    (suspension : Core.HostSuspension)
    (advanced : Core.hostAdvance frame.initializerState = .suspended suspension) :
    PreparedInitializerFrame initialWorld rootContract rootInvocation :=
  let requestResult := HostStorageDriver.handleRequest
    frame.initializerInvocation.executionInputs frame.initializerContext
      suspension.request
  let typing := Core.hostAdvance_suspended_hasType
    frame.initializerStateTyping advanced
  let parentPresence : PresentAccountAt
      frame.initializerContext.context.values.working.1
      frame.suspendedRoot.parentContext.context.storageAddress :=
    ⟨frame.parentAccount, frame.parentAccount_present⟩
  let nextPresence := parentPresence.afterHandleRequest
    frame.initializerInvocation.executionInputs frame.initializerContext
      suspension.request
      frame.suspendedRoot.parentContext.context.storageAddress
  {
    frame with
    initializerContext := requestResult.1
    initializer_storageAddress_eq := by
      exact (handleRequest_storageAddress _ _ _).trans
        frame.initializer_storageAddress_eq
    initializer_checkpointState_eq := by
      exact (handleRequest_checkpointState _ _ _).trans
        frame.initializer_checkpointState_eq
    initializerState := suspension.resume requestResult.2
    initializerStateTyping := typing.resume requestResult.2
    parentAccount := nextPresence.account
    parentAccount_present := nextPresence.present
  }

def outcomeDone
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : PreparedInitializerFrame initialWorld rootContract rootInvocation)
    (value : Core.Value)
    (advanced : Core.hostAdvance frame.initializerState = .done value) :
    CheckedCoreWordOutcome := by
  have decoded : frame.prepared.template.initializer.decodeWordOutcome? value ≠ none := by
    obtain ⟨store, stateEq⟩ := Core.hostAdvance_done_iff.mp advanced
    have typing := frame.initializerStateTyping
    rw [stateEq] at typing
    cases typing with
    | ret _ valueTyping continuationTyping =>
        cases continuationTyping with
        | nil =>
            apply CoreContractEntryProfile.decodeWordOutcome?_ne_none_of_hasType
            rw [← frame.prepared.template.initializer.resultType_eq]
            exact valueTyping
  match resultEq : frame.prepared.template.initializer.decodeWordOutcome? value with
  | some outcome => exact outcome
  | none => exact False.elim (decoded resultEq)

end PreparedInitializerFrame
end Solcore.Semantics.OneLevelNestedExecution
