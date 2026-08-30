import Solcore.Semantics.OneLevelNestedCreationTransitions

/-! Terminal resolution for one prepared checked contract initializer. -/

set_option autoImplicit false

namespace Solcore.Semantics.OneLevelNestedExecution

structure DeployedInitializerResult
    (initialWorld : WorldState)
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (frame : PreparedInitializerFrame initialWorld rootContract rootInvocation) where
  latestCreatedAccount : Account
  latestCreatedAccount_present :
    frame.initializerContext.context.values.working.1.account?
        frame.prepared.createdAddress = some latestCreatedAccount
  deployedAccount : Account
  deployedAccount_eq :
    deployedAccount = latestCreatedAccount.withCode frame.prepared.template.runtime.code
  deployedWorld : WorldState
  writeCode_eq :
    frame.initializerContext.context.values.working.1.writeCode?
        frame.prepared.createdAddress frame.prepared.template.runtime.code =
      some deployedWorld
  runtimeInstalled :
    InstalledCheckedCoreContract deployedWorld frame.prepared.createdAddress
      frame.prepared.template.runtime
  resumedRoot : RootFrame initialWorld rootContract rootInvocation
  resumedRoot_contextWorld_eq :
    resumedRoot.context.context.values.working.1 = deployedWorld
  resumedRoot_storageAddress_eq :
    resumedRoot.context.context.storageAddress =
      frame.suspendedRoot.parentContext.context.storageAddress
  resumedRoot_checkpointState_eq :
    resumedRoot.context.context.values.checkpoint.state =
      frame.suspendedRoot.parentContext.context.values.checkpoint.state
  resumedRoot_response_eq :
    resumedRoot.state = frame.suspendedRoot.suspension.resume
      (frame.suspendedRoot.profile.response
        (.returned (addressToWord frame.prepared.createdAddress)))

inductive InitializerCompletionResult
    (initialWorld : WorldState)
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (frame : PreparedInitializerFrame initialWorld rootContract rootInvocation) where
  | returned (deployed :
      DeployedInitializerResult initialWorld rootContract rootInvocation frame)
  | reverted (data : Core.Word)
      (root : RootFrame initialWorld rootContract rootInvocation)
      (context_eq : root.context = frame.postNonceParentContext)
      (response_eq : root.state = frame.suspendedRoot.suspension.resume
        (frame.suspendedRoot.profile.response (.reverted data)))
  | trapped (reason : Core.Word)
      (root : RootFrame initialWorld rootContract rootInvocation)
      (context_eq : root.context = frame.postNonceParentContext)
      (response_eq : root.state = frame.suspendedRoot.suspension.resume
        (frame.suspendedRoot.profile.response (.trapped reason)))

namespace InitializerCompletionResult

/-- The resumed parent root selected by every initializer outcome. -/
def root
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {frame : PreparedInitializerFrame initialWorld rootContract rootInvocation} :
    InitializerCompletionResult initialWorld rootContract rootInvocation frame →
      RootFrame initialWorld rootContract rootInvocation
  | .returned deployed => deployed.resumedRoot
  | .reverted _ root _ _ => root
  | .trapped _ root _ _ => root

end InitializerCompletionResult

namespace DeployedInitializerResult

@[simp] theorem deployed_code
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {frame : PreparedInitializerFrame initialWorld rootContract rootInvocation}
    (result : DeployedInitializerResult initialWorld rootContract rootInvocation frame) :
    result.deployedAccount.code? = some frame.prepared.template.runtime.code := by
  rw [result.deployedAccount_eq]
  rfl

@[simp] theorem deployed_storage
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {frame : PreparedInitializerFrame initialWorld rootContract rootInvocation}
    (result : DeployedInitializerResult initialWorld rootContract rootInvocation frame)
    (slot : Core.Word) :
    result.deployedAccount.storageValue? slot =
      result.latestCreatedAccount.storageValue? slot := by
  rw [result.deployedAccount_eq]
  rfl

@[simp] theorem deployed_balance
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {frame : PreparedInitializerFrame initialWorld rootContract rootInvocation}
    (result : DeployedInitializerResult initialWorld rootContract rootInvocation frame) :
    result.deployedAccount.balance = result.latestCreatedAccount.balance := by
  rw [result.deployedAccount_eq]
  rfl

@[simp] theorem deployed_nonce
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {frame : PreparedInitializerFrame initialWorld rootContract rootInvocation}
    (result : DeployedInitializerResult initialWorld rootContract rootInvocation frame) :
    result.deployedAccount.nonce = result.latestCreatedAccount.nonce := by
  rw [result.deployedAccount_eq]
  rfl

end DeployedInitializerResult

namespace PreparedInitializerFrame

def completeReturned
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : PreparedInitializerFrame initialWorld rootContract rootInvocation) :
    DeployedInitializerResult initialWorld rootContract rootInvocation frame := by
  let latestCreatedAccount := frame.initializerContext.storageAccount
  have latestPresent :
      frame.initializerContext.context.values.working.1.account?
          frame.prepared.createdAddress = some latestCreatedAccount := by
    rw [← frame.initializer_storageAddress_eq]
    exact frame.initializerContext.storageAccount_present
  let deployedAccount := latestCreatedAccount.withCode
    frame.prepared.template.runtime.code
  let deployedWorld := frame.initializerContext.context.values.working.1.putAccount
    frame.prepared.createdAddress deployedAccount
  have writeCodeEq :
      frame.initializerContext.context.values.working.1.writeCode?
          frame.prepared.createdAddress frame.prepared.template.runtime.code =
        some deployedWorld := by
    rw [WorldState.writeCode?_of_present _ _ _ _ latestPresent]
  let installed : InstalledCheckedCoreContract deployedWorld
      frame.prepared.createdAddress frame.prepared.template.runtime := {
    account := deployedAccount
    account_present := WorldState.account?_putAccount_same _ _ _
    code_present := by rfl
  }
  have created_ne_parent : frame.prepared.createdAddress ≠
      frame.suspendedRoot.parentContext.context.storageAddress := by
    intro equal
    have different :=
      CheckedAccountCreation.PreparedAccountCreation.created_ne_creator
        frame.prepared.statePreparation
    apply different
    exact frame.prepared.preparation_address_eq.trans
      (equal.trans frame.creatorAddress_eq.symm)
  have parentPresent : deployedWorld.account?
      frame.suspendedRoot.parentContext.context.storageAddress =
        some frame.parentAccount := by
    rw [WorldState.account?_putAccount_other _ frame.prepared.createdAddress
      frame.suspendedRoot.parentContext.context.storageAddress deployedAccount
      (Ne.symm created_ne_parent)]
    exact frame.parentAccount_present
  have parentPresentAtPostNonceSelector : deployedWorld.account?
      frame.postNonceParentContext.context.storageAddress =
        some frame.parentAccount := by
    rw [frame.postNonce_storageAddress_eq]
    exact parentPresent
  let parentContext := frame.postNonceParentContext.rebaseWorking deployedWorld
    frame.parentAccount parentPresentAtPostNonceSelector
  let root := frame.suspendedRoot.resumeWith parentContext
    (.returned (addressToWord frame.prepared.createdAddress))
  exact {
    latestCreatedAccount := latestCreatedAccount
    latestCreatedAccount_present := latestPresent
    deployedAccount := deployedAccount
    deployedAccount_eq := rfl
    deployedWorld := deployedWorld
    writeCode_eq := writeCodeEq
    runtimeInstalled := installed
    resumedRoot := root
    resumedRoot_contextWorld_eq := rfl
    resumedRoot_storageAddress_eq := frame.postNonce_storageAddress_eq
    resumedRoot_checkpointState_eq :=
      congrArg FrameCheckpointSnapshot.state frame.postNonce_checkpoint_eq
    resumedRoot_response_eq := rfl
  }

def complete
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : PreparedInitializerFrame initialWorld rootContract rootInvocation) :
    CheckedCoreWordOutcome →
      InitializerCompletionResult initialWorld rootContract rootInvocation frame
  | .returned _ => .returned frame.completeReturned
  | .reverted data =>
      let root := frame.suspendedRoot.resumeWith frame.postNonceParentContext
        (.reverted data)
      .reverted data root rfl rfl
  | .trapped reason =>
      let root := frame.suspendedRoot.resumeWith frame.postNonceParentContext
        (.trapped reason)
      .trapped reason root rfl rfl

end PreparedInitializerFrame

namespace InitializerCompletionResult

@[simp] theorem root_storageAddress
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {frame : PreparedInitializerFrame initialWorld rootContract rootInvocation}
    (result :
      InitializerCompletionResult initialWorld rootContract rootInvocation frame) :
    result.root.context.context.storageAddress =
      frame.suspendedRoot.parentContext.context.storageAddress := by
  cases result with
  | returned deployed =>
      exact deployed.resumedRoot_storageAddress_eq
  | reverted data resumed context_eq response_eq =>
      simp only [root]
      rw [context_eq]
      exact frame.postNonce_storageAddress_eq
  | trapped reason resumed context_eq response_eq =>
      simp only [root]
      rw [context_eq]
      exact frame.postNonce_storageAddress_eq

@[simp] theorem root_checkpointState
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {frame : PreparedInitializerFrame initialWorld rootContract rootInvocation}
    (result :
      InitializerCompletionResult initialWorld rootContract rootInvocation frame) :
    result.root.context.context.values.checkpoint.state =
      frame.suspendedRoot.parentContext.context.values.checkpoint.state := by
  cases result with
  | returned deployed =>
      exact deployed.resumedRoot_checkpointState_eq
  | reverted data resumed context_eq response_eq =>
      simp only [root]
      rw [context_eq]
      exact congrArg FrameCheckpointSnapshot.state frame.postNonce_checkpoint_eq
  | trapped reason resumed context_eq response_eq =>
      simp only [root]
      rw [context_eq]
      exact congrArg FrameCheckpointSnapshot.state frame.postNonce_checkpoint_eq

end InitializerCompletionResult
end Solcore.Semantics.OneLevelNestedExecution
