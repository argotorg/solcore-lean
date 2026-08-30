import Solcore.Semantics.CheckedCreationPreflightProperties
import Solcore.Semantics.OneLevelNestedExecutionState

/-! Proof-carrying scheduler state for one prepared contract initializer. -/

set_option autoImplicit false

namespace Solcore.Semantics.OneLevelNestedExecution

/-- Exact arguments of the checked creation host request. -/
structure CreationProfile where
  templateId : Core.Word
  value : Core.Word
  input : Core.Word

namespace CreationProfile

def request (profile : CreationProfile) : Core.HostRequest :=
  .createContractWord profile.templateId profile.value profile.input

def response
    (profile : CreationProfile)
    (result : Core.ContractCallWordResult) : profile.request.Response :=
  result

/-- Derive the initializer invocation from the frozen parent inputs. -/
def initializerInvocation
    (profile : CreationProfile)
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (createdAddress : Address) : TopLevelInvocation := {
  target := createdAddress
  caller := parentInputs.currentAddress
  callValue := profile.value
  inputData := HostStorageDriver.InputData.ofWord profile.input
}

@[simp] theorem request_exact (profile : CreationProfile) :
    profile.request =
      .createContractWord profile.templateId profile.value profile.input :=
  rfl

@[simp] theorem initializerInvocation_target
    (profile : CreationProfile)
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (createdAddress : Address) :
    (profile.initializerInvocation parentInputs createdAddress).target =
      createdAddress :=
  rfl

@[simp] theorem initializerInvocation_caller
    (profile : CreationProfile)
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (createdAddress : Address) :
    (profile.initializerInvocation parentInputs createdAddress).caller =
      parentInputs.currentAddress :=
  rfl

@[simp] theorem initializerInvocation_callValue
    (profile : CreationProfile)
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (createdAddress : Address) :
    (profile.initializerInvocation parentInputs createdAddress).callValue =
      profile.value :=
  rfl

@[simp] theorem initializerInvocation_inputData
    (profile : CreationProfile)
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (createdAddress : Address) :
    (profile.initializerInvocation parentInputs createdAddress).inputData =
      HostStorageDriver.InputData.ofWord profile.input :=
  rfl

end CreationProfile

/-- A root creation suspension before any response or state preparation. -/
structure SuspendedCreationRoot
    (initialWorld : WorldState)
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation) where
  parentContext : HostStorageDriver.Context Unit Unit
  profile : CreationProfile
  continuation : List Core.Frame
  store : Core.Store
  suspensionTyping :
    Core.HostSuspensionHasType
      ⟨profile.request, continuation, store⟩
      rootContract.code.program.resultType
      rootContract.code.program.dataDefinitions

namespace SuspendedCreationRoot

def suspension
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (root : SuspendedCreationRoot initialWorld rootContract rootInvocation) :
    Core.HostSuspension :=
  ⟨root.profile.request, root.continuation, root.store⟩

end SuspendedCreationRoot

/--
Prepared initializer execution with one immutable environment and exact links
to the parent call site, post-nonce checkpoint, and initializer working world.
The scheduler's active-mode type is defined separately so this carrier stays
independent of the execution dispatcher.
-/
structure PreparedInitializerFrame
    (initialWorld : WorldState)
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation) where
  suspendedRoot :
    SuspendedCreationRoot initialWorld rootContract rootInvocation
  environment : ExecutionEnvironment
  prepared :
    PreparedCheckedCreation
      suspendedRoot.parentContext.context.values.working.1
      environment
      rootInvocation.executionInputs.currentAddress
      suspendedRoot.profile.templateId
      suspendedRoot.profile.value
  creatorAddress_eq :
    rootInvocation.executionInputs.currentAddress =
      suspendedRoot.parentContext.context.storageAddress
  initializerInvocation : TopLevelInvocation
  initializerInvocation_eq :
    initializerInvocation =
      suspendedRoot.profile.initializerInvocation
        rootInvocation.executionInputs prepared.createdAddress
  postNonceParentContext : HostStorageDriver.Context Unit Unit
  postNonce_storageAddress_eq :
    postNonceParentContext.context.storageAddress =
      suspendedRoot.parentContext.context.storageAddress
  postNonce_workingWorld_eq :
    postNonceParentContext.context.values.working.1 =
      prepared.statePreparation.postNonceWorld
  postNonce_checkpoint_eq :
    postNonceParentContext.context.values.checkpoint =
      suspendedRoot.parentContext.context.values.checkpoint
  initializerContext : HostStorageDriver.Context Unit Unit
  initializer_storageAddress_eq :
    initializerContext.context.storageAddress = prepared.createdAddress
  initializer_checkpointState_eq :
    initializerContext.context.values.checkpoint.state =
      prepared.statePreparation.postNonceWorld
  initializerState : Core.State
  initializerStateTyping :
    Core.HostStateHasType initializerState
      prepared.template.initializer.code.program.resultType
      prepared.template.initializer.code.program.dataDefinitions
  parentAccount : Account
  parentAccount_present :
    initializerContext.context.values.working.1.account?
        suspendedRoot.parentContext.context.storageAddress =
      some parentAccount

end Solcore.Semantics.OneLevelNestedExecution
