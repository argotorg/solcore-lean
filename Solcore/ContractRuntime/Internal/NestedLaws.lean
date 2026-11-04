import Solcore.ContractRuntime.NestedExecution
import Solcore.Core.HostMachine
import Solcore.ContractRuntime.Internal.EntryOutcomeLaws
import Solcore.ContractRuntime.Internal.StorageDriverLaws
import Solcore.ContractRuntime.Internal.TopLevelLaws
import Solcore.ContractRuntime.Internal.WorldStateLaws
import Solcore.ContractRuntime.Internal.CreationLaws
import Solcore.Core.HostRunner
import Solcore.Core.Internal.HostPreservation
import Solcore.ContractRuntime.StorageDriver
import Solcore.ContractRuntime.Internal.TransactionLaws
import Solcore.ContractRuntime.Internal.ContractLaws
import Solcore.ContractRuntime.Internal.FrameLaws
import Solcore.ContractRuntime.Internal.WorldStateDeltaLaws

/-!
# Laws of nested execution

The depth-one word call, the steps of the transition system, and the anchoring of reachable states.
-/

section
-- leanmerge: from Solcore.ContractRuntime.NestedWordCall
/-! Exact invocation and response derivation for one internal Word call. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace TopLevelInvocation

@[simp] theorem childWord_target
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (input : Core.Word) :
    (childWord parentInputs target input).target = target :=
  rfl

@[simp] theorem childWord_caller
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (input : Core.Word) :
    (childWord parentInputs target input).caller =
      parentInputs.currentAddress :=
  rfl

@[simp] theorem childWord_callValue
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (input : Core.Word) :
    (childWord parentInputs target input).callValue = Core.Word.zero :=
  rfl

@[simp] theorem childWord_inputBytes
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (input : Core.Word) :
    (childWord parentInputs target input).inputData.bytes =
      encodeWordBytesBE input :=
  rfl

@[simp] theorem childWord_executionInputs
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (input : Core.Word) :
    (childWord parentInputs target input).executionInputs = {
      codeAddress := target
      callValue := Core.Word.zero
      callerAddress := parentInputs.currentAddress
      inputData := HostStorageDriver.InputData.ofWord input
      currentAddress := target
    } :=
  rfl

@[simp] theorem childWordWithValue_target
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (value input : Core.Word) :
    (childWordWithValue parentInputs target value input).target = target :=
  rfl

@[simp] theorem childWordWithValue_caller
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (value input : Core.Word) :
    (childWordWithValue parentInputs target value input).caller =
      parentInputs.currentAddress :=
  rfl

@[simp] theorem childWordWithValue_callValue
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (value input : Core.Word) :
    (childWordWithValue parentInputs target value input).callValue = value :=
  rfl

@[simp] theorem childWordWithValue_inputBytes
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (value input : Core.Word) :
    (childWordWithValue parentInputs target value input).inputData.bytes =
      encodeWordBytesBE input :=
  rfl

@[simp] theorem childWordWithValue_executionInputs
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (value input : Core.Word) :
    (childWordWithValue parentInputs target value input).executionInputs = {
      codeAddress := target
      callValue := value
      callerAddress := parentInputs.currentAddress
      inputData := HostStorageDriver.InputData.ofWord input
      currentAddress := target
    } :=
  rfl

end TopLevelInvocation

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.OneLevelNestedTransitionSystem
/-! State and transition rules for one-level nested contract execution. -/

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedExecutionState`
-/

/-! Typed root and child states for one-level nested checked-Core execution. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedCreationState`
-/

/-! Proof-carrying scheduler state for one prepared contract initializer. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution

namespace CreationProfile

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

end Solcore.ContractRuntime.OneLevelNestedExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedExecutionMode`
-/

/-! Active modes of the one-level checked-Core scheduler. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedCreationTransitions`
-/

/-! Lifecycle helpers for one prepared checked contract initializer. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution

namespace SuspendedCreationRoot

@[simp] theorem startInitializer_postNonce_workingJournal
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (root : SuspendedCreationRoot initialWorld rootContract rootInvocation)
    (environment : ExecutionEnvironment)
    (prepared : PreparedCheckedCreation
      root.parentContext.context.values.working.1 environment
      rootInvocation.executionInputs.currentAddress root.profile.templateId
      root.profile.value)
    (initializerReturnsOneWord :
      prepared.template.initializer.entryProfile.returnsOneWord = true)
    (creatorAddress_eq : rootInvocation.executionInputs.currentAddress =
      root.parentContext.context.storageAddress) :
    (root.startInitializer environment prepared initializerReturnsOneWord
      creatorAddress_eq).postNonceParentContext.workingJournal =
      root.parentContext.workingJournal := by
  rfl

@[simp] theorem startInitializer_initializer_checkpointJournal
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (root : SuspendedCreationRoot initialWorld rootContract rootInvocation)
    (environment : ExecutionEnvironment)
    (prepared : PreparedCheckedCreation
      root.parentContext.context.values.working.1 environment
      rootInvocation.executionInputs.currentAddress root.profile.templateId
      root.profile.value)
    (initializerReturnsOneWord :
      prepared.template.initializer.entryProfile.returnsOneWord = true)
    (creatorAddress_eq : rootInvocation.executionInputs.currentAddress =
      root.parentContext.context.storageAddress) :
    (root.startInitializer environment prepared initializerReturnsOneWord
      creatorAddress_eq).initializerContext.context.values.checkpoint.effects.rollback =
      root.parentContext.workingJournal := by
  rfl

@[simp] theorem startInitializer_initializer_workingJournal
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (root : SuspendedCreationRoot initialWorld rootContract rootInvocation)
    (environment : ExecutionEnvironment)
    (prepared : PreparedCheckedCreation
      root.parentContext.context.values.working.1 environment
      rootInvocation.executionInputs.currentAddress root.profile.templateId
      root.profile.value)
    (initializerReturnsOneWord :
      prepared.template.initializer.entryProfile.returnsOneWord = true)
    (creatorAddress_eq : rootInvocation.executionInputs.currentAddress =
      root.parentContext.context.storageAddress) :
    (root.startInitializer environment prepared initializerReturnsOneWord
      creatorAddress_eq).initializerContext.workingJournal =
      root.parentContext.workingJournal := by
  rfl

end SuspendedCreationRoot

end Solcore.ContractRuntime.OneLevelNestedExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedCreationCompletion`
-/

/-! Terminal resolution for one prepared checked contract initializer. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution

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

namespace DeployedInitializerResult

@[simp] theorem resumedRoot_logList
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {frame : PreparedInitializerFrame initialWorld rootContract rootInvocation}
    (result :
      DeployedInitializerResult initialWorld rootContract rootInvocation frame) :
    result.resumedRoot.context.workingJournal.logList =
      frame.initializerContext.workingJournal.logList := by
  rw [result.resumedRoot_workingJournal_eq]
  simp

@[simp] theorem resumedRoot_createdContractList
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {frame : PreparedInitializerFrame initialWorld rootContract rootInvocation}
    (result :
      DeployedInitializerResult initialWorld rootContract rootInvocation frame) :
    result.resumedRoot.context.workingJournal.createdContractList =
      frame.initializerContext.workingJournal.createdContractList ++
        [frame.prepared.createdAddress] := by
  rw [result.resumedRoot_workingJournal_eq]
  simp

end DeployedInitializerResult

end Solcore.ContractRuntime.OneLevelNestedExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedExecutionTransitions`
-/

/-! Proof-preserving local transitions for the one-level nested scheduler. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution

namespace SuspendedRoot

@[simp] theorem startChild_checkpointJournal
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (root : SuspendedRoot initialWorld rootContract rootInvocation)
    (target : Address)
    (targetAddress_eq : wordToAddress? root.call.target = some target)
    (childContract : CheckedCoreContract)
    (childReturnsOneWord : childContract.entryProfile.returnsOneWord = true)
    (preTransferInstalled : InstalledCheckedCoreContract
      root.parentContext.context.values.working.1 target childContract)
    (childInitialWorld : WorldState)
    (installed : InstalledCheckedCoreContract childInitialWorld target childContract)
    (parentPresence : PresentAccountAt childInitialWorld
      root.parentContext.context.storageAddress) :
    (root.startChild target targetAddress_eq childContract childReturnsOneWord
      preTransferInstalled childInitialWorld installed parentPresence).childContext.context.values.checkpoint.effects.rollback =
        root.parentContext.workingJournal := by
  rfl

@[simp] theorem startChild_workingJournal
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (root : SuspendedRoot initialWorld rootContract rootInvocation)
    (target : Address)
    (targetAddress_eq : wordToAddress? root.call.target = some target)
    (childContract : CheckedCoreContract)
    (childReturnsOneWord : childContract.entryProfile.returnsOneWord = true)
    (preTransferInstalled : InstalledCheckedCoreContract
      root.parentContext.context.values.working.1 target childContract)
    (childInitialWorld : WorldState)
    (installed : InstalledCheckedCoreContract childInitialWorld target childContract)
    (parentPresence : PresentAccountAt childInitialWorld
      root.parentContext.context.storageAddress) :
    (root.startChild target targetAddress_eq childContract childReturnsOneWord
      preTransferInstalled childInitialWorld installed parentPresence).childContext.workingJournal =
        root.parentContext.workingJournal := by
  rfl

end SuspendedRoot

end Solcore.ContractRuntime.OneLevelNestedExecution
end

section
-- leanmerge: from Solcore.ContractRuntime.OneLevelNestedExecution
/-! Reachability seal for scheduler states produced by checked execution. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedExecutionReachabilityProperties`
-/

/-! Root and child context provenance derived from scheduler reachability. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution

theorem Reachable.root_checkpointState
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {registry : ExecutionEnvironment}
    {frame : RootFrame initialWorld rootContract rootInvocation}
    (reachable : Reachable registry (.root frame)) :
    frame.context.context.values.checkpoint.state = initialWorld :=
  reachable.anchored.checkpointState_eq

/-- Every reachable root retains the empty transaction rollback journal. -/
theorem Reachable.root_checkpointJournal
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {registry : ExecutionEnvironment}
    {frame : RootFrame initialWorld rootContract rootInvocation}
    (reachable : Reachable registry (.root frame)) :
    frame.context.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty :=
  reachable.anchored.checkpointJournal_eq

theorem Reachable.child_parentStorageAddress
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {registry : ExecutionEnvironment}
    {frame : ChildFrame initialWorld rootContract rootInvocation}
    (reachable : Reachable registry (.child frame)) :
    frame.suspendedRoot.parentContext.context.storageAddress =
      rootInvocation.target :=
  reachable.anchored.parentStorageAddress_eq

theorem Reachable.child_parentCheckpointState
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {registry : ExecutionEnvironment}
    {frame : ChildFrame initialWorld rootContract rootInvocation}
    (reachable : Reachable registry (.child frame)) :
    frame.suspendedRoot.parentContext.context.values.checkpoint.state =
      initialWorld :=
  reachable.anchored.parentCheckpointState_eq

/-- The suspended root behind a child retains the empty transaction checkpoint. -/
theorem Reachable.child_parentCheckpointJournal
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {registry : ExecutionEnvironment}
    {frame : ChildFrame initialWorld rootContract rootInvocation}
    (reachable : Reachable registry (.child frame)) :
    frame.suspendedRoot.parentContext.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty :=
  reachable.anchored.parentCheckpointJournal_eq

theorem Reachable.child_storageAddress
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {registry : ExecutionEnvironment}
    {frame : ChildFrame initialWorld rootContract rootInvocation}
    (reachable : Reachable registry (.child frame)) :
    frame.childContext.context.storageAddress = frame.childTarget :=
  reachable.anchored.childStorageAddress_eq

theorem Reachable.child_checkpointState
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {registry : ExecutionEnvironment}
    {frame : ChildFrame initialWorld rootContract rootInvocation}
    (reachable : Reachable registry (.child frame)) :
    frame.childContext.context.values.checkpoint.state =
      frame.childInitialWorld :=
  reachable.anchored.childCheckpointState_eq

/-- A live child's rollback journal is the exact parent prefix at its call site. -/
theorem Reachable.child_checkpointJournal
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {registry : ExecutionEnvironment}
    {frame : ChildFrame initialWorld rootContract rootInvocation}
    (reachable : Reachable registry (.child frame)) :
    frame.childContext.context.values.checkpoint.effects.rollback =
      frame.suspendedRoot.parentContext.workingJournal :=
  reachable.anchored.childCheckpointJournal_eq

/-- A live child is exactly the contract resolved at its frozen call site. -/
theorem Reachable.child_registryResolution
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {registry : ExecutionEnvironment}
    {frame : ChildFrame initialWorld rootContract rootInvocation}
    (reachable : Reachable registry (.child frame)) :
    registry.callRegistry.resolve?
        frame.suspendedRoot.parentContext.context.values.working.1
        frame.childTarget =
      some ⟨frame.childContract, frame.preTransferInstalled⟩ :=
  reachable.anchored.registryResolution_eq

/-- A live initializer rolls back to the exact journal prefix before creation. -/
theorem Reachable.initializer_checkpointJournal
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {environment : ExecutionEnvironment}
    {frame : PreparedInitializerFrame initialWorld rootContract rootInvocation}
    (reachable : Reachable environment (.initializer frame)) :
    frame.initializerContext.context.values.checkpoint.effects.rollback =
      frame.suspendedRoot.parentContext.workingJournal :=
  reachable.anchored.initializerCheckpointJournal_eq

/-- The suspended root behind an initializer retains the empty checkpoint. -/
theorem Reachable.initializer_parentCheckpointJournal
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {environment : ExecutionEnvironment}
    {frame : PreparedInitializerFrame initialWorld rootContract rootInvocation}
    (reachable : Reachable environment (.initializer frame)) :
    frame.suspendedRoot.parentContext.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty :=
  reachable.anchored.parentCheckpointJournal_eq

end Solcore.ContractRuntime.OneLevelNestedExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedExecutionResult`
-/

/-! Total bounded results for one-level nested checked-Core execution. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedExecution`
-/

/-! Shared-fuel execution for one root and one active leaf child. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedExecutionProperties`
-/

/-! Exact branch laws for one-level nested checked-Core execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution

namespace RootFrame

@[simp] theorem finalize_returned_finalWorld
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (value : Core.Value) (store : Core.Store) (data : Bytes) :
    (frame.finalize value store (.returned data)).finalWorld =
      frame.context.context.values.working.1 :=
  rfl

@[simp] theorem finalize_reverted_finalWorld
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (value : Core.Value) (store : Core.Store) (data : Bytes) :
    (frame.finalize value store (.reverted data)).finalWorld = initialWorld :=
  rfl

@[simp] theorem finalize_trapped_finalWorld
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (value : Core.Value) (store : Core.Store) (reason : Core.Word) :
    (frame.finalize value store (.trapped reason)).finalWorld = initialWorld :=
  rfl

@[simp] theorem finalize_outcome
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (value : Core.Value) (store : Core.Store)
    (outcome : FrameOutcome Core.Word) :
    (frame.finalize value store outcome).outcome = outcome := by
  cases outcome <;> rfl

@[simp] theorem finalize_workingDelta
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (value : Core.Value) (store : Core.Store)
    (outcome : FrameOutcome Core.Word) :
    (frame.finalize value store outcome).workingDelta = .exact := by
  cases outcome <;> rfl

@[simp] theorem finalize_workingJournal
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (value : Core.Value) (store : Core.Store)
    (outcome : FrameOutcome Core.Word) :
    (frame.finalize value store outcome).workingJournal =
      frame.context.workingJournal := by
  cases outcome <;> rfl

@[simp] theorem finalize_returned_committedJournal
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (value : Core.Value) (store : Core.Store) (data : Bytes) :
    (frame.finalize value store (.returned data)).committedJournal =
      frame.context.workingJournal :=
  rfl

@[simp] theorem finalize_reverted_committedJournal
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (value : Core.Value) (store : Core.Store) (data : Bytes) :
    (frame.finalize value store (.reverted data)).committedJournal =
      frame.context.context.values.checkpoint.effects.rollback :=
  rfl

@[simp] theorem finalize_trapped_committedJournal
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (value : Core.Value) (store : Core.Store) (reason : Core.Word) :
    (frame.finalize value store (.trapped reason)).committedJournal =
      frame.context.context.values.checkpoint.effects.rollback :=
  rfl

end RootFrame

namespace ChildFrame

@[simp] theorem selectedParentContext_returned_workingWorld
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : ChildFrame initialWorld rootContract rootInvocation)
    (data : Core.Word) :
    (frame.selectedParentContext (.returned data)).context.values.working.1 =
      frame.childContext.context.values.working.1 :=
  rfl

@[simp] theorem selectedParentContext_returned_workingJournal
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : ChildFrame initialWorld rootContract rootInvocation)
    (data : Core.Word) :
    (frame.selectedParentContext (.returned data)).workingJournal =
      frame.childContext.workingJournal :=
  rfl

@[simp] theorem selectedParentContext_reverted
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : ChildFrame initialWorld rootContract rootInvocation)
    (data : Core.Word) :
    frame.selectedParentContext (.reverted data) =
      frame.suspendedRoot.parentContext :=
  rfl

@[simp] theorem selectedParentContext_trapped
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : ChildFrame initialWorld rootContract rootInvocation)
    (reason : Core.Word) :
    frame.selectedParentContext (.trapped reason) =
      frame.suspendedRoot.parentContext :=
  rfl

@[simp] theorem resumeRoot_returned_workingWorld
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : ChildFrame initialWorld rootContract rootInvocation)
    (data : Core.Word) :
    (frame.resumeRoot (.returned data)).context.context.values.working.1 =
      frame.childContext.context.values.working.1 :=
  rfl

@[simp] theorem resumeRoot_reverted_context
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : ChildFrame initialWorld rootContract rootInvocation)
    (data : Core.Word) :
    (frame.resumeRoot (.reverted data)).context =
      frame.suspendedRoot.parentContext :=
  rfl

@[simp] theorem resumeRoot_trapped_context
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : ChildFrame initialWorld rootContract rootInvocation)
    (reason : Core.Word) :
    (frame.resumeRoot (.trapped reason)).context =
      frame.suspendedRoot.parentContext :=
  rfl

@[simp] theorem resumeRoot_returned_response
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : ChildFrame initialWorld rootContract rootInvocation)
    (data : Core.Word) :
    (frame.resumeRoot (.returned data)).state =
      frame.suspendedRoot.suspension.resume
        (frame.suspendedRoot.call.response (.returned data)) :=
  rfl

@[simp] theorem resumeRoot_reverted_response
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : ChildFrame initialWorld rootContract rootInvocation)
    (data : Core.Word) :
    (frame.resumeRoot (.reverted data)).state =
      frame.suspendedRoot.suspension.resume
        (frame.suspendedRoot.call.response (.reverted data)) :=
  rfl

@[simp] theorem resumeRoot_trapped_response
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : ChildFrame initialWorld rootContract rootInvocation)
    (reason : Core.Word) :
    (frame.resumeRoot (.trapped reason)).state =
      frame.suspendedRoot.suspension.resume
        (frame.suspendedRoot.call.response (.trapped reason)) :=
  rfl

end ChildFrame

end Solcore.ContractRuntime.OneLevelNestedExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedExecutionResumption`
-/

/-! Resumption for bounded one-level nested checked-Core execution. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedExecutionResumptionProperties`
-/

/-! Exact split-fuel laws for one-level nested checked-Core execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution

/-- Explicitly named form of the fixed-environment split-fuel law. -/
theorem resumeWithFuel_runModeWithEnvironment
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (environment : ExecutionEnvironment)
    (fuel additional : Nat)
    (mode : Mode initialWorld rootContract rootInvocation)
    (reachable : Reachable environment mode) :
    resumeWithFuel
        (runModeWithEnvironment environment fuel mode reachable) additional =
      runModeWithEnvironment environment (fuel + additional) mode reachable :=
  resumeWithFuel_runMode environment fuel additional mode reachable

/-- A terminal nested result remains terminal under every added budget. -/
@[simp] theorem resumeWithFuel_completed
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (terminal : TerminalResult initialWorld rootContract rootInvocation)
    (completed : result.view = .completed terminal)
    (additional : Nat) :
    resumeWithFuel result additional = result := by
  simp [resumeWithFuel, completed]

/-- An exhausted result resumes with its retained registry and active mode. -/
@[simp] theorem resumeWithFuel_outOfFuel
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : ExecutionEnvironment)
    (mode : Mode initialWorld rootContract rootInvocation)
    (reachable : Reachable registry mode)
    (result : Result initialWorld rootContract rootInvocation)
    (exhausted : result.view = .outOfFuel registry mode reachable)
    (additional : Nat) :
    resumeWithFuel result additional =
      runMode registry additional mode reachable := by
  simp [resumeWithFuel, exhausted]

/-- Zero additional fuel is an identity for every actual scheduler run. -/
@[simp] theorem resumeWithFuel_runMode_zero
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : ExecutionEnvironment)
    (fuel : Nat)
    (mode : Mode initialWorld rootContract rootInvocation)
    (reachable : Reachable registry mode) :
    resumeWithFuel (runMode registry fuel mode reachable) 0 =
      runMode registry fuel mode reachable := by
  rw [resumeWithFuel_runMode]
  simp only [Nat.add_zero]

/-- Sequential additions associate for every retained scheduler result. -/
theorem resumeWithFuel_add
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (first second : Nat) :
    resumeWithFuel (resumeWithFuel result first) second =
      resumeWithFuel result (first + second) := by
  cases observed : result.view with
  | completed terminal =>
      simp [resumeWithFuel, observed]
  | outOfFuel registry mode reachable =>
      rw [resumeWithFuel_outOfFuel registry mode reachable result observed]
      rw [resumeWithFuel_outOfFuel registry mode reachable result observed]
      exact resumeWithFuel_runMode registry first second mode reachable

/-- Two additions after an actual run equal one run at the total budget. -/
theorem resumeWithFuel_runMode_add
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : ExecutionEnvironment)
    (fuel first second : Nat)
    (mode : Mode initialWorld rootContract rootInvocation)
    (reachable : Reachable registry mode) :
    resumeWithFuel
        (resumeWithFuel (runMode registry fuel mode reachable) first) second =
      runMode registry (fuel + first + second) mode reachable := by
  rw [resumeWithFuel_runMode, resumeWithFuel_runMode]

/-- Splitting fuel at the installed-root API is exactly one larger run. -/
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
  exact resumeWithFuel_runMode environment fuel additional
    (Mode.initialRoot rootContract rootInvocation installed)
    (.initial installed)

end Solcore.ContractRuntime.OneLevelNestedExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedExecutionBalancedRootProperties`
-/

/-! Exact projections of a root prepared after top-level value transfer. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution.RootFrame

@[simp] theorem prepared_storageAddress
    {checkpointWorld workingWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (installed :
      InstalledCheckedCoreContract workingWorld rootInvocation.target
        rootContract) :
    (prepared (checkpointWorld := checkpointWorld) rootContract rootInvocation
      installed).context.context.storageAddress = rootInvocation.target := by
  rfl

@[simp] theorem prepared_checkpointState
    {checkpointWorld workingWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (installed :
      InstalledCheckedCoreContract workingWorld rootInvocation.target
        rootContract) :
    (prepared (checkpointWorld := checkpointWorld) rootContract rootInvocation
      installed).context.context.values.checkpoint.state =
        checkpointWorld := by
  rfl

@[simp] theorem prepared_workingState
    {checkpointWorld workingWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (installed :
      InstalledCheckedCoreContract workingWorld rootInvocation.target
        rootContract) :
    (prepared (checkpointWorld := checkpointWorld) rootContract rootInvocation
      installed).context.context.values.working.1 = workingWorld := by
  rfl

@[simp] theorem prepared_storageAccount
    {checkpointWorld workingWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (installed :
      InstalledCheckedCoreContract workingWorld rootInvocation.target
        rootContract) :
    (prepared (checkpointWorld := checkpointWorld) rootContract rootInvocation
      installed).context.storageAccount = installed.account := by
  rfl

@[simp] theorem prepared_state
    {checkpointWorld workingWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (installed :
      InstalledCheckedCoreContract workingWorld rootInvocation.target
        rootContract) :
    (prepared (checkpointWorld := checkpointWorld) rootContract rootInvocation
      installed).state =
        Core.State.initial rootContract.code.program.body
          Core.hostEnvironment := by
  rfl

end Solcore.ContractRuntime.OneLevelNestedExecution.RootFrame

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedValueCallProperties`
-/

/-! Public projection laws for the nested value-call scheduler profile. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution.CallProfile

@[simp] theorem request_legacy (target input : Core.Word) :
    (legacy target input).request = .callContractWord target input :=
  rfl

@[simp] theorem request_withValue (target value input : Core.Word) :
    (withValue target value input).request =
      .callContractWordWithValue target value input :=
  rfl

@[simp] theorem target_legacy (target input : Core.Word) :
    (legacy target input).target = target :=
  rfl

@[simp] theorem target_withValue (target value input : Core.Word) :
    (withValue target value input).target = target :=
  rfl

@[simp] theorem invocation_legacy
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (targetWord input : Core.Word) :
    (legacy targetWord input).invocation parentInputs target =
      TopLevelInvocation.childWord parentInputs target input :=
  rfl

@[simp] theorem invocation_withValue
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) (targetWord value input : Core.Word) :
    (withValue targetWord value input).invocation parentInputs target =
      TopLevelInvocation.childWordWithValue parentInputs target value input :=
  rfl

end Solcore.ContractRuntime.OneLevelNestedExecution.CallProfile
end
