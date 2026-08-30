import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteProjectionProperties
import Solcore.Semantics.HostStorageContextRebase
import Solcore.Semantics.OneLevelNestedExecutionReachability
import Solcore.Semantics.TopLevelExecutionContextProperties

/-! Root and child context provenance derived from scheduler reachability. -/

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

private theorem handleRequest_checkpoint
    {RollbackState TraceState : Type}
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (request : Core.HostRequest) :
    (HostStorageDriver.handleRequest inputs context request).1.context.values.checkpoint =
      context.context.values.checkpoint := by
  cases request <;> rfl

private theorem ChildFrame.afterHandledSuspension_storageAddress
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : ChildFrame initialWorld rootContract rootInvocation)
    (suspension : Core.HostSuspension)
    (advanced : Core.hostAdvance frame.childState = .suspended suspension) :
    (frame.afterHandledSuspension suspension advanced).childContext.context.storageAddress =
      frame.childContext.context.storageAddress := by
  exact handleRequest_storageAddress _ _ _

private theorem ChildFrame.afterHandledSuspension_checkpoint
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : ChildFrame initialWorld rootContract rootInvocation)
    (suspension : Core.HostSuspension)
    (advanced : Core.hostAdvance frame.childState = .suspended suspension) :
    (frame.afterHandledSuspension suspension advanced).childContext.context.values.checkpoint =
      frame.childContext.context.values.checkpoint := by
  exact handleRequest_checkpoint _ _ _

/-- A reachable root context remains anchored to its top-level invocation. -/
structure RootAnchored
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : RootFrame initialWorld rootContract rootInvocation) : Prop where
  storageAddress_eq :
    frame.context.context.storageAddress = rootInvocation.target
  checkpointState_eq :
    frame.context.context.values.checkpoint.state = initialWorld

/-- A reachable child retains both its root origin and its call checkpoint. -/
structure ChildAnchored
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : CheckedContractRegistry)
    (frame : ChildFrame initialWorld rootContract rootInvocation) : Prop where
  parentStorageAddress_eq :
    frame.suspendedRoot.parentContext.context.storageAddress =
      rootInvocation.target
  parentCheckpointState_eq :
    frame.suspendedRoot.parentContext.context.values.checkpoint.state =
      initialWorld
  childStorageAddress_eq :
    frame.childContext.context.storageAddress = frame.childTarget
  childCheckpointState_eq :
    frame.childContext.context.values.checkpoint.state =
      frame.childInitialWorld
  registryResolution_eq :
    registry.resolve?
        frame.suspendedRoot.parentContext.context.values.working.1
        frame.childTarget =
      some ⟨frame.childContract, frame.preTransferInstalled⟩

/-- Mode-indexed form used for one induction over the transition closure. -/
def Anchored
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : CheckedContractRegistry) :
    Mode initialWorld rootContract rootInvocation → Prop
  | .root frame => RootAnchored frame
  | .child frame => ChildAnchored registry frame

private theorem rootAfterSuspension_anchored
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : CheckedContractRegistry)
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (suspension : Core.HostSuspension)
    (advanced : Core.hostAdvance frame.state = .suspended suspension)
    (anchored : RootAnchored frame) :
    Anchored registry
      (frame.afterSuspension registry suspension advanced) := by
  rcases suspension with ⟨request, continuation, store⟩
  cases request with
  | callContractWord target input =>
      simp only [RootFrame.afterSuspension]
      split
      · exact ⟨anchored.storageAddress_eq, anchored.checkpointState_eq⟩
      ·
        split
        · exact ⟨anchored.storageAddress_eq, anchored.checkpointState_eq⟩
        · exact ⟨anchored.storageAddress_eq,
            anchored.checkpointState_eq, rfl, rfl, by assumption⟩
  | callContractWordWithValue target value input =>
      simp only [RootFrame.afterSuspension]
      split
      · exact ⟨anchored.storageAddress_eq, anchored.checkpointState_eq⟩
      · split
        · exact ⟨anchored.storageAddress_eq, anchored.checkpointState_eq⟩
        · split
          · exact ⟨anchored.storageAddress_eq, anchored.checkpointState_eq⟩
          · exact ⟨anchored.storageAddress_eq,
              anchored.checkpointState_eq, rfl, rfl, by assumption⟩
  | createContractWord templateId value input =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq⟩
  | storageRead slot =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq⟩
  | storageWrite slot value =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq⟩
  | storageAddress =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq⟩
  | codeAddress =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq⟩
  | callValue =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq⟩
  | callerAddress =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq⟩
  | inputDataByte? offset =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq⟩
  | inputDataSize =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq⟩
  | inputDataWordBE? offset =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq⟩
  | currentAddress =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq⟩

/-- Every scheduler-reachable mode retains its root and call-site anchors. -/
theorem Reachable.anchored
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {registry : CheckedContractRegistry}
    {mode : Mode initialWorld rootContract rootInvocation}
    (reachable : Reachable registry mode) :
    Anchored registry mode := by
  induction reachable with
  | initial installed =>
      exact ⟨rfl, rfl⟩
  | balancedInitial installed transferred =>
      exact ⟨rfl, rfl⟩
  | rootNext prior advanced inductionHypothesis =>
      rcases inductionHypothesis with ⟨address, checkpoint⟩
      exact ⟨address, checkpoint⟩
  | rootSuspended prior advanced inductionHypothesis =>
      exact rootAfterSuspension_anchored _ _ _ advanced
        inductionHypothesis
  | childDone prior advanced inductionHypothesis =>
      rcases inductionHypothesis with
        ⟨parentAddress, parentCheckpoint, childAddress, childCheckpoint,
          registryResolution⟩
      cases outcome : ChildFrame.outcomeDone _ _ advanced with
      | returned data =>
          exact ⟨by simpa [Anchored, ChildFrame.resumeRoot,
              ChildFrame.selectedParentContext, outcome,
              SuspendedRoot.resumeWith] using parentAddress,
            by simpa [Anchored, ChildFrame.resumeRoot,
              ChildFrame.selectedParentContext, outcome,
              SuspendedRoot.resumeWith] using parentCheckpoint⟩
      | reverted data =>
          exact ⟨by simpa [Anchored, ChildFrame.resumeRoot,
              ChildFrame.selectedParentContext, outcome,
              SuspendedRoot.resumeWith] using parentAddress,
            by simpa [Anchored, ChildFrame.resumeRoot,
              ChildFrame.selectedParentContext, outcome,
              SuspendedRoot.resumeWith] using parentCheckpoint⟩
      | trapped reason =>
          exact ⟨by simpa [Anchored, ChildFrame.resumeRoot,
              ChildFrame.selectedParentContext, outcome,
              SuspendedRoot.resumeWith] using parentAddress,
            by simpa [Anchored, ChildFrame.resumeRoot,
              ChildFrame.selectedParentContext, outcome,
              SuspendedRoot.resumeWith] using parentCheckpoint⟩
  | childNext prior advanced inductionHypothesis =>
      rcases inductionHypothesis with
        ⟨parentAddress, parentCheckpoint, childAddress, childCheckpoint,
          registryResolution⟩
      exact ⟨parentAddress, parentCheckpoint,
        childAddress, childCheckpoint, registryResolution⟩
  | childSuspended prior advanced inductionHypothesis =>
      rcases inductionHypothesis with
        ⟨parentAddress, parentCheckpoint, childAddress, childCheckpoint,
          registryResolution⟩
      exact ⟨parentAddress, parentCheckpoint,
        (ChildFrame.afterHandledSuspension_storageAddress _ _ advanced).trans
          childAddress,
        (congrArg FrameCheckpointSnapshot.state
          (ChildFrame.afterHandledSuspension_checkpoint _ _ advanced)).trans
          childCheckpoint,
        registryResolution⟩

theorem Reachable.root_storageAddress
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {registry : CheckedContractRegistry}
    {frame : RootFrame initialWorld rootContract rootInvocation}
    (reachable : Reachable registry (.root frame)) :
    frame.context.context.storageAddress = rootInvocation.target :=
  reachable.anchored.storageAddress_eq

theorem Reachable.root_checkpointState
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {registry : CheckedContractRegistry}
    {frame : RootFrame initialWorld rootContract rootInvocation}
    (reachable : Reachable registry (.root frame)) :
    frame.context.context.values.checkpoint.state = initialWorld :=
  reachable.anchored.checkpointState_eq

theorem Reachable.child_parentStorageAddress
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {registry : CheckedContractRegistry}
    {frame : ChildFrame initialWorld rootContract rootInvocation}
    (reachable : Reachable registry (.child frame)) :
    frame.suspendedRoot.parentContext.context.storageAddress =
      rootInvocation.target :=
  reachable.anchored.parentStorageAddress_eq

theorem Reachable.child_parentCheckpointState
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {registry : CheckedContractRegistry}
    {frame : ChildFrame initialWorld rootContract rootInvocation}
    (reachable : Reachable registry (.child frame)) :
    frame.suspendedRoot.parentContext.context.values.checkpoint.state =
      initialWorld :=
  reachable.anchored.parentCheckpointState_eq

theorem Reachable.child_storageAddress
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {registry : CheckedContractRegistry}
    {frame : ChildFrame initialWorld rootContract rootInvocation}
    (reachable : Reachable registry (.child frame)) :
    frame.childContext.context.storageAddress = frame.childTarget :=
  reachable.anchored.childStorageAddress_eq

theorem Reachable.child_checkpointState
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {registry : CheckedContractRegistry}
    {frame : ChildFrame initialWorld rootContract rootInvocation}
    (reachable : Reachable registry (.child frame)) :
    frame.childContext.context.values.checkpoint.state =
      frame.childInitialWorld :=
  reachable.anchored.childCheckpointState_eq

/-- A live child is exactly the contract resolved at its frozen call site. -/
theorem Reachable.child_registryResolution
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {registry : CheckedContractRegistry}
    {frame : ChildFrame initialWorld rootContract rootInvocation}
    (reachable : Reachable registry (.child frame)) :
    registry.resolve?
        frame.suspendedRoot.parentContext.context.values.working.1
        frame.childTarget =
      some ⟨frame.childContract, frame.preTransferInstalled⟩ :=
  reachable.anchored.registryResolution_eq

end Solcore.Semantics.OneLevelNestedExecution
