import Solcore.ContractRuntime.OneLevelNestedTransitionSystem
import Solcore.ContractRuntime.BalanceTransfer
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
import Solcore.ContractRuntime.HostStorageContext
import Solcore.ContractRuntime.TopLevelExecution
import Solcore.ContractRuntime.ExecutionEnvironment
import Solcore.ContractRuntime.WorldStateDelta
import Solcore.Core.HostRunner
import Solcore.ContractRuntime.CheckedContractRegistry

/-! Reachability seal for scheduler states produced by checked execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution

/--
Evidence that an active scheduler mode was obtained from an installed root by
only the transitions of the one-level executor under one fixed environment.

This seal prevents low-level frame constructors and transition helpers from
being used to manufacture a resumable state with an unrelated working world.
-/
inductive Reachable
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (environment : ExecutionEnvironment) :
    Mode initialWorld rootContract rootInvocation → Prop where
  | initial
      (installed :
        InstalledCheckedCoreContract initialWorld rootInvocation.target
          rootContract) :
      Reachable environment
        (Mode.initialRoot rootContract rootInvocation installed)
  | balancedInitial
      {workingWorld : WorldState}
      (installed :
        InstalledCheckedCoreContract initialWorld rootInvocation.target
          rootContract)
      (transferred :
        initialWorld.transferBalance rootInvocation.caller
            rootInvocation.target rootInvocation.callValue =
          .ok workingWorld) :
      Reachable environment
        (Mode.preparedRoot rootContract rootInvocation
          (WorldState.transferBalance_preserves_installed transferred
            installed))
  | rootNext
      {frame : RootFrame initialWorld rootContract rootInvocation}
      {next : Core.State}
      (prior : Reachable environment (.root frame))
      (advanced : Core.hostAdvance frame.state = .next next) :
      Reachable environment (.root (frame.afterNext next advanced))
  | rootSuspended
      {frame : RootFrame initialWorld rootContract rootInvocation}
      {suspension : Core.HostSuspension}
      (prior : Reachable environment (.root frame))
      (creatorAddress_eq : rootInvocation.executionInputs.currentAddress =
        frame.context.context.storageAddress)
      (advanced : Core.hostAdvance frame.state = .suspended suspension) :
      Reachable environment
        (frame.afterSuspensionWithEnvironment environment creatorAddress_eq
          suspension advanced)
  | childDone
      {frame : ChildFrame initialWorld rootContract rootInvocation}
      {value : Core.Value}
      (prior : Reachable environment (.child frame))
      (advanced : Core.hostAdvance frame.childState = .done value) :
      Reachable environment
        (.root (frame.resumeRoot (frame.outcomeDone value advanced)))
  | childNext
      {frame : ChildFrame initialWorld rootContract rootInvocation}
      {next : Core.State}
      (prior : Reachable environment (.child frame))
      (advanced : Core.hostAdvance frame.childState = .next next) :
      Reachable environment (.child (frame.afterNext next advanced))
  | childSuspended
      {frame : ChildFrame initialWorld rootContract rootInvocation}
      {suspension : Core.HostSuspension}
      (prior : Reachable environment (.child frame))
      (advanced : Core.hostAdvance frame.childState = .suspended suspension) :
      Reachable environment
        (.child (frame.afterHandledSuspension suspension advanced))
  | initializerDone
      {frame : PreparedInitializerFrame initialWorld rootContract rootInvocation}
      {value : Core.Value}
      (prior : Reachable environment (.initializer frame))
      (advanced : Core.hostAdvance frame.initializerState = .done value) :
      Reachable environment
        (.root
          ((frame.complete (frame.outcomeDone value advanced)).root))
  | initializerNext
      {frame : PreparedInitializerFrame initialWorld rootContract rootInvocation}
      {next : Core.State}
      (prior : Reachable environment (.initializer frame))
      (advanced : Core.hostAdvance frame.initializerState = .next next) :
      Reachable environment (.initializer (frame.afterNext next advanced))
  | initializerSuspended
      {frame : PreparedInitializerFrame initialWorld rootContract rootInvocation}
      {suspension : Core.HostSuspension}
      (prior : Reachable environment (.initializer frame))
      (advanced :
        Core.hostAdvance frame.initializerState = .suspended suspension) :
      Reachable environment
        (.initializer (frame.afterHandledSuspension suspension advanced))

end Solcore.ContractRuntime.OneLevelNestedExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedExecutionReachabilityProperties`
-/

/-! Root and child context provenance derived from scheduler reachability. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution

private theorem transactionHandleRequest_storageAddress
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : TransactionHostStorageDriver.Context)
    (request : Core.HostRequest) :
    (TransactionHostStorageDriver.handleRequest inputs context request).1.context.storageAddress =
      context.context.storageAddress := by
  cases request <;> rfl

private theorem transactionHandleRequest_checkpoint
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : TransactionHostStorageDriver.Context)
    (request : Core.HostRequest) :
    (TransactionHostStorageDriver.handleRequest inputs context request).1.context.values.checkpoint =
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
  exact transactionHandleRequest_storageAddress _ _ _

private theorem ChildFrame.afterHandledSuspension_checkpoint
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (frame : ChildFrame initialWorld rootContract rootInvocation)
    (suspension : Core.HostSuspension)
    (advanced : Core.hostAdvance frame.childState = .suspended suspension) :
    (frame.afterHandledSuspension suspension advanced).childContext.context.values.checkpoint =
      frame.childContext.context.values.checkpoint := by
  exact transactionHandleRequest_checkpoint _ _ _

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
  checkpointJournal_eq :
    frame.context.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty

/-- A reachable child retains both its root origin and its call checkpoint. -/
structure ChildAnchored
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : ExecutionEnvironment)
    (frame : ChildFrame initialWorld rootContract rootInvocation) : Prop where
  parentStorageAddress_eq :
    frame.suspendedRoot.parentContext.context.storageAddress =
      rootInvocation.target
  parentCheckpointState_eq :
    frame.suspendedRoot.parentContext.context.values.checkpoint.state =
      initialWorld
  parentCheckpointJournal_eq :
    frame.suspendedRoot.parentContext.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty
  childStorageAddress_eq :
    frame.childContext.context.storageAddress = frame.childTarget
  childCheckpointState_eq :
    frame.childContext.context.values.checkpoint.state =
      frame.childInitialWorld
  childCheckpointJournal_eq :
    frame.childContext.context.values.checkpoint.effects.rollback =
      frame.suspendedRoot.parentContext.workingJournal
  registryResolution_eq :
    registry.callRegistry.resolve?
        frame.suspendedRoot.parentContext.context.values.working.1
        frame.childTarget =
      some ⟨frame.childContract, frame.preTransferInstalled⟩

/-- A prepared initializer retains its fixed environment and transaction roots. -/
structure InitializerAnchored
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (environment : ExecutionEnvironment)
    (frame : PreparedInitializerFrame initialWorld rootContract rootInvocation) :
    Prop where
  environment_eq : frame.environment = environment
  parentStorageAddress_eq :
    frame.suspendedRoot.parentContext.context.storageAddress =
      rootInvocation.target
  parentCheckpointState_eq :
    frame.suspendedRoot.parentContext.context.values.checkpoint.state =
      initialWorld
  parentCheckpointJournal_eq :
    frame.suspendedRoot.parentContext.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty
  postNonceStorageAddress_eq :
    frame.postNonceParentContext.context.storageAddress = rootInvocation.target
  postNonceCheckpointState_eq :
    frame.postNonceParentContext.context.values.checkpoint.state = initialWorld
  initializerStorageAddress_eq :
    frame.initializerContext.context.storageAddress = frame.prepared.createdAddress
  initializerCheckpointState_eq :
    frame.initializerContext.context.values.checkpoint.state =
      frame.prepared.statePreparation.postNonceWorld
  initializerCheckpointJournal_eq :
    frame.initializerContext.context.values.checkpoint.effects.rollback =
      frame.suspendedRoot.parentContext.workingJournal

/-- Mode-indexed form used for one induction over the transition closure. -/
def Anchored
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : ExecutionEnvironment) :
    Mode initialWorld rootContract rootInvocation → Prop
  | .root frame => RootAnchored frame
  | .child frame => ChildAnchored registry frame
  | .initializer frame => InitializerAnchored registry frame

private theorem rootAfterSuspension_anchored
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : ExecutionEnvironment)
    (frame : RootFrame initialWorld rootContract rootInvocation)
    (suspension : Core.HostSuspension)
    (advanced : Core.hostAdvance frame.state = .suspended suspension)
    (anchored : RootAnchored frame) :
    Anchored registry
      (frame.afterSuspensionWithEnvironment registry
        (by rw [TopLevelInvocation.executionInputs_currentAddress]
            exact anchored.storageAddress_eq.symm)
        suspension advanced) := by
  rcases suspension with ⟨request, continuation, store⟩
  cases request with
  | callContractWord target input =>
      simp only [RootFrame.afterSuspensionWithEnvironment]
      split
      · exact ⟨anchored.storageAddress_eq, anchored.checkpointState_eq,
          anchored.checkpointJournal_eq⟩
      ·
        split
        · exact ⟨anchored.storageAddress_eq, anchored.checkpointState_eq,
            anchored.checkpointJournal_eq⟩
        · exact ⟨anchored.storageAddress_eq,
            anchored.checkpointState_eq, anchored.checkpointJournal_eq,
            rfl, rfl, rfl, by assumption⟩
  | callContractWordWithValue target value input =>
      simp only [RootFrame.afterSuspensionWithEnvironment]
      split
      · exact ⟨anchored.storageAddress_eq, anchored.checkpointState_eq,
          anchored.checkpointJournal_eq⟩
      · split
        · exact ⟨anchored.storageAddress_eq, anchored.checkpointState_eq,
            anchored.checkpointJournal_eq⟩
        · split
          · exact ⟨anchored.storageAddress_eq, anchored.checkpointState_eq,
              anchored.checkpointJournal_eq⟩
          · exact ⟨anchored.storageAddress_eq,
              anchored.checkpointState_eq, anchored.checkpointJournal_eq,
              rfl, rfl, rfl, by assumption⟩
  | createContractWord templateId value input =>
      simp only [RootFrame.afterSuspensionWithEnvironment]
      split
      · exact ⟨anchored.storageAddress_eq, anchored.checkpointState_eq,
          anchored.checkpointJournal_eq⟩
      · exact ⟨rfl, anchored.storageAddress_eq,
          anchored.checkpointState_eq, anchored.checkpointJournal_eq,
          (PreparedInitializerFrame.postNonce_storageAddress_eq _).trans
            anchored.storageAddress_eq,
          (congrArg FrameCheckpointSnapshot.state
            (PreparedInitializerFrame.postNonce_checkpoint_eq _)).trans
            anchored.checkpointState_eq,
          PreparedInitializerFrame.initializer_storageAddress_eq _,
          PreparedInitializerFrame.initializer_checkpointState_eq _, rfl⟩
  | storageRead slot =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq, anchored.checkpointJournal_eq⟩
  | storageWrite slot value =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq, anchored.checkpointJournal_eq⟩
  | storageAddress =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq, anchored.checkpointJournal_eq⟩
  | codeAddress =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq, anchored.checkpointJournal_eq⟩
  | callValue =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq, anchored.checkpointJournal_eq⟩
  | callerAddress =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq, anchored.checkpointJournal_eq⟩
  | inputDataByte? offset =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq, anchored.checkpointJournal_eq⟩
  | inputDataSize =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq, anchored.checkpointJournal_eq⟩
  | inputDataWordBE? offset =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq, anchored.checkpointJournal_eq⟩
  | currentAddress =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq, anchored.checkpointJournal_eq⟩
  | emitLogWord topic payload =>
      exact ⟨anchored.storageAddress_eq,
        anchored.checkpointState_eq, anchored.checkpointJournal_eq⟩

/-- Every scheduler-reachable mode retains its root and call-site anchors. -/
theorem Reachable.anchored
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {registry : ExecutionEnvironment}
    {mode : Mode initialWorld rootContract rootInvocation}
    (reachable : Reachable registry mode) :
    Anchored registry mode := by
  induction reachable with
  | initial installed =>
      exact ⟨rfl, rfl, rfl⟩
  | balancedInitial installed transferred =>
      exact ⟨rfl, rfl, rfl⟩
  | rootNext prior advanced inductionHypothesis =>
      rcases inductionHypothesis with ⟨address, checkpoint, journal⟩
      exact ⟨address, checkpoint, journal⟩
  | rootSuspended prior creatorAddress_eq advanced inductionHypothesis =>
      exact rootAfterSuspension_anchored _ _ _ advanced
        inductionHypothesis
  | childDone prior advanced inductionHypothesis =>
      rcases inductionHypothesis with
        ⟨parentAddress, parentCheckpoint, parentJournal, childAddress, childCheckpoint,
          childJournalCheckpoint, registryResolution⟩
      cases outcome : ChildFrame.outcomeDone _ _ advanced with
      | returned data =>
          exact ⟨by simpa [Anchored, ChildFrame.resumeRoot,
              ChildFrame.selectedParentContext, outcome,
              SuspendedRoot.resumeWith] using parentAddress,
            by simpa [Anchored, ChildFrame.resumeRoot,
              ChildFrame.selectedParentContext, outcome,
              SuspendedRoot.resumeWith] using parentCheckpoint,
            by simpa [Anchored, ChildFrame.resumeRoot,
              ChildFrame.selectedParentContext, outcome,
              SuspendedRoot.resumeWith] using parentJournal⟩
      | reverted data =>
          exact ⟨by simpa [Anchored, ChildFrame.resumeRoot,
              ChildFrame.selectedParentContext, outcome,
              SuspendedRoot.resumeWith] using parentAddress,
            by simpa [Anchored, ChildFrame.resumeRoot,
              ChildFrame.selectedParentContext, outcome,
              SuspendedRoot.resumeWith] using parentCheckpoint,
            by simpa [Anchored, ChildFrame.resumeRoot,
              ChildFrame.selectedParentContext, outcome,
              SuspendedRoot.resumeWith] using parentJournal⟩
      | trapped reason =>
          exact ⟨by simpa [Anchored, ChildFrame.resumeRoot,
              ChildFrame.selectedParentContext, outcome,
              SuspendedRoot.resumeWith] using parentAddress,
            by simpa [Anchored, ChildFrame.resumeRoot,
              ChildFrame.selectedParentContext, outcome,
              SuspendedRoot.resumeWith] using parentCheckpoint,
            by simpa [Anchored, ChildFrame.resumeRoot,
              ChildFrame.selectedParentContext, outcome,
              SuspendedRoot.resumeWith] using parentJournal⟩
  | childNext prior advanced inductionHypothesis =>
      rcases inductionHypothesis with
        ⟨parentAddress, parentCheckpoint, parentJournal, childAddress, childCheckpoint,
          childJournalCheckpoint, registryResolution⟩
      exact ⟨parentAddress, parentCheckpoint, parentJournal,
        childAddress, childCheckpoint, childJournalCheckpoint,
        registryResolution⟩
  | childSuspended prior advanced inductionHypothesis =>
      rcases inductionHypothesis with
        ⟨parentAddress, parentCheckpoint, parentJournal, childAddress, childCheckpoint,
          childJournalCheckpoint, registryResolution⟩
      exact ⟨parentAddress, parentCheckpoint, parentJournal,
        (ChildFrame.afterHandledSuspension_storageAddress _ _ advanced).trans
          childAddress,
        (congrArg FrameCheckpointSnapshot.state
          (ChildFrame.afterHandledSuspension_checkpoint _ _ advanced)).trans
          childCheckpoint,
        (congrArg
          (fun checkpoint => checkpoint.effects.rollback)
          (ChildFrame.afterHandledSuspension_checkpoint _ _ advanced)).trans
          childJournalCheckpoint,
        registryResolution⟩
  | initializerDone prior advanced inductionHypothesis =>
      exact ⟨InitializerCompletionResult.root_storageAddress _ |>.trans
          inductionHypothesis.parentStorageAddress_eq,
        InitializerCompletionResult.root_checkpointState _ |>.trans
          inductionHypothesis.parentCheckpointState_eq,
        (congrArg
          (fun checkpoint => checkpoint.effects.rollback)
          (InitializerCompletionResult.root_checkpoint _)).trans
          inductionHypothesis.parentCheckpointJournal_eq⟩
  | initializerNext prior advanced inductionHypothesis =>
      exact { inductionHypothesis with }
  | initializerSuspended prior advanced inductionHypothesis =>
      exact { inductionHypothesis with
        initializerStorageAddress_eq :=
          (transactionHandleRequest_storageAddress _ _ _).trans
            inductionHypothesis.initializerStorageAddress_eq
        initializerCheckpointState_eq :=
          (congrArg FrameCheckpointSnapshot.state
            (transactionHandleRequest_checkpoint _ _ _)).trans
            inductionHypothesis.initializerCheckpointState_eq
        initializerCheckpointJournal_eq :=
          (congrArg
            (fun checkpoint => checkpoint.effects.rollback)
            (transactionHandleRequest_checkpoint _ _ _)).trans
            inductionHypothesis.initializerCheckpointJournal_eq }

theorem Reachable.root_storageAddress
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {registry : ExecutionEnvironment}
    {frame : RootFrame initialWorld rootContract rootInvocation}
    (reachable : Reachable registry (.root frame)) :
    frame.context.context.storageAddress = rootInvocation.target :=
  reachable.anchored.storageAddress_eq

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

namespace Solcore.ContractRuntime.OneLevelNestedExecution

/--
A terminal root result with exact speculative and externally committed world
endpoints. The outcome determines which endpoint the executor selects.
-/
structure TerminalResult
    (initialWorld : WorldState)
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation) where
  terminalContext : TransactionHostStorageDriver.Context
  coreValue : Core.Value
  coreStore : Core.Store
  outcome : FrameOutcome Core.Word
  finalWorld : WorldState
  workingJournal : TransactionJournal
  workingJournal_eq :
    workingJournal = terminalContext.workingJournal
  committedJournal : TransactionJournal
  committedJournal_eq :
    committedJournal =
      match outcome with
      | .returned _ => terminalContext.workingJournal
      | .reverted _ => terminalContext.context.values.checkpoint.effects.rollback
      | .trapped _ => terminalContext.context.values.checkpoint.effects.rollback
  workingDelta :
    WorldStateDelta initialWorld
      terminalContext.context.values.working.1
  committedDelta : WorldStateDelta initialWorld finalWorld

/-- Observable classification of one sealed nested execution result. -/
inductive ResultView
    (initialWorld : WorldState)
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation) where
  | completed
      (terminal : TerminalResult initialWorld rootContract rootInvocation)
  | outOfFuel
      (environment : ExecutionEnvironment)
      (mode : Mode initialWorld rootContract rootInvocation)
      (reachable : Reachable environment mode)

end Solcore.ContractRuntime.OneLevelNestedExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedExecution`
-/

/-! Shared-fuel execution for one root and one active leaf child. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution

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

end Solcore.ContractRuntime.OneLevelNestedExecution

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

namespace Solcore.ContractRuntime.OneLevelNestedExecution

/--
Keep a terminal result stable, or continue its exact retained scheduler mode
with one additional shared-fuel budget.
-/
def resumeWithFuel
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (additional : Nat) :
    Result initialWorld rootContract rootInvocation :=
  match result.view with
  | .completed _terminal => result
  | .outOfFuel environment mode reachable =>
      runMode environment additional mode reachable

end Solcore.ContractRuntime.OneLevelNestedExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedExecutionResumptionProperties`
-/

/-! Exact split-fuel laws for one-level nested checked-Core execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution

/-- Resuming an actual bounded run is exactly one run at the summed budget. -/
theorem resumeWithFuel_runMode
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : ExecutionEnvironment)
    (fuel additional : Nat)
    (mode : Mode initialWorld rootContract rootInvocation)
    (reachable : Reachable registry mode) :
    resumeWithFuel (runMode registry fuel mode reachable) additional =
      runMode registry (fuel + additional) mode reachable := by
  induction fuel, mode, reachable using runMode.induct registry
      generalizing additional with
  | case1 fuel frame reachable value stepEq active =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixView :
          (runMode registry fuel (.root frame) reachable).view =
            .completed (frame.finalizeDone value stepEq) := by
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      have summedView :
          (runMode registry (fuel + additional) (.root frame) reachable).view =
            .completed (frame.finalizeDone value stepEq) := by
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      apply Result.eq_of_view_eq
      simp [resumeWithFuel, prefixView, summedView]
  | case2 frame reachable next stepEq active =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixView :
          (runMode registry 0 (.root frame) reachable).view =
            .outOfFuel registry (.root frame) reachable := by
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      apply Result.eq_of_view_eq
      simp [resumeWithFuel, prefixView]
  | case3 frame reachable next stepEq remaining active ih =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixEq :
          runMode registry remaining.succ (.root frame) reachable =
            runMode registry remaining
              (.root (frame.afterNext next stepEq))
              (.rootNext reachable stepEq) := by
        apply Result.eq_of_view_eq
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      have summedEq :
          runMode registry (remaining.succ + additional) (.root frame)
              reachable =
            runMode registry (remaining + additional)
              (.root (frame.afterNext next stepEq))
              (.rootNext reachable stepEq) := by
        rw [Nat.succ_add]
        apply Result.eq_of_view_eq
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq, summedEq]
      exact ih additional
  | case4 frame reachable suspension stepEq active =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixView :
          (runMode registry 0 (.root frame) reachable).view =
            .outOfFuel registry (.root frame) reachable := by
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      apply Result.eq_of_view_eq
      simp [resumeWithFuel, prefixView]
  | case5 frame reachable suspension stepEq remaining creatorAddress_eq active ih =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixEq :
          runMode registry remaining.succ (.root frame) reachable =
            runMode registry remaining
              (frame.afterSuspensionWithEnvironment registry creatorAddress_eq
                suspension stepEq)
              (.rootSuspended reachable creatorAddress_eq stepEq) := by
        apply Result.eq_of_view_eq
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      have summedEq :
          runMode registry (remaining.succ + additional) (.root frame)
              reachable =
            runMode registry (remaining + additional)
              (frame.afterSuspensionWithEnvironment registry creatorAddress_eq
                suspension stepEq)
              (.rootSuspended reachable creatorAddress_eq stepEq) := by
        rw [Nat.succ_add]
        apply Result.eq_of_view_eq
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq, summedEq]
      exact ih additional
  | case6 fuel frame reachable value stepEq active ih =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixEq :
          runMode registry fuel (.child frame) reachable =
            runMode registry fuel
              (.root (frame.resumeRoot (frame.outcomeDone value stepEq)))
              (.childDone reachable stepEq) := by
        apply Result.eq_of_view_eq
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      have summedEq :
          runMode registry (fuel + additional) (.child frame) reachable =
            runMode registry (fuel + additional)
              (.root (frame.resumeRoot (frame.outcomeDone value stepEq)))
              (.childDone reachable stepEq) := by
        apply Result.eq_of_view_eq
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq, summedEq]
      exact ih additional
  | case7 frame reachable next stepEq active =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixView :
          (runMode registry 0 (.child frame) reachable).view =
            .outOfFuel registry (.child frame) reachable := by
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      apply Result.eq_of_view_eq
      simp [resumeWithFuel, prefixView]
  | case8 frame reachable next stepEq remaining active ih =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixEq :
          runMode registry remaining.succ (.child frame) reachable =
            runMode registry remaining
              (.child (frame.afterNext next stepEq))
              (.childNext reachable stepEq) := by
        apply Result.eq_of_view_eq
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      have summedEq :
          runMode registry (remaining.succ + additional) (.child frame)
              reachable =
            runMode registry (remaining + additional)
              (.child (frame.afterNext next stepEq))
              (.childNext reachable stepEq) := by
        rw [Nat.succ_add]
        apply Result.eq_of_view_eq
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq, summedEq]
      exact ih additional
  | case9 frame reachable suspension stepEq active =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixView :
          (runMode registry 0 (.child frame) reachable).view =
            .outOfFuel registry (.child frame) reachable := by
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      apply Result.eq_of_view_eq
      simp [resumeWithFuel, prefixView]
  | case10 frame reachable suspension stepEq remaining active ih =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixEq :
          runMode registry remaining.succ (.child frame) reachable =
            runMode registry remaining
              (.child (frame.afterHandledSuspension suspension stepEq))
              (.childSuspended reachable stepEq) := by
        apply Result.eq_of_view_eq
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      have summedEq :
          runMode registry (remaining.succ + additional) (.child frame)
              reachable =
            runMode registry (remaining + additional)
              (.child (frame.afterHandledSuspension suspension stepEq))
              (.childSuspended reachable stepEq) := by
        rw [Nat.succ_add]
        apply Result.eq_of_view_eq
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq, summedEq]
      exact ih additional
  | case11 fuel frame reachable value stepEq completion active ih =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixEq :
          runMode registry fuel (.initializer frame) reachable =
            runMode registry fuel (.root completion.root)
              (.initializerDone reachable stepEq) := by
        apply Result.eq_of_view_eq
        rw [runMode.eq_3]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      have summedEq :
          runMode registry (fuel + additional) (.initializer frame) reachable =
            runMode registry (fuel + additional) (.root completion.root)
              (.initializerDone reachable stepEq) := by
        apply Result.eq_of_view_eq
        rw [runMode.eq_3]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq, summedEq]
      exact ih additional
  | case12 frame reachable next stepEq active =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixView :
          (runMode registry 0 (.initializer frame) reachable).view =
            .outOfFuel registry (.initializer frame) reachable := by
        rw [runMode.eq_3]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      apply Result.eq_of_view_eq
      simp [resumeWithFuel, prefixView]
  | case13 frame reachable next stepEq remaining active ih =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixEq :
          runMode registry remaining.succ (.initializer frame) reachable =
            runMode registry remaining
              (.initializer (frame.afterNext next stepEq))
              (.initializerNext reachable stepEq) := by
        apply Result.eq_of_view_eq
        rw [runMode.eq_3]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      have summedEq :
          runMode registry (remaining.succ + additional)
              (.initializer frame) reachable =
            runMode registry (remaining + additional)
              (.initializer (frame.afterNext next stepEq))
              (.initializerNext reachable stepEq) := by
        rw [Nat.succ_add]
        apply Result.eq_of_view_eq
        rw [runMode.eq_3]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq, summedEq]
      exact ih additional
  | case14 frame reachable suspension stepEq active =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixView :
          (runMode registry 0 (.initializer frame) reachable).view =
            .outOfFuel registry (.initializer frame) reachable := by
        rw [runMode.eq_3]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      apply Result.eq_of_view_eq
      simp [resumeWithFuel, prefixView]
  | case15 frame reachable suspension stepEq remaining active ih =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixEq :
          runMode registry remaining.succ (.initializer frame) reachable =
            runMode registry remaining
              (.initializer (frame.afterHandledSuspension suspension stepEq))
              (.initializerSuspended reachable stepEq) := by
        apply Result.eq_of_view_eq
        rw [runMode.eq_3]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      have summedEq :
          runMode registry (remaining.succ + additional)
              (.initializer frame) reachable =
            runMode registry (remaining + additional)
              (.initializer (frame.afterHandledSuspension suspension stepEq))
              (.initializerSuspended reachable stepEq) := by
        rw [Nat.succ_add]
        apply Result.eq_of_view_eq
        rw [runMode.eq_3]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq, summedEq]
      exact ih additional

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

/-- Splitting fuel at the calls-only compatibility API is exact. -/
theorem resumeWithFuel_run
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (registry : CheckedContractRegistry)
    (fuel additional : Nat) :
    resumeWithFuel
        (run rootContract rootInvocation installed registry fuel) additional =
      run rootContract rootInvocation installed registry
        (fuel + additional) := by
  exact resumeWithFuel_runMode (.callsOnly registry) fuel additional
    (Mode.initialRoot rootContract rootInvocation installed)
    (.initial installed)

/-- Zero additional fuel is an identity for every installed-root run. -/
@[simp] theorem resumeWithFuel_run_zero
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (registry : CheckedContractRegistry)
    (fuel : Nat) :
    resumeWithFuel
        (run rootContract rootInvocation installed registry fuel) 0 =
      run rootContract rootInvocation installed registry fuel := by
  rw [resumeWithFuel_run]
  simp only [Nat.add_zero]

/-- Sequential resumption at the public API uses the summed shared budget. -/
theorem resumeWithFuel_run_add
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (registry : CheckedContractRegistry)
    (fuel first second : Nat) :
    resumeWithFuel
        (resumeWithFuel
          (run rootContract rootInvocation installed registry fuel) first)
        second =
      run rootContract rootInvocation installed registry
        (fuel + first + second) := by
  rw [resumeWithFuel_run, resumeWithFuel_run]

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
