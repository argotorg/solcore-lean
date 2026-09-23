import Solcore.ContractRuntime.CheckedHostCoreProgram
import Solcore.ContractRuntime.NestedWordCall
import Solcore.ContractRuntime.CheckedCreationPreflight
import Solcore.Core.HostRunner
import Solcore.Core.HostTransitionSafety
import Solcore.ContractRuntime.CheckedCoreWordOutcome
import Solcore.ContractRuntime.BalanceTransfer
import Solcore.ContractRuntime.CheckedAccountCreation
import Solcore.ContractRuntime.HostStorageAccountPresence
import Solcore.ContractRuntime.TransactionHostStorage
import Solcore.ContractRuntime.WorldStateCode
import Solcore.ContractRuntime.TransactionJournal
import Solcore.ContractRuntime.CheckedContractRegistry
import Solcore.ContractRuntime.ContractCallFailure
import Solcore.ContractRuntime.ExecutionEnvironment

/-! State and transition rules for one-level nested contract execution. -/

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedExecutionState`
-/

/-! Typed root and child states for one-level nested checked-Core execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution

/-- A running root machine paired with its observable transaction context. -/
structure RootFrame
    (initialWorld : WorldState)
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation) where
  context : TransactionHostStorageDriver.Context
  state : Core.State
  stateTyping :
    Core.HostStateHasType state rootContract.code.program.resultType
      rootContract.code.program.dataDefinitions

namespace RootFrame

/-- Start the root machine from the installed contract and explicit world. -/
def initial
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract) :
    RootFrame initialWorld rootContract rootInvocation := {
  context := TopLevelExecution.initialTransactionContext installed
  state :=
    Core.State.initial rootContract.code.program.body Core.hostEnvironment
  stateTyping := rootContract.code.initialState_hasType
}

/--
Start a root from a prepared working world while retaining a distinct original
world as the transaction checkpoint.
-/
def prepared
    {checkpointWorld workingWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract workingWorld rootInvocation.target
        rootContract) :
    RootFrame checkpointWorld rootContract rootInvocation := {
  context :=
    TopLevelExecution.preparedTransactionContext
      (checkpointWorld := checkpointWorld) installed
  state :=
    Core.State.initial rootContract.code.program.body Core.hostEnvironment
  stateTyping := rootContract.code.initialState_hasType
}

end RootFrame

/-- The two root requests intercepted by the depth-one scheduler. -/
inductive CallProfile where
  | legacy (target input : Core.Word)
  | withValue (target value input : Core.Word)

namespace CallProfile

def request : CallProfile → Core.HostRequest
  | .legacy target input => .callContractWord target input
  | .withValue target value input =>
      .callContractWordWithValue target value input

def response
    (profile : CallProfile)
    (result : Core.ContractCallWordResult) : profile.request.Response := by
  cases profile <;> exact result

def target : CallProfile → Core.Word
  | .legacy target _ => target
  | .withValue target _ _ => target

def input : CallProfile → Core.Word
  | .legacy _ input => input
  | .withValue _ _ input => input

def invocation
    (profile : CallProfile)
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address) : TopLevelInvocation :=
  match profile with
  | .legacy _ input => TopLevelInvocation.childWord parentInputs target input
  | .withValue _ value input =>
      TopLevelInvocation.childWordWithValue parentInputs target value input

end CallProfile

/--
The exact root call suspension retained while its selected child is running.
No response has yet been injected into this continuation.
-/
structure SuspendedRoot
    (initialWorld : WorldState)
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation) where
  parentContext : TransactionHostStorageDriver.Context
  call : CallProfile
  continuation : List Core.Frame
  store : Core.Store
  suspensionTyping :
    Core.HostSuspensionHasType
      ⟨call.request, continuation, store⟩
      rootContract.code.program.resultType
      rootContract.code.program.dataDefinitions

namespace SuspendedRoot

/-- Reconstruct the exact Core suspension represented by this carrier. -/
def suspension
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (root : SuspendedRoot initialWorld rootContract rootInvocation) :
    Core.HostSuspension :=
  ⟨root.call.request, root.continuation, root.store⟩

end SuspendedRoot

/--
A running resolved child and the untouched root suspension waiting for its
typed call response. The selected Account witness makes both self-call and
cross-account rebasing proof-total when the child later completes.
-/
structure ChildFrame
    (initialWorld : WorldState)
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation) where
  suspendedRoot : SuspendedRoot initialWorld rootContract rootInvocation
  childTarget : Address
  targetAddress_eq :
    wordToAddress? suspendedRoot.call.target = some childTarget
  childContract : CheckedCoreContract
  preTransferInstalled :
    InstalledCheckedCoreContract
      suspendedRoot.parentContext.context.values.working.1 childTarget
      childContract
  childInitialWorld : WorldState
  childInvocation : TopLevelInvocation
  installed :
    InstalledCheckedCoreContract
      childInitialWorld childTarget
      childContract
  childInvocation_eq :
    childInvocation =
      suspendedRoot.call.invocation rootInvocation.executionInputs childTarget
  childContext : TransactionHostStorageDriver.Context
  childState : Core.State
  childStateTyping :
    Core.HostStateHasType childState childContract.code.program.resultType
      childContract.code.program.dataDefinitions
  parentStorageAccount : Account
  parentStorageAccount_present :
    childContext.context.values.working.1.account?
        suspendedRoot.parentContext.context.storageAddress =
      some parentStorageAccount

end Solcore.ContractRuntime.OneLevelNestedExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedCreationState`
-/

/-! Proof-carrying scheduler state for one prepared contract initializer. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution

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
  parentContext : TransactionHostStorageDriver.Context
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
  postNonceParentContext : TransactionHostStorageDriver.Context
  postNonce_storageAddress_eq :
    postNonceParentContext.context.storageAddress =
      suspendedRoot.parentContext.context.storageAddress
  postNonce_workingWorld_eq :
    postNonceParentContext.context.values.working.1 =
      prepared.statePreparation.postNonceWorld
  postNonce_checkpoint_eq :
    postNonceParentContext.context.values.checkpoint =
      suspendedRoot.parentContext.context.values.checkpoint
  initializerContext : TransactionHostStorageDriver.Context
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

end Solcore.ContractRuntime.OneLevelNestedExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedExecutionMode`
-/

/-! Active modes of the one-level checked-Core scheduler. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution

/-- The currently active machine in the one-level scheduler. -/
inductive Mode
    (initialWorld : WorldState)
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation) where
  | root (frame : RootFrame initialWorld rootContract rootInvocation)
  | child (frame : ChildFrame initialWorld rootContract rootInvocation)
  | initializer
      (frame :
        PreparedInitializerFrame initialWorld rootContract rootInvocation)

namespace Mode

/-- Construct the initial active-root mode from exact installation evidence. -/
def initialRoot
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract) :
    Mode initialWorld rootContract rootInvocation :=
  .root (RootFrame.initial rootContract rootInvocation installed)

/-- Construct an active root over a prepared post-transfer working world. -/
def preparedRoot
    {checkpointWorld workingWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract workingWorld rootInvocation.target
        rootContract) :
    Mode checkpointWorld rootContract rootInvocation :=
  .root
    (RootFrame.prepared
      (checkpointWorld := checkpointWorld) rootContract rootInvocation
      installed)

/-- Administrative rank used with shared fuel to justify mode switching. -/
def rank
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation} :
    Mode initialWorld rootContract rootInvocation → Nat
  | .root _ => 0
  | .child _ => 1
  | .initializer _ => 1

theorem rank_le_one
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (mode : Mode initialWorld rootContract rootInvocation) :
    mode.rank ≤ 1 := by
  cases mode <;> simp [rank]

end Mode

end Solcore.ContractRuntime.OneLevelNestedExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedCreationTransitions`
-/

/-! Lifecycle helpers for one prepared checked contract initializer. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution

private theorem handleRequest_storageAddress
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : TransactionHostStorageDriver.Context)
    (request : Core.HostRequest) :
    (TransactionHostStorageDriver.handleRequest inputs context request).1.context.storageAddress =
      context.context.storageAddress := by
  cases request <;> rfl

private theorem handleRequest_checkpointState
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : TransactionHostStorageDriver.Context)
    (request : Core.HostRequest) :
    (TransactionHostStorageDriver.handleRequest inputs context request).1.context.values.checkpoint.state =
      context.context.values.checkpoint.state := by
  cases request <;> rfl

private def afterTransactionHandleRequestPresence
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : TransactionHostStorageDriver.Context)
    (request : Core.HostRequest)
    (address : Address)
    (presence : PresentAccountAt context.context.values.working.1 address) :
    PresentAccountAt
      (TransactionHostStorageDriver.handleRequest inputs context request).1.context.values.working.1
      address := by
  cases request with
  | storageRead slot =>
      exact presence.afterHandleRequest inputs context (.storageRead slot) address
  | storageWrite slot value =>
      exact presence.afterHandleRequest inputs context
        (.storageWrite slot value) address
  | storageAddress =>
      exact presence.afterHandleRequest inputs context .storageAddress address
  | codeAddress =>
      exact presence.afterHandleRequest inputs context .codeAddress address
  | callValue =>
      exact presence.afterHandleRequest inputs context .callValue address
  | callerAddress =>
      exact presence.afterHandleRequest inputs context .callerAddress address
  | inputDataByte? offset =>
      exact presence.afterHandleRequest inputs context
        (.inputDataByte? offset) address
  | inputDataSize =>
      exact presence.afterHandleRequest inputs context .inputDataSize address
  | inputDataWordBE? offset =>
      exact presence.afterHandleRequest inputs context
        (.inputDataWordBE? offset) address
  | currentAddress =>
      exact presence.afterHandleRequest inputs context .currentAddress address
  | callContractWord target input =>
      exact presence.afterHandleRequest inputs context
        (.callContractWord target input) address
  | callContractWordWithValue target value input =>
      exact presence.afterHandleRequest inputs context
        (.callContractWordWithValue target value input) address
  | createContractWord templateId value input =>
      exact presence.afterHandleRequest inputs context
        (.createContractWord templateId value input) address
  | emitLogWord topic payload =>
      exact ⟨presence.account, by
        simpa [TransactionHostStorageDriver.handleRequest,
          TransactionHostStorageDriver.Context.recordLog,
          TransactionHostStorageDriver.Context.withWorkingJournal] using
            presence.present⟩

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
  let inheritedJournal := root.parentContext.workingJournal
  let initializerContext :=
    TopLevelExecution.preparedTransactionContextWithJournals
      (checkpointWorld := statePreparation.postNonceWorld)
      inheritedJournal inheritedJournal statePreparation.initializerInstalled
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
        TopLevelExecution.preparedTransactionContextWithJournals,
        TopLevelExecution.preparedTransactionValuesWithJournals] using
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
        TopLevelExecution.preparedTransactionContextWithJournals,
        TopLevelExecution.preparedTransactionValuesWithJournals] using
          initializerParentPresence.present
  }

@[simp] theorem startInitializer_postNonce_workingJournal
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
    (root.startInitializer environment prepared creatorAddress_eq).postNonceParentContext.workingJournal =
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
    (creatorAddress_eq : rootInvocation.executionInputs.currentAddress =
      root.parentContext.context.storageAddress) :
    (root.startInitializer environment prepared creatorAddress_eq).initializerContext.context.values.checkpoint.effects.rollback =
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
    (creatorAddress_eq : rootInvocation.executionInputs.currentAddress =
      root.parentContext.context.storageAddress) :
    (root.startInitializer environment prepared creatorAddress_eq).initializerContext.workingJournal =
      root.parentContext.workingJournal := by
  rfl

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
  let requestResult := TransactionHostStorageDriver.handleRequest
    frame.initializerInvocation.executionInputs frame.initializerContext
      suspension.request
  let typing := Core.hostAdvance_suspended_hasType
    frame.initializerStateTyping advanced
  let parentPresence : PresentAccountAt
      frame.initializerContext.context.values.working.1
      frame.suspendedRoot.parentContext.context.storageAddress :=
    ⟨frame.parentAccount, frame.parentAccount_present⟩
  let nextPresence := afterTransactionHandleRequestPresence
    frame.initializerInvocation.executionInputs frame.initializerContext
      suspension.request
      frame.suspendedRoot.parentContext.context.storageAddress
      parentPresence
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
end Solcore.ContractRuntime.OneLevelNestedExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedCreationCompletion`
-/

/-! Terminal resolution for one prepared checked contract initializer. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution

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
  resumedRoot_checkpoint_eq :
    resumedRoot.context.context.values.checkpoint =
      frame.suspendedRoot.parentContext.context.values.checkpoint
  resumedRoot_workingJournal_eq :
    resumedRoot.context.workingJournal =
      frame.initializerContext.workingJournal.recordCreatedContract
        frame.prepared.createdAddress
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
  let completedJournal :=
    frame.initializerContext.workingJournal.recordCreatedContract
      frame.prepared.createdAddress
  let completedEffects : FrameEffectJournal TransactionJournal Unit :=
    ⟨completedJournal, ()⟩
  let parentContext := frame.postNonceParentContext.rebaseWorkingWithEffects
    deployedWorld completedEffects frame.parentAccount
      parentPresentAtPostNonceSelector
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
    resumedRoot_checkpoint_eq := frame.postNonce_checkpoint_eq
    resumedRoot_workingJournal_eq := rfl
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

@[simp] theorem root_checkpoint
    {initialWorld : WorldState} {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    {frame : PreparedInitializerFrame initialWorld rootContract rootInvocation}
    (result :
      InitializerCompletionResult initialWorld rootContract rootInvocation frame) :
    result.root.context.context.values.checkpoint =
      frame.suspendedRoot.parentContext.context.values.checkpoint := by
  cases result with
  | returned deployed =>
      exact deployed.resumedRoot_checkpoint_eq
  | reverted data resumed context_eq response_eq =>
      simp only [root]
      rw [context_eq]
      exact frame.postNonce_checkpoint_eq
  | trapped reason resumed context_eq response_eq =>
      simp only [root]
      rw [context_eq]
      exact frame.postNonce_checkpoint_eq

end InitializerCompletionResult
end Solcore.ContractRuntime.OneLevelNestedExecution

/-!
## Consolidated module: `Solcore.ContractRuntime.OneLevelNestedExecutionTransitions`
-/

/-! Proof-preserving local transitions for the one-level nested scheduler. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution

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
    TransactionHostStorageDriver.handleRequest rootInvocation.executionInputs
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
    (context : TransactionHostStorageDriver.Context)
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
  let inheritedJournal := root.parentContext.workingJournal
  let childContext :=
    TopLevelExecution.preparedTransactionContextWithJournals
      (checkpointWorld := childInitialWorld)
      (workingWorld := childInitialWorld)
      inheritedJournal inheritedJournal installed
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
      simpa [childContext,
        TopLevelExecution.preparedTransactionContextWithJournals,
        TopLevelExecution.preparedTransactionValuesWithJournals] using
          parentPresence.present
  }

@[simp] theorem startChild_checkpointJournal
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
    (root.startChild target targetAddress_eq childContract preTransferInstalled
      childInitialWorld installed parentPresence).childContext.context.values.checkpoint.effects.rollback =
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
    (preTransferInstalled : InstalledCheckedCoreContract
      root.parentContext.context.values.working.1 target childContract)
    (childInitialWorld : WorldState)
    (installed : InstalledCheckedCoreContract childInitialWorld target childContract)
    (parentPresence : PresentAccountAt childInitialWorld
      root.parentContext.context.storageAddress) :
    (root.startChild target targetAddress_eq childContract preTransferInstalled
      childInitialWorld installed parentPresence).childContext.workingJournal =
        root.parentContext.workingJournal := by
  rfl

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
  | emitLogWord topic payload =>
      exact .root (frame.afterHandledSuspension
        ⟨.emitLogWord topic payload, continuation, store⟩ advanced)

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

private def afterTransactionHandleRequestPresenceForExecution
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : TransactionHostStorageDriver.Context)
    (request : Core.HostRequest)
    (address : Address)
    (presence : PresentAccountAt context.context.values.working.1 address) :
    PresentAccountAt
      (TransactionHostStorageDriver.handleRequest inputs context request).1.context.values.working.1
      address := by
  cases request with
  | storageRead slot =>
      exact presence.afterHandleRequest inputs context (.storageRead slot) address
  | storageWrite slot value =>
      exact presence.afterHandleRequest inputs context
        (.storageWrite slot value) address
  | storageAddress =>
      exact presence.afterHandleRequest inputs context .storageAddress address
  | codeAddress =>
      exact presence.afterHandleRequest inputs context .codeAddress address
  | callValue =>
      exact presence.afterHandleRequest inputs context .callValue address
  | callerAddress =>
      exact presence.afterHandleRequest inputs context .callerAddress address
  | inputDataByte? offset =>
      exact presence.afterHandleRequest inputs context
        (.inputDataByte? offset) address
  | inputDataSize =>
      exact presence.afterHandleRequest inputs context .inputDataSize address
  | inputDataWordBE? offset =>
      exact presence.afterHandleRequest inputs context
        (.inputDataWordBE? offset) address
  | currentAddress =>
      exact presence.afterHandleRequest inputs context .currentAddress address
  | callContractWord target input =>
      exact presence.afterHandleRequest inputs context
        (.callContractWord target input) address
  | callContractWordWithValue target value input =>
      exact presence.afterHandleRequest inputs context
        (.callContractWordWithValue target value input) address
  | createContractWord templateId value input =>
      exact presence.afterHandleRequest inputs context
        (.createContractWord templateId value input) address
  | emitLogWord topic payload =>
      exact ⟨presence.account, by
        simpa [TransactionHostStorageDriver.handleRequest,
          TransactionHostStorageDriver.Context.recordLog,
          TransactionHostStorageDriver.Context.withWorkingJournal] using
            presence.present⟩

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
    TransactionHostStorageDriver.handleRequest
      frame.childInvocation.executionInputs
      frame.childContext suspension.request
  let suspensionTyping :=
    Core.hostAdvance_suspended_hasType frame.childStateTyping advanced
  let parentPresence :
      PresentAccountAt frame.childContext.context.values.working.1
        frame.suspendedRoot.parentContext.context.storageAddress :=
    ⟨frame.parentStorageAccount, frame.parentStorageAccount_present⟩
  let nextPresence := afterTransactionHandleRequestPresenceForExecution
    frame.childInvocation.executionInputs frame.childContext
      suspension.request
      frame.suspendedRoot.parentContext.context.storageAddress
      parentPresence
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
    CheckedCoreWordOutcome → TransactionHostStorageDriver.Context
  | .returned _ =>
      frame.suspendedRoot.parentContext.rebaseWorkingWithEffects
        frame.childContext.context.values.working.1
        frame.childContext.context.values.working.2
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

end Solcore.ContractRuntime.OneLevelNestedExecution
