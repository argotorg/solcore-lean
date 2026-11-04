import Solcore.ContractRuntime.Contracts
import Solcore.Core.Syntax
import Solcore.Core.HostMachine
import Solcore.ContractRuntime.RuntimeScalars
import Solcore.ContractRuntime.StorageDriver
import Solcore.ContractRuntime.Transactions
import Solcore.ContractRuntime.WorldState
import Solcore.Core.Machine
import Solcore.Core.HostTyping
import Solcore.ContractRuntime.TopLevel
import Solcore.ContractRuntime.Internal.WorldStateLaws
import Solcore.Core.Host
import Solcore.ContractRuntime.Frames
import Solcore.ContractRuntime.Creation
import Solcore.Core.Internal.HostPreservation
import Solcore.ContractRuntime.Internal.CreationLaws
import Solcore.ContractRuntime.Internal.TopLevelLaws
import Solcore.Core.HostRunner
import Solcore.Core.Typing

/-!
# One-level nested execution

A root contract that can call a child or create a contract, one level deep.
`OneLevelNestedExecution.Mode` is the scheduler's state, with `OneLevelNestedExecution.RootFrame`,
`OneLevelNestedExecution.ChildFrame` and `OneLevelNestedExecution.PreparedInitializerFrame`.
`OneLevelNestedExecution.runMode`, `OneLevelNestedExecution.run`,
`OneLevelNestedExecution.runWithEnvironment` and `OneLevelNestedExecution.resumeWithFuel` run it.
`OneLevelNestedExecution.Reachable` is evidence that a mode came from an installed root by the
executor's own transitions. `OneLevelNestedExecution.Result` has a private constructor, so the
theorems that build one stay in this file.

Main theorems: `OneLevelNestedExecution.resumeWithFuel_runMode`,
`OneLevelNestedExecution.resumeWithFuel_run`, `OneLevelNestedExecution.resumeWithFuel_run_add` and
`OneLevelNestedExecution.resumeWithFuel_run_zero` say resuming is one run with the summed budget.
-/

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsNestedWordCall
/-! Exact invocation and response derivation for one internal Word call. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace CheckedCoreWordOutcome

/-- Preserve the exact terminal branch and Word when resuming the caller. -/
def toContractCallResult :
    CheckedCoreWordOutcome → Core.ContractCallWordResult
  | .returned data => .returned data
  | .reverted data => .reverted data
  | .trapped reason => .trapped reason

end CheckedCoreWordOutcome

namespace TopLevelInvocation

/-- Derive the fixed depth-one child-call profile from its parent inputs. -/
def childWord
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address)
    (input : Core.Word) : TopLevelInvocation := {
  target := target
  caller := parentInputs.currentAddress
  callValue := Core.Word.zero
  inputData := HostStorageDriver.InputData.ofWord input
}

/-- Derive a value-bearing child invocation in target/value/input order. -/
def childWordWithValue
    (parentInputs : HostStorageDriver.ExecutionInputs)
    (target : Address)
    (value input : Core.Word) : TopLevelInvocation := {
  target := target
  caller := parentInputs.currentAddress
  callValue := value
  inputData := HostStorageDriver.InputData.ofWord input
}

end TopLevelInvocation

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsOneLevelNestedTransitionSystem
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
cross-account rebasing proof-total when the child later completes. A word call
carries exactly one Word of child return data, so the child's convention
returns one Word.
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
  childContract_returnsOneWord : childContract.entryProfile.returnsOneWord = true
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
  initializer_returnsOneWord :
    prepared.template.initializer.entryProfile.returnsOneWord = true
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
    (initializerReturnsOneWord :
      prepared.template.initializer.entryProfile.returnsOneWord = true)
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
    initializer_returnsOneWord := initializerReturnsOneWord
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
            apply CoreContractEntryProfile.decodeWordOutcome?_ne_none_of_hasType _
              frame.initializer_returnsOneWord
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
    (childReturnsOneWord : childContract.entryProfile.returnsOneWord = true)
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
    childContract_returnsOneWord := childReturnsOneWord
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
              -- A word call admits only a child whose convention returns one Word.
              exact if oneWord : resolved.1.entryProfile.returnsOneWord = true then
                .child (suspended.startChild address addressEq resolved.1 oneWord resolved.2
                  suspended.parentContext.context.values.working.1 resolved.2
                  suspended.parentContext.selectedPresence)
              else
                .root
                  (suspended.resumeWith suspended.parentContext
                    ContractCallFailure.unavailable.result)
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
              -- The one-Word admission precedes the value transfer.
              if oneWord : resolved.1.entryProfile.returnsOneWord = true then
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
                    exact .child (suspended.startChild address addressEq resolved.1 oneWord
                      resolved.2 childWorld installed parentPresence)
              else
                exact .root
                  (suspended.resumeWith suspended.parentContext
                    ContractCallFailure.unavailable.result)
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
          -- Creation admits only an initializer whose convention returns one Word.
          exact if oneWord :
              creation.template.initializer.entryProfile.returnsOneWord = true then
            .initializer
              (suspended.startInitializer environment creation oneWord creatorAddress_eq)
          else
            .root
              (suspended.resumeWith suspended.parentContext
                CheckedCreationPreflightFailure.unavailable.toContractCallResult)
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
            apply CoreContractEntryProfile.decodeWordOutcome?_ne_none_of_hasType _
              frame.childContract_returnsOneWord
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
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsOneLevelNestedExecution
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
        · split
          · exact ⟨anchored.storageAddress_eq,
              anchored.checkpointState_eq, anchored.checkpointJournal_eq,
              rfl, rfl, rfl, by assumption⟩
          · exact ⟨anchored.storageAddress_eq, anchored.checkpointState_eq,
              anchored.checkpointJournal_eq⟩
  | callContractWordWithValue target value input =>
      simp only [RootFrame.afterSuspensionWithEnvironment]
      split
      · exact ⟨anchored.storageAddress_eq, anchored.checkpointState_eq,
          anchored.checkpointJournal_eq⟩
      · split
        · exact ⟨anchored.storageAddress_eq, anchored.checkpointState_eq,
            anchored.checkpointJournal_eq⟩
        · split
          · split
            · exact ⟨anchored.storageAddress_eq, anchored.checkpointState_eq,
                anchored.checkpointJournal_eq⟩
            · exact ⟨anchored.storageAddress_eq,
                anchored.checkpointState_eq, anchored.checkpointJournal_eq,
                rfl, rfl, rfl, by assumption⟩
          · exact ⟨anchored.storageAddress_eq, anchored.checkpointState_eq,
              anchored.checkpointJournal_eq⟩
  | createContractWord templateId value input =>
      simp only [RootFrame.afterSuspensionWithEnvironment]
      split
      · exact ⟨anchored.storageAddress_eq, anchored.checkpointState_eq,
          anchored.checkpointJournal_eq⟩
      · split
        · exact ⟨rfl, anchored.storageAddress_eq,
            anchored.checkpointState_eq, anchored.checkpointJournal_eq,
            (PreparedInitializerFrame.postNonce_storageAddress_eq _).trans
              anchored.storageAddress_eq,
            (congrArg FrameCheckpointSnapshot.state
              (PreparedInitializerFrame.postNonce_checkpoint_eq _)).trans
              anchored.checkpointState_eq,
            PreparedInitializerFrame.initializer_storageAddress_eq _,
            PreparedInitializerFrame.initializer_checkpointState_eq _, rfl⟩
        · exact ⟨anchored.storageAddress_eq, anchored.checkpointState_eq,
            anchored.checkpointJournal_eq⟩
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
end
