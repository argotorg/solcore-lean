import Solcore.Semantics.CheckedHostCoreProgramProperties
import Solcore.Semantics.NestedWordCall

/-! Typed root and child states for one-level nested checked-Core execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.OneLevelNestedExecution

/-- A running root machine paired with its current storage-backed context. -/
structure RootFrame
    (initialWorld : WorldState)
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation) where
  context : HostStorageDriver.Context Unit Unit
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
  context := TopLevelExecution.initialContext installed
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
    TopLevelExecution.preparedContext
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
  parentContext : HostStorageDriver.Context Unit Unit
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
  childContext : HostStorageDriver.Context Unit Unit
  childState : Core.State
  childStateTyping :
    Core.HostStateHasType childState childContract.code.program.resultType
      childContract.code.program.dataDefinitions
  parentStorageAccount : Account
  parentStorageAccount_present :
    childContext.context.values.working.1.account?
        suspendedRoot.parentContext.context.storageAddress =
      some parentStorageAccount

/-- The currently active machine in the one-level scheduler. -/
inductive Mode
    (initialWorld : WorldState)
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation) where
  | root (frame : RootFrame initialWorld rootContract rootInvocation)
  | child (frame : ChildFrame initialWorld rootContract rootInvocation)

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

end Mode

end Solcore.Semantics.OneLevelNestedExecution
