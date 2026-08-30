import Solcore.Semantics.OneLevelNestedExecutionProperties
import Solcore.Semantics.OneLevelNestedExecutionReachabilityProperties

/-! External compile consumers for the public ADR-0146 scheduler laws. -/

set_option autoImplicit false

namespace Tests.Adr0146SchedulerExternalProperties

open Solcore.Core
open Solcore.Semantics
open OneLevelNestedExecution

example := @Result.eq_of_view_eq

example
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (mode : Mode initialWorld rootContract rootInvocation) :
    mode.rank ≤ 1 :=
  Mode.rank_le_one mode

section RootFinalization

variable {initialWorld : WorldState}
variable {rootContract : CheckedCoreContract}
variable {rootInvocation : TopLevelInvocation}
variable
  (frame : RootFrame initialWorld rootContract rootInvocation)
variable (value : Value) (store : Store)

example (data : Bytes) :
    (frame.finalize value store (.returned data)).finalWorld =
      frame.context.context.values.working.1 :=
  RootFrame.finalize_returned_finalWorld frame value store data

example (data : Bytes) :
    (frame.finalize value store (.reverted data)).finalWorld =
      initialWorld :=
  RootFrame.finalize_reverted_finalWorld frame value store data

example (reason : Word) :
    (frame.finalize value store (.trapped reason)).finalWorld =
      initialWorld :=
  RootFrame.finalize_trapped_finalWorld frame value store reason

example (outcome : FrameOutcome Word) :
    (frame.finalize value store outcome).outcome = outcome :=
  RootFrame.finalize_outcome frame value store outcome

example (outcome : FrameOutcome Word) :
    (frame.finalize value store outcome).workingDelta = .exact :=
  RootFrame.finalize_workingDelta frame value store outcome

end RootFinalization

section ChildResolution

variable {initialWorld : WorldState}
variable {rootContract : CheckedCoreContract}
variable {rootInvocation : TopLevelInvocation}
variable
  (frame : ChildFrame initialWorld rootContract rootInvocation)

example (data : Word) :
    (frame.selectedParentContext (.returned data)).context.values.working.1 =
      frame.childContext.context.values.working.1 :=
  ChildFrame.selectedParentContext_returned_workingWorld frame data

example (data : Word) :
    frame.selectedParentContext (.reverted data) =
      frame.suspendedRoot.parentContext :=
  ChildFrame.selectedParentContext_reverted frame data

example (reason : Word) :
    frame.selectedParentContext (.trapped reason) =
      frame.suspendedRoot.parentContext :=
  ChildFrame.selectedParentContext_trapped frame reason

example (data : Word) :
    (frame.resumeRoot (.returned data)).context.context.values.working.1 =
      frame.childContext.context.values.working.1 :=
  ChildFrame.resumeRoot_returned_workingWorld frame data

example (data : Word) :
    (frame.resumeRoot (.reverted data)).context =
      frame.suspendedRoot.parentContext :=
  ChildFrame.resumeRoot_reverted_context frame data

example (reason : Word) :
    (frame.resumeRoot (.trapped reason)).context =
      frame.suspendedRoot.parentContext :=
  ChildFrame.resumeRoot_trapped_context frame reason

example (data : Word) :
    (frame.resumeRoot (.returned data)).state =
      frame.suspendedRoot.suspension.resume
        (frame.suspendedRoot.call.response (.returned data)) :=
  ChildFrame.resumeRoot_returned_response frame data

example (data : Word) :
    (frame.resumeRoot (.reverted data)).state =
      frame.suspendedRoot.suspension.resume
        (frame.suspendedRoot.call.response (.reverted data)) :=
  ChildFrame.resumeRoot_reverted_response frame data

example (reason : Word) :
    (frame.resumeRoot (.trapped reason)).state =
      frame.suspendedRoot.suspension.resume
        (frame.suspendedRoot.call.response (.trapped reason)) :=
  ChildFrame.resumeRoot_trapped_response frame reason

end ChildResolution

section ReachabilitySeal

variable {initialWorld : WorldState}
variable {rootContract : CheckedCoreContract}
variable {rootInvocation : TopLevelInvocation}
variable {registry : ExecutionEnvironment}
variable {mode : Mode initialWorld rootContract rootInvocation}

example (reachable : Reachable registry mode) :
    Anchored registry mode :=
  reachable.anchored

end ReachabilitySeal

section ReachableRoot

variable {initialWorld : WorldState}
variable {rootContract : CheckedCoreContract}
variable {rootInvocation : TopLevelInvocation}
variable {registry : ExecutionEnvironment}
variable {frame : RootFrame initialWorld rootContract rootInvocation}
variable (reachable : Reachable registry (.root frame))

example :
    frame.context.context.storageAddress = rootInvocation.target :=
  reachable.root_storageAddress

example :
    frame.context.context.values.checkpoint.state = initialWorld :=
  reachable.root_checkpointState

end ReachableRoot

section ReachableChild

variable {initialWorld : WorldState}
variable {rootContract : CheckedCoreContract}
variable {rootInvocation : TopLevelInvocation}
variable {registry : ExecutionEnvironment}
variable {frame : ChildFrame initialWorld rootContract rootInvocation}
variable (reachable : Reachable registry (.child frame))

example :
    frame.suspendedRoot.parentContext.context.storageAddress =
      rootInvocation.target :=
  reachable.child_parentStorageAddress

example :
    frame.suspendedRoot.parentContext.context.values.checkpoint.state =
      initialWorld :=
  reachable.child_parentCheckpointState

example :
    frame.childContext.context.storageAddress = frame.childTarget :=
  reachable.child_storageAddress

example :
    frame.childContext.context.values.checkpoint.state =
      frame.childInitialWorld :=
  reachable.child_checkpointState

example :
    registry.callRegistry.resolve?
        frame.suspendedRoot.parentContext.context.values.working.1
        frame.childTarget =
      some ⟨frame.childContract, frame.preTransferInstalled⟩ :=
  reachable.child_registryResolution

end ReachableChild

end Tests.Adr0146SchedulerExternalProperties
