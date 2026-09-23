import Solcore.ContractRuntime.CheckedContractRegistryProperties
import Solcore.ContractRuntime.OneLevelNestedExecution
import Solcore.ContractRuntime.WorldStateDeltaProperties

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
