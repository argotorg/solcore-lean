import Solcore.Semantics.ParentIndexedFrameContinuationConstruction
import Solcore.Semantics.ParentIndexedSelectedCheckedWordExecution

/-! Canonical returned-parent projection for selected checked Word execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedSelectedCheckedWordExecution

universe u v w

/--
Build the returned parent continuation only from the exact completion projected
by this execution. The equality prevents unrelated completion data from being
assigned this carrier's provenance.
-/
def toReturnedContinuation
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (_completed : entry.execution.completion? = some completion) :
    ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking :=
  ParentIndexedFrameContinuationContext.fromTraceExtension
    parentWorking initialization.workingRollback
    initialization.initialTraceExtension
    completion.toFrameContinuationContext.result

/--
Retain the exact canonical Word completion together with its proof-linked
returned parent continuation.
-/
def returnedCompletion?
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    Option
      (WordReturnedFrameCompletion RollbackState (FrameTrace Event) ×
        ParentIndexedFrameContinuationContext
          RollbackState Event TrapReason parentWorking) :=
  match completed : entry.execution.completion? with
  | none => none
  | some completion =>
      some (completion, entry.toReturnedContinuation completion completed)

/-- Forget only the retained completion; this is not a second producer. -/
def returnedContinuation?
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    Option
      (ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking) :=
  (entry.returnedCompletion? (TrapReason := TrapReason)).map Prod.snd

end Solcore.Semantics.ParentIndexedSelectedCheckedWordExecution
