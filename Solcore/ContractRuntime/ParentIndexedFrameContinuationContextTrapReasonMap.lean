import Solcore.ContractRuntime.ParentIndexedFrameContinuationContext
import Solcore.ContractRuntime.FrameContinuationContextWithTracePrefixTrapReasonMap

/-! Trap-reason mapping for parent-indexed continuation contexts. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w x

/-- Map only the refined context's trap reason, retaining the parent index. -/
def mapTrapReason
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    ParentIndexedFrameContinuationContext
      RollbackState Event MappedTrapReason parentWorking :=
  {
    toFrameContinuationContextWithTracePrefix :=
      context.toFrameContinuationContextWithTracePrefix.mapTrapReason mapReason
    checkpoint_eq_parentWorking := context.checkpoint_eq_parentWorking
  }

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext
