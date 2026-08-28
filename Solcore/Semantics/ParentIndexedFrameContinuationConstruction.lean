import Solcore.Semantics.FrameTraceExtension
import Solcore.Semantics.ParentIndexedFrameContinuationContext

/-! Restricted construction of a parent-indexed context from a trace extension. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

universe u v w

/-- Build the indexed context while deriving its two relationship proofs. -/
def fromTraceExtension
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event))
    (workingRollback : RollbackState)
    (extension : FrameTrace.ExtensionFrom parentWorking.2.trace)
    (result : FrameRunResult TrapReason) :
    ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking :=
  {
    stateCheckpoint := parentWorking.1
    effectCheckpoint := parentWorking.2
    effectWorking := ⟨workingRollback, extension.toTrace⟩
    result := result
    tracePrefix := extension.earlier_isPrefixOf_toTrace
    checkpoint_eq_parentWorking := rfl
  }

end Solcore.Semantics.ParentIndexedFrameContinuationContext
