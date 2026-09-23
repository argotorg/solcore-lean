import Solcore.ContractRuntime.FrameContinuationContext
import Solcore.ContractRuntime.FrameRunResultTrapReasonMap

/-! Checkpoint-preserving mapping of continuation-context trap reasons. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameContinuationContext

universe u v w x

/-- Preserve caller-owned inputs while mapping only the completed result. -/
def mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContext RollbackState TraceState TrapReason) :
    FrameContinuationContext RollbackState TraceState MappedTrapReason :=
  {
    stateCheckpoint := context.stateCheckpoint
    effectCheckpoint := context.effectCheckpoint
    effectWorking := context.effectWorking
    result := context.result.mapTrapReason mapReason
  }

end Solcore.ContractRuntime.FrameContinuationContext
