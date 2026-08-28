import Solcore.Semantics.FrameResolutionResultTrapReasonMapProperties
import Solcore.Semantics.FrameResolutionResultContinuationProperties

/-! Invariance of bytes-aware continuation under result reason mapping. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameResolutionResult

universe u v w x y

/-- Mapping a trapped reason leaves bytes-aware continuation results unchanged. -/
@[simp] theorem continue?_mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {Next : Type y}
    (mapReason : TrapReason → MappedTrapReason)
    (result : FrameResolutionResult RollbackState TraceState TrapReason)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next) :
    (mapTrapReason mapReason result).continue?
        onReturned onReverted =
      result.continue? onReturned onReverted := by
  cases result <;> simp

end Solcore.Semantics.FrameResolutionResult
