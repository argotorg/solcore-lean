import Solcore.ContractRuntime.FrameContinuationContextTrapReasonMapProperties
import Solcore.ContractRuntime.FrameResolutionResultProperties
import Solcore.ContractRuntime.FrameResolutionResultTrapReasonMapProperties

/-! Naturality of trap-reason mapping under total frame resolution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameContinuationContext

universe u v w x

@[simp] theorem resolve_mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    resolve (mapTrapReason mapReason context) =
      FrameResolutionResult.mapTrapReason mapReason (resolve context) := by
  cases context with
  | mk stateCheckpoint effectCheckpoint effectWorking result =>
      cases result with
      | mk working outcome =>
          cases outcome <;> simp

end Solcore.ContractRuntime.FrameContinuationContext
