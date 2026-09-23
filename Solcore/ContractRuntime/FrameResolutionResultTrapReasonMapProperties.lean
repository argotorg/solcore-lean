import Solcore.ContractRuntime.FrameResolutionResultTrapReasonMap

/-! Constructor and composition laws for total-resolution reason mapping. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameResolutionResult

universe u v w x y

@[simp] theorem mapTrapReason_returned
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (state : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    mapTrapReason mapReason
        (FrameResolutionResult.returned
          (TrapReason := TrapReason) state effects data) =
      FrameResolutionResult.returned
        (TrapReason := MappedTrapReason) state effects data := by
  rfl

@[simp] theorem mapTrapReason_reverted
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (state : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    mapTrapReason mapReason
        (FrameResolutionResult.reverted
          (TrapReason := TrapReason) state effects data) =
      FrameResolutionResult.reverted
        (TrapReason := MappedTrapReason) state effects data := by
  rfl

@[simp] theorem mapTrapReason_trapped
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (reason : TrapReason) :
    mapTrapReason mapReason
        (FrameResolutionResult.trapped
          (RollbackState := RollbackState) (TraceState := TraceState) reason) =
      FrameResolutionResult.trapped (mapReason reason) := by
  rfl

@[simp] theorem mapTrapReason_id
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (result : FrameResolutionResult RollbackState TraceState TrapReason) :
    mapTrapReason (fun reason => reason) result = result := by
  cases result <;> rfl

@[simp] theorem mapTrapReason_comp
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {IntermediateTrapReason : Type x}
    {MappedTrapReason : Type y}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (result : FrameResolutionResult RollbackState TraceState TrapReason) :
    mapTrapReason second (mapTrapReason first result) =
      mapTrapReason (fun reason => second (first reason)) result := by
  cases result <;> rfl

end Solcore.ContractRuntime.FrameResolutionResult
