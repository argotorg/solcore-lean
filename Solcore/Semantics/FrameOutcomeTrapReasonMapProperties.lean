import Solcore.Semantics.FrameOutcomeTrapReasonMap

/-! Constructor and composition laws for frame trap-reason mapping. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameOutcome

universe u v w

@[simp] theorem mapTrapReason_returned
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason) (data : Bytes) :
    mapTrapReason mapReason
        (FrameOutcome.returned (TrapReason := TrapReason) data) =
      FrameOutcome.returned (TrapReason := MappedTrapReason) data := by
  rfl

@[simp] theorem mapTrapReason_reverted
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason) (data : Bytes) :
    mapTrapReason mapReason
        (FrameOutcome.reverted (TrapReason := TrapReason) data) =
      FrameOutcome.reverted (TrapReason := MappedTrapReason) data := by
  rfl

@[simp] theorem mapTrapReason_trapped
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (reason : TrapReason) :
    mapTrapReason mapReason (FrameOutcome.trapped reason) =
      FrameOutcome.trapped (mapReason reason) := by
  rfl

@[simp] theorem mapTrapReason_id
    {TrapReason : Type u} (outcome : FrameOutcome TrapReason) :
    mapTrapReason (fun reason => reason) outcome = outcome := by
  cases outcome <;> rfl

@[simp] theorem mapTrapReason_comp
    {TrapReason : Type u}
    {IntermediateTrapReason : Type v}
    {MappedTrapReason : Type w}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (outcome : FrameOutcome TrapReason) :
    mapTrapReason second (mapTrapReason first outcome) =
      mapTrapReason (fun reason => second (first reason)) outcome := by
  cases outcome <;> rfl

end Solcore.Semantics.FrameOutcome
