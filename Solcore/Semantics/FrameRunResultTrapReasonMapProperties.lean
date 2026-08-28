import Solcore.Semantics.FrameOutcomeTrapReasonMapProperties
import Solcore.Semantics.FrameRunResultTrapReasonMap

/-! Construction, projection, and composition laws for frame-result mapping. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameRunResult

universe u v w

@[simp] theorem mapTrapReason_mk
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (working : WorldState) (outcome : FrameOutcome TrapReason) :
    mapTrapReason mapReason ⟨working, outcome⟩ =
      (⟨working, outcome.mapTrapReason mapReason⟩ :
        FrameRunResult MappedTrapReason) := by
  rfl

@[simp] theorem working_mapTrapReason
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (result : FrameRunResult TrapReason) :
    (mapTrapReason mapReason result).working = result.working := by
  rfl

@[simp] theorem outcome_mapTrapReason
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (result : FrameRunResult TrapReason) :
    (mapTrapReason mapReason result).outcome =
      result.outcome.mapTrapReason mapReason := by
  rfl

@[simp] theorem mapTrapReason_id
    {TrapReason : Type u} (result : FrameRunResult TrapReason) :
    mapTrapReason (fun reason => reason) result = result := by
  cases result with
  | mk working outcome =>
      rw [mapTrapReason_mk, FrameOutcome.mapTrapReason_id]

@[simp] theorem mapTrapReason_comp
    {TrapReason : Type u}
    {IntermediateTrapReason : Type v}
    {MappedTrapReason : Type w}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (result : FrameRunResult TrapReason) :
    mapTrapReason second (mapTrapReason first result) =
      mapTrapReason (fun reason => second (first reason)) result := by
  cases result with
  | mk working outcome =>
      rw [mapTrapReason_mk, mapTrapReason_mk, mapTrapReason_mk,
        FrameOutcome.mapTrapReason_comp]

end Solcore.Semantics.FrameRunResult
