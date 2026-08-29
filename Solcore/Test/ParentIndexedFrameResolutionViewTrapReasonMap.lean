import Solcore.Semantics.FrameResolutionResultContinueTrapReasonMapProperties
import Solcore.Semantics.ParentIndexedFrameResolutionViewTrapReasonMapProperties

/-! Compile-only consumers of resolution-view reason-mapping naturality. -/

set_option autoImplicit false

namespace Tests

open Solcore.Semantics

universe u v w x y z

/-- One heterogeneous mapping uses the whole-product public law directly. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    (context.mapTrapReason mapReason).resolveWithTrapRollback =
      (FrameResolutionResult.mapTrapReason mapReason
          (context.resolveWithTrapRollback).1,
        (context.resolveWithTrapRollback).2) := by
  exact
    ParentIndexedFrameContinuationContext.resolveWithTrapRollback_mapTrapReason
      mapReason context

/-- Nested and composed heterogeneous mappings normalize to the same view. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {IntermediateTrapReason : Type x}
    {MappedTrapReason : Type y}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    ((context.mapTrapReason first).mapTrapReason second
        ).resolveWithTrapRollback =
      (FrameResolutionResult.mapTrapReason
          (fun reason => second (first reason))
          (context.resolveWithTrapRollback).1,
        (context.resolveWithTrapRollback).2) := by
  simp

/-- Identity reason mapping normalizes to the original complete view. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    (context.mapTrapReason (fun reason => reason)).resolveWithTrapRollback =
      context.resolveWithTrapRollback := by
  simp

/-- Callback selection and rollback observation are invariant together. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x} {Next : Type z}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          Bytes → Option Next) :
    ((((context.mapTrapReason mapReason).resolveWithTrapRollback).1.continue?
        onReturned onReverted),
      ((context.mapTrapReason mapReason).resolveWithTrapRollback).2) =
    (((context.resolveWithTrapRollback).1.continue?
        onReturned onReverted),
      (context.resolveWithTrapRollback).2) := by
  simp

end Tests
