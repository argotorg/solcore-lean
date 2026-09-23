import Solcore.ContractRuntime.ParentIndexedFrameResolutionFoldProperties
import Solcore.ContractRuntime.ParentIndexedFrameResolutionFoldTrapReasonMapProperties
import Solcore.ContractRuntime.ParentIndexedFrameResolutionViewTrapReasonMapProperties

/-! Compile-only consumers of resolution-fold reason-mapping naturality. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

universe u v w x y z

/-- One heterogeneous mapping uses the fold law directly. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x} {Next : Type y}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        MappedTrapReason → Next) :
    (context.mapTrapReason mapReason).foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      context.foldResolutionWithTrapRollback
        onReturned onReverted
        (fun values reason => onTrapped values (mapReason reason)) := by
  exact context.foldResolutionWithTrapRollback_mapTrapReason
    mapReason onReturned onReverted onTrapped

/-- Identity reason mapping normalizes to the original fold. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {Next : Type y}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        TrapReason → Next) :
    (context.mapTrapReason (fun reason => reason)
        ).foldResolutionWithTrapRollback
          onReturned onReverted onTrapped =
      context.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped := by
  simp

/-- Nested mappings normalize to one composed trap function. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {IntermediateTrapReason : Type x}
    {MappedTrapReason : Type y} {Next : Type z}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        MappedTrapReason → Next) :
    ((context.mapTrapReason first).mapTrapReason second
        ).foldResolutionWithTrapRollback
          onReturned onReverted onTrapped =
      context.foldResolutionWithTrapRollback
        onReturned onReverted
        (fun values reason => onTrapped values (second (first reason))) := by
  simp

/-- Fold reconstruction commutes with resolution-view reason mapping. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    (context.mapTrapReason mapReason).foldResolutionWithTrapRollback
        (fun values data =>
          (FrameResolutionResult.returned values.1 values.2 data, none))
        (fun values data =>
          (FrameResolutionResult.reverted values.1 values.2 data, none))
        (fun values reason =>
          (FrameResolutionResult.trapped reason, some values)) =
      (FrameResolutionResult.mapTrapReason mapReason
          (context.resolveWithTrapRollback).1,
        (context.resolveWithTrapRollback).2) := by
  rw [(context.mapTrapReason mapReason
    ).foldResolutionWithTrapRollback_reconstructs_view]
  exact context.resolveWithTrapRollback_mapTrapReason mapReason

end Tests
