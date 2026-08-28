import Solcore.Semantics.ParentIndexedFrameContinuationContextTrapReasonMap

/-! Definition-only compile regressions for parent-indexed reason mapping. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

universe u v w x

private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContextWithTracePrefix RollbackState Event TrapReason)
    (checkpointEq :
      (context.stateCheckpoint, context.effectCheckpoint) = parentWorking) :
    ParentIndexedFrameContinuationContext.mapTrapReason mapReason
        (⟨context, checkpointEq⟩ :
          ParentIndexedFrameContinuationContext
            RollbackState Event TrapReason parentWorking) =
      (⟨context.mapTrapReason mapReason, checkpointEq⟩ :
        ParentIndexedFrameContinuationContext
          RollbackState Event MappedTrapReason parentWorking) := by
  rfl

private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    (context.stateCheckpoint, context.effectCheckpoint) = parentWorking :=
  (context.mapTrapReason mapReason).checkpoint_eq_parentWorking

private inductive SourceReason where
  | marker
  | other

private inductive TargetReason where
  | mapped
  | other

private def mapReason : SourceReason → TargetReason
  | .marker => .mapped
  | .other => .other

private inductive Event where
  | parent
  | nested

private def parentTrace : FrameTrace Event :=
  FrameTrace.record FrameTrace.empty .parent

private def nestedFragment : FrameTrace Event :=
  FrameTrace.record FrameTrace.empty .nested

private def nestedTrace : FrameTrace Event :=
  FrameTrace.append parentTrace nestedFragment

private def address : Address := ⟨0, by decide⟩
private def slot : Core.Word := ⟨0x11, by decide⟩
private def parentValue : Core.Word := ⟨0xaa, by decide⟩
private def nestedValue : Core.Word := ⟨0xbb, by decide⟩

private def stateWith (value : Core.Word) : WorldState :=
  WorldState.empty.putAccount address (Account.empty.storageWrite slot value)

private def parentJournal : FrameEffectJournal Nat (FrameTrace Event) :=
  ⟨10, parentTrace⟩

private def nestedJournal : FrameEffectJournal Nat (FrameTrace Event) :=
  ⟨20, nestedTrace⟩

private def parentWorking :
    WorldState × FrameEffectJournal Nat (FrameTrace Event) :=
  (stateWith parentValue, parentJournal)

private theorem prefixEvidence :
    FrameTrace.IsPrefixOf parentTrace nestedTrace :=
  ⟨nestedFragment, rfl⟩

private def concreteContext :
    ParentIndexedFrameContinuationContext
      Nat Event SourceReason parentWorking :=
  ⟨⟨⟨stateWith parentValue, parentJournal, nestedJournal,
        ⟨stateWith nestedValue, .trapped .marker⟩⟩,
      prefixEvidence⟩,
    rfl⟩

private example :
    concreteContext.mapTrapReason mapReason =
      (⟨⟨⟨stateWith parentValue, parentJournal, nestedJournal,
            ⟨stateWith nestedValue, FrameOutcome.trapped .mapped⟩⟩,
          prefixEvidence⟩,
        rfl⟩ :
        ParentIndexedFrameContinuationContext
          Nat Event TargetReason parentWorking) := by
  rfl

end Tests
