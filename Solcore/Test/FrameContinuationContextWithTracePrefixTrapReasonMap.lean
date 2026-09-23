import Solcore.ContractRuntime.FrameContinuationContextWithTracePrefixTrapReasonMap

/-! Definition-only compile regressions for trace-prefixed reason mapping. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

universe u v w x

private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContext RollbackState (FrameTrace Event) TrapReason)
    (tracePrefix :
      FrameTrace.IsPrefixOf
        context.effectCheckpoint.trace context.effectWorking.trace) :
    FrameContinuationContextWithTracePrefix.mapTrapReason mapReason
        (⟨context, tracePrefix⟩ :
          FrameContinuationContextWithTracePrefix
            RollbackState Event TrapReason) =
      (⟨context.mapTrapReason mapReason, tracePrefix⟩ :
        FrameContinuationContextWithTracePrefix
          RollbackState Event MappedTrapReason) := by
  rfl

private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContextWithTracePrefix
        RollbackState Event TrapReason) :
    FrameTrace.IsPrefixOf
      context.effectCheckpoint.trace context.effectWorking.trace :=
  (context.mapTrapReason mapReason).tracePrefix

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
  | checkpoint
  | working

private def checkpointTrace : FrameTrace Event :=
  FrameTrace.record FrameTrace.empty .checkpoint

private def suffix : FrameTrace Event :=
  FrameTrace.record FrameTrace.empty .working

private def workingTrace : FrameTrace Event :=
  FrameTrace.append checkpointTrace suffix

private def address : Address := ⟨0, by decide⟩
private def slot : Core.Word := ⟨0x11, by decide⟩
private def checkpointValue : Core.Word := ⟨0xaa, by decide⟩
private def workingValue : Core.Word := ⟨0xbb, by decide⟩

private def stateWith (value : Core.Word) : WorldState :=
  WorldState.empty.putAccount address (Account.empty.storageWrite slot value)

private def checkpointJournal : FrameEffectJournal Nat (FrameTrace Event) :=
  ⟨10, checkpointTrace⟩

private def workingJournal : FrameEffectJournal Nat (FrameTrace Event) :=
  ⟨20, workingTrace⟩

private def concreteContext :
    FrameContinuationContextWithTracePrefix Nat Event SourceReason :=
  ⟨⟨stateWith checkpointValue, checkpointJournal, workingJournal,
      ⟨stateWith workingValue, .trapped .marker⟩⟩,
    ⟨suffix, rfl⟩⟩

private example :
    (concreteContext.mapTrapReason mapReason).toFrameContinuationContext =
      (⟨stateWith checkpointValue, checkpointJournal, workingJournal,
        ⟨stateWith workingValue, FrameOutcome.trapped .mapped⟩⟩ :
        FrameContinuationContext Nat (FrameTrace Event) TargetReason) := by
  rfl

end Tests
