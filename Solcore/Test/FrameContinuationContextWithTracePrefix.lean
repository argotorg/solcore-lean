import Solcore.Semantics.FrameContinuationContextWithTracePrefix

/-! Definition-only regressions for frame contexts with trace-prefix evidence. -/

set_option autoImplicit false

namespace Tests

open Solcore.Semantics

private inductive ContextTraceEvent where
  | entered
  | completed

private inductive ContextTraceReason where
  | marker

private def checkpointTrace : FrameTrace ContextTraceEvent :=
  FrameTrace.record FrameTrace.empty .entered

private def completionFragment : FrameTrace ContextTraceEvent :=
  FrameTrace.record FrameTrace.empty .completed

private def baseContext :
    FrameContinuationContext Nat (FrameTrace ContextTraceEvent)
      ContextTraceReason :=
  ⟨WorldState.empty, ⟨10, checkpointTrace⟩,
    ⟨20, FrameTrace.append checkpointTrace completionFragment⟩,
    ⟨WorldState.empty, .trapped .marker⟩⟩

private def contextWithTracePrefix :
    FrameContinuationContextWithTracePrefix Nat ContextTraceEvent
      ContextTraceReason :=
  ⟨baseContext, ⟨completionFragment, rfl⟩⟩

private example :
    FrameContinuationContextWithTracePrefix Nat ContextTraceEvent
      ContextTraceReason :=
  ⟨baseContext, ⟨completionFragment, rfl⟩⟩

private example :
    FrameTrace.IsPrefixOf
      contextWithTracePrefix.effectCheckpoint.trace
      contextWithTracePrefix.effectWorking.trace :=
  contextWithTracePrefix.tracePrefix

private example :
    contextWithTracePrefix.resolve =
      contextWithTracePrefix.toFrameContinuationContext.resolve := by
  rfl

end Tests
