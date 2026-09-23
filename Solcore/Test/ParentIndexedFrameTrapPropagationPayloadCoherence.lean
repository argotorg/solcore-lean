import Solcore.ContractRuntime.ParentIndexedFrameTrapPropagationPayloadCoherenceProperties
import Solcore.ContractRuntime.ParentIndexedFrameContinuationConstruction

/-! Compile regressions for parent-indexed trap payload coherence. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive TrapPayloadCoherenceEvent where
  | parent
  | nested

private inductive TrapPayloadCoherenceReason where
  | marker
  | other

private def address : Address := ⟨0, by decide⟩
private def slot : Core.Word := ⟨0x11, by decide⟩
private def parentValue : Core.Word := ⟨0xaa, by decide⟩
private def nestedValue : Core.Word := ⟨0xbb, by decide⟩

private def stateWith (value : Core.Word) : WorldState :=
  WorldState.empty.putAccount address (Account.empty.storageWrite slot value)

private def parentTrace : FrameTrace TrapPayloadCoherenceEvent :=
  FrameTrace.record FrameTrace.empty .parent

private def parentWorking :
    WorldState ×
      FrameEffectJournal Nat (FrameTrace TrapPayloadCoherenceEvent) :=
  (stateWith parentValue, ⟨10, parentTrace⟩)

private def extension :
    FrameTrace.ExtensionFrom parentWorking.2.trace :=
  (FrameTrace.ExtensionFrom.start parentWorking.2.trace).record .nested

private def context :
    ParentIndexedFrameContinuationContext Nat TrapPayloadCoherenceEvent
      TrapPayloadCoherenceReason parentWorking :=
  ParentIndexedFrameContinuationContext.fromTraceExtension
    parentWorking 20 extension
      ⟨stateWith nestedValue, FrameOutcome.trapped .marker⟩

private def expectedPayload :
    FrameRunResult TrapPayloadCoherenceReason ×
      FrameEffectJournal Nat (FrameTrace TrapPayloadCoherenceEvent) :=
  (⟨parentWorking.1, FrameOutcome.trapped .marker⟩,
    ⟨parentWorking.2.rollback, extension.toTrace⟩)

private example :
    context.trapPropagationPayload? = some expectedPayload ∧
      ∃ reason,
        context.result.outcome = FrameOutcome.trapped reason ∧
        expectedPayload =
          (⟨parentWorking.1, FrameOutcome.trapped reason⟩,
            ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) := by
  have payloadEq : context.trapPropagationPayload? = some expectedPayload := by
    rfl
  have characterization :=
    (context.trapPropagationPayload?_eq_some_iff expectedPayload).mp payloadEq
  have reconstructed :=
    (context.trapPropagationPayload?_eq_some_iff expectedPayload).mpr
      characterization
  exact ⟨reconstructed, characterization⟩

private example :
    FrameTrace.IsPrefixOf
        parentWorking.2.trace expectedPayload.2.trace ∧
      expectedPayload.2.trace.toList = [.parent, .nested] := by
  constructor
  · exact context.trapPropagationPayload?_some_tracePrefix expectedPayload rfl
  · rfl

end Tests
