import Solcore.SourceSemantics.CoreLowering.ProtectedStateOrdinaryAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryAllocation

/-! The generic lexical allocation interface is implemented by the actual
owned-pool producer. A readiness receipt identifies its exact ordered row,
physical frame and authenticated stable history. No capture is substituted. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationProducer
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

def Ready {index : ProtectedStateTransition.Index} (initial : State headers keys index)
    (location : Location) (native : NativeFrame) : Prop :=
  ∃ selected : Fin keys.length, ∃ metadata,
    keys[selected.val].frameLocation = location ∧
    (initial.rows selected).authority.current = native ∧
    Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows selected).authority.current (initial.rows selected).authority.ghost metadata

theorem ready_selected {index : ProtectedStateTransition.Index} (initial : State headers keys index)
    (selected : Fin keys.length) {metadata : Option MetadataState}
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows selected).authority.current (initial.rows selected).authority.ghost metadata) :
    Ready initial keys[selected.val].frameLocation (initial.rows selected).authority.current :=
  ⟨selected, metadata, rfl, rfl, history⟩

private theorem current_history_of_stable {native : NativeFrame} {savedGhost reachedGhost : GhostFrame}
    {metadata : Option MetadataState}
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native savedGhost metadata)
    (current : Current compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native reachedGhost) :
    ∃ reachedMetadata, Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native reachedGhost reachedMetadata := by
  cases stable with
  | empty => cases current with | stable carried => exact ⟨_, carried⟩
  | state stored history => cases current with | stable carried => exact ⟨_, carried⟩

/-- A retained stable frame read rules out a transient read-view history in
the reached selected row. Authentication comes from that actual row's Current
receipt, preserving its own ghost witness. -/
theorem ready_of_stable_read {index : ProtectedStateTransition.Index} (initial : State headers keys index)
    (selected : Fin keys.length) {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (read : index.store.read? keys[selected.val].frameLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata) :
    Ready initial keys[selected.val].frameLocation native := by
  have encoded := Option.some.inj ((CallableIndexedOwnedFunctionEntries.reached_frame_read initial selected).symm.trans read)
  have current : (initial.rows selected).authority.current = native := by
    have decoded := congrArg (SourceCoreCallableIndexedFrames.decode compiled.indexed.ancestry.layout.frame) encoded
    simpa only [SourceCoreCallableIndexedFrames.decode_encode, Option.some.injEq] using decoded
  have actualHistory := (initial.rows selected).authority.frame.history
  rw [current] at actualHistory
  obtain ⟨reachedMetadata, carried⟩ := current_history_of_stable stable actualHistory
  refine ⟨selected, reachedMetadata, rfl, current, ?_⟩
  simpa only [current] using carried

def producer {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program))
    (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions) :
    ProtectedStateTransition.OrdinaryAllocation.Producer (protocol headers keys)
      compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model where
  Ready := Ready
  complete := by
    intro owner active request globals allocate allocation annotation same _definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native payload sourceValue sourceLocation
      environments agrees heaps reference _read payloadAt cell allocated initial ready
    obtain ⟨selected, metadata, physicalOwner, current, history⟩ := ready
    subst contextLocation
    subst native
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, _boundEnvironment,
      frame, final, related, _selectedRecords, _otherRecords⟩ :=
      CallableIndexedOwnedOrdinaryAllocation.completed_bind allocation annotation same registered initial selected
        history environments agrees heaps reference payloadAt cell allocated
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, final, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationProducer
