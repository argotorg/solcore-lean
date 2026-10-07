import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMarkedAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryAllocation

/-! Original canonical global slots accompany the actual owned pool through
lexical allocation and scope restoration. The wrapper adds a proof only;
its complete ordered records and actual row transitions remain unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCanonicalState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedExpressionHeads (Globals argumentProtocol)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat)

/-- Prepending a real lexical slot shifts every original global by one. -/
theorem globals_prepend {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (globals : Globals (headers := headers) owner callerPrefix scope canonical)
    (id : Resolved.LocalId) (type : Ty) (value : Value) :
    Globals (headers := headers) owner callerPrefix ((id, type) :: scope) (value :: canonical) := by
  intro header member
  have offset : ((id, type) :: scope).length + callerPrefix + header.slot =
      scope.length + callerPrefix + header.slot + 1 := by simp; omega
  rw [offset]
  exact globals header member

/-- Removing that same lexical slot restores its exact original global index. -/
theorem globals_restore {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {id : Resolved.LocalId} {type : Ty} {value : Value}
    (globals : Globals (headers := headers) owner callerPrefix ((id, type) :: scope) (value :: canonical)) :
    Globals (headers := headers) owner callerPrefix scope canonical := by
  intro header member
  have slot := globals header member
  have offset : ((id, type) :: scope).length + callerPrefix + header.slot =
      scope.length + callerPrefix + header.slot + 1 := by simp; omega
  rw [offset] at slot
  exact slot

def administrativeTransport :
    ProtectedStateTransition.AdministrativeTransport (argumentProtocol (headers := headers) owner callerPrefix) where
  extend := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    ⟨(CallableIndexedOwnedFunctionState.administrativeTransport headers keys).extend state.val maps worlds frame metadata,
      state.property⟩
  related := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys).related state.val maps worlds frame metadata
  records_eq := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys).records_eq state.val maps worlds frame metadata

def bindings : ProtectedStateTransition.Bindings (argumentProtocol (headers := headers) owner callerPrefix) where
  prepend := fun state id type value =>
    ⟨(CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).prepend state.val id type value,
      globals_prepend owner callerPrefix state.property id type value⟩
  prepend_related := fun state id type value =>
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).prepend_related state.val id type value
  prepend_records := fun state id type value =>
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).prepend_records state.val id type value
  restore := fun state =>
    ⟨(CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore state.val,
      globals_restore owner callerPrefix state.property⟩
  restore_related := fun state =>
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore_related state.val
  restore_records := fun state =>
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore_records state.val

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)

/-- The real marked allocator returns its actual reached row pool. The added
slot proof describes the canonical reference prepended by that same receipt. -/
def markedProducer :
    ProtectedStateTransition.MarkedAllocation.Producer (argumentProtocol (headers := headers) owner callerPrefix)
      compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model where
  Ready := fun state location native =>
    (CallableIndexedOwnedMarkedAllocation.producer headers keys model).Ready state.val location native
  complete := by
    intro allocationOwner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native sourceType payload sourceValue sourceLocation
      environments agrees heaps reference read payloadAt cell allocated initial ready
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, transition⟩ :=
      (CallableIndexedOwnedMarkedAllocation.producer headers keys model).complete allocation annotation same definitions registered
        environments agrees heaps reference read payloadAt cell allocated initial.val ready
    obtain ⟨reached, related⟩ := transition
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame,
      ⟨⟨reached, globals_prepend owner callerPrefix initial.property request.binder.id request.payloadType
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))⟩, related⟩⟩

/-- Allocation readiness comes from the physical owner and authentic history;
the canonical-slot proof supplies no capture or snapshot authority. -/
theorem readyAt_of_stableOwner {location : Location} {native : NativeFrame}
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      (markedProducer (headers := headers) owner callerPrefix model).toOrdinary location native := by
  intro index state read
  exact CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner (headers := headers) model stable state.val read

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCanonicalState
