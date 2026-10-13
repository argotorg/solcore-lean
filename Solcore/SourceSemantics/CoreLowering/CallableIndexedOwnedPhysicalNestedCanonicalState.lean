import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCanonicalState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCanonicalState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCallerSlotForgetting

/-! The same actual caller carries its named Source seed, full physical slot
layout and installed cache through lexical scopes and real heap effects. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalNestedCanonicalState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedHistory CallableIndexedOwnedPhysicalGlobals
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : CallableIndexedOwnedFunctionValues.Header compiled program)

abbrev Packet := CallableIndexedOwnedNestedCanonicalState.Packet (headers := headers) owner caller

def slotsProtocol : ProtectedStateTransition.Protocol (Records keys) where
  State := fun index => { _initial : (CallableIndexedOwnedNestedCanonicalState.protocol
    (headers := headers) owner caller).State index // Slots compiled 1 index.scope index.canonical }
  records := fun state => records state.val.val
  Relates := fun first last => Relates first.val.val last.val.val
  refl := fun state => Relates.refl state.val.val
  trans := fun first last => first.trans last

def protocol := CallableIndexedOwnedPhysicalState.protocol (slotsProtocol (headers := headers) owner caller)

def canonical {index : ProtectedStateTransition.Index}
    (state : (protocol (headers := headers) owner caller).State index) :
    (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State index :=
  ⟨⟨state.base.val.val, state.base.property⟩, state.physical⟩

def of_canonical {index : ProtectedStateTransition.Index}
    (state : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State index)
    (packet : Packet owner caller index state.base.val) :
    (protocol (headers := headers) owner caller).State index := ⟨⟨⟨state.base.val, packet⟩, state.base.property⟩, state.physical⟩

/-- Restoring the named packet uses the actual reached pool and preserved frame. -/
def after {index : ProtectedStateTransition.Index}
    (initial : (protocol (headers := headers) owner caller).State index)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (reached : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      (index.extend mapping world heap store))
    (frame : AdministrativePreserved index.mapping index.store mapping store) :
    (protocol (headers := headers) owner caller).State (index.extend mapping world heap store) :=
  of_canonical owner caller reached (initial.base.val.property.after owner caller reached.base.val frame)

private def slotsCaller : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => Slots compiled 1 index.scope index.canonical) (slotsProtocol (headers := headers) owner caller) where
  pool := fun state => state.val.val
  records_eq := fun _ => rfl
  related := fun related => related
  slots := fun state => state.property
  restore := fun {_index} initial {_mapping _world _heap _store} reached _maps _worlds frame _metadata related =>
    ⟨⟨⟨reached, initial.val.property.after owner caller reached frame⟩, initial.property⟩, rfl, related⟩

def carrier : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => Slots compiled 1 index.scope index.canonical ∧ Authority compiled index.mapping index.store)
    (protocol (headers := headers) owner caller) := CallableIndexedOwnedPhysicalState.carrier (slotsCaller owner caller)

def bridge := (carrier (headers := headers) owner caller).forgetSlots

private def slotsAdministrative : ProtectedStateTransition.AdministrativeTransport
    (slotsProtocol (headers := headers) owner caller) where
  extend := fun {_index} state {_mapping _world _heap _store} maps worlds frame metadata =>
    ⟨(CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner caller).extend state.val maps worlds frame metadata,
      state.property⟩
  related := fun {_index} state {_mapping _world _heap _store} maps worlds frame metadata =>
    (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner caller).related state.val maps worlds frame metadata
  records_eq := fun {_index} state {_mapping _world _heap _store} maps worlds frame metadata =>
    (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner caller).records_eq state.val maps worlds frame metadata

def administrativeTransport : ProtectedStateTransition.AdministrativeTransport
    (protocol (headers := headers) owner caller) :=
  CallableIndexedOwnedPhysicalState.administrativeTransport (slotsAdministrative owner caller)

private def slotsBindings : ProtectedStateTransition.Bindings (slotsProtocol (headers := headers) owner caller) where
  prepend := fun state id type value =>
    ⟨(CallableIndexedOwnedNestedCanonicalState.bindings owner caller).prepend state.val id type value,
      state.property.prepend id type value⟩
  prepend_related := fun state id type value =>
    (CallableIndexedOwnedNestedCanonicalState.bindings owner caller).prepend_related state.val id type value
  prepend_records := fun state id type value =>
    (CallableIndexedOwnedNestedCanonicalState.bindings owner caller).prepend_records state.val id type value
  restore := fun state =>
    ⟨(CallableIndexedOwnedNestedCanonicalState.bindings owner caller).restore state.val, state.property.restore⟩
  restore_related := fun state => (CallableIndexedOwnedNestedCanonicalState.bindings owner caller).restore_related state.val
  restore_records := fun state => (CallableIndexedOwnedNestedCanonicalState.bindings owner caller).restore_records state.val

def bindings : ProtectedStateTransition.Bindings (protocol (headers := headers) owner caller) :=
  CallableIndexedOwnedPhysicalState.bindings (slotsBindings owner caller)

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)

private def slotsMarked : ProtectedStateTransition.MarkedAllocation.Producer
    (slotsProtocol (headers := headers) owner caller) compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model where
  Ready := fun state location native =>
    (CallableIndexedOwnedNestedCanonicalState.markedProducer owner caller model).Ready state.val location native
  complete := by
    intro allocationOwner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native sourceType payload sourceValue sourceLocation
      environments agrees heaps reference read payloadAt cell allocated initial ready
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, final, related⟩ :=
      (CallableIndexedOwnedNestedCanonicalState.markedProducer owner caller model).complete
        allocation annotation same definitions registered environments agrees heaps reference read payloadAt cell allocated initial.val ready
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame,
      ⟨final, initial.property.prepend request.binder.id request.payloadType
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))⟩, related⟩

def markedProducer : ProtectedStateTransition.MarkedAllocation.Producer
    (protocol (headers := headers) owner caller) compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model :=
  CallableIndexedOwnedPhysicalState.markedProducer (slotsMarked owner caller model)

theorem readyAt_of_stableOwner {location : Location} {native : NativeFrame}
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      (markedProducer (headers := headers) owner caller model).toOrdinary location native := by
  intro index state read
  exact CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner (headers := headers) model stable state.base.val.val read

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalNestedCanonicalState
