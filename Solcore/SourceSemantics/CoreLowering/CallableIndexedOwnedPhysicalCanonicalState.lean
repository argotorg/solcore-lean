import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCanonicalState

/-! Canonical callers retain every physical global reference, including method
slots, together with the complete cache. Ordinary Header slots are a derived
projection using the actual owner's initialized location association. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCanonicalState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedHistory
open CallableIndexedOwnedPhysicalGlobals
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

def slotsProtocol (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)) (callerPrefix : Nat) :
    ProtectedStateTransition.Protocol (Records keys) where
  State := fun index => { _pool : State headers keys index // Slots compiled callerPrefix index.scope index.canonical }
  records := fun state => records state.val
  Relates := fun first last => Relates first.val last.val
  refl := fun state => Relates.refl state.val
  trans := fun first last => first.trans last

def protocol (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)) (callerPrefix : Nat) :=
  CallableIndexedOwnedPhysicalState.protocol (slotsProtocol headers keys callerPrefix)

/-- Lift the actual marked parameter result. The full physical proof comes
from the original cache, the actual frame write and the returned administrative
frame; the canonical slots come from the retained allocation spine. -/
def of_parameter_spine
    {mapping : LocationMap} {store : Store} {frameLocation : Location} {native : NativeFrame}
    (physical : Authority compiled mapping store)
    (frameRead : store.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (next : NativeFrame) {index : ProtectedStateTransition.Index}
    (frame : AdministrativePreserved mapping
      (store.set frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame next)) index.mapping index.store)
    (pool : State headers keys index)
    {canonical added : Environment} (slots : Slots compiled 0 [] canonical) (packed : Value)
    (length : added.length = index.scope.length)
    (spine : index.canonical = added ++ packed :: canonical) :
    (protocol headers keys 1).State index :=
  ⟨⟨pool, spine ▸ slots.parameters packed length⟩, (physical.install frameRead next).extend frame⟩

private def slotsCaller (callerPrefix : Nat) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun index => Slots compiled callerPrefix index.scope index.canonical) (slotsProtocol headers keys callerPrefix) where
  pool := fun state => state.val
  records_eq := fun _ => rfl
  related := fun related => related
  slots := fun state => state.property
  restore := fun {_index} initial {_mapping _world _heap _store} reached _maps _worlds _frame _metadata related =>
    ⟨⟨reached, initial.property⟩, rfl, related⟩

def caller (callerPrefix : Nat) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun index => Slots compiled callerPrefix index.scope index.canonical ∧
        Authority compiled index.mapping index.store) (protocol headers keys callerPrefix) :=
  CallableIndexedOwnedPhysicalState.carrier (slotsCaller callerPrefix)

theorem ordinary_slots (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (locations : ∀ header, header ∈ headers → owner.key.locations header = location compiled header.slot)
    {callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (slots : Slots compiled callerPrefix scope canonical) :
    CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner callerPrefix scope canonical := by
  intro header member
  rw [locations header member]
  exact slots _ _ (CallableIndexedPreparedInventories.cached_global_at compiled header.selected)

/-- Existing ordinary direct calls use the same stronger state and unchanged
pool. This adapter forgets only the extra slot facts at its interface. -/
def ordinaryCaller (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat)
    (locations : ∀ header, header ∈ headers → owner.key.locations header = location compiled header.slot) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner callerPrefix index.scope index.canonical)
      (protocol headers keys callerPrefix) where
  pool := (caller callerPrefix).pool
  records_eq := (caller callerPrefix).records_eq
  related := (caller callerPrefix).related
  slots := fun state => ordinary_slots owner locations ((caller callerPrefix).slots state).1
  restore := (caller callerPrefix).restore

private def slotsAdministrative (callerPrefix : Nat) :
    ProtectedStateTransition.AdministrativeTransport (slotsProtocol headers keys callerPrefix) where
  extend := fun {_index} state {_mapping _world _heap _store} maps worlds frame metadata =>
    ⟨state.val.extend maps worlds frame metadata, state.property⟩
  related := fun {_index} _state {_mapping _world _heap _store} _maps _worlds _frame _metadata =>
    Relates.of_records_eq rfl
  records_eq := fun {_index} _state {_mapping _world _heap _store} _maps _worlds _frame _metadata => rfl

def administrativeTransport (callerPrefix : Nat) :
    ProtectedStateTransition.AdministrativeTransport (protocol headers keys callerPrefix) :=
  CallableIndexedOwnedPhysicalState.administrativeTransport (slotsAdministrative callerPrefix)

private def slotsBindings (callerPrefix : Nat) :
    ProtectedStateTransition.Bindings (slotsProtocol headers keys callerPrefix) where
  prepend := fun state id type value =>
    ⟨(CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).prepend state.val id type value,
      state.property.prepend id type value⟩
  prepend_related := fun state id type value =>
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).prepend_related state.val id type value
  prepend_records := fun state id type value =>
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).prepend_records state.val id type value
  restore := fun state => ⟨(CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore state.val,
    state.property.restore⟩
  restore_related := fun state => (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore_related state.val
  restore_records := fun state => (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore_records state.val

def bindings (callerPrefix : Nat) : ProtectedStateTransition.Bindings (protocol headers keys callerPrefix) :=
  CallableIndexedOwnedPhysicalState.bindings (slotsBindings callerPrefix)

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)

private def slotsMarked (callerPrefix : Nat) :
    ProtectedStateTransition.MarkedAllocation.Producer (slotsProtocol headers keys callerPrefix)
      compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model where
  Ready := fun state location native => (CallableIndexedOwnedMarkedAllocation.producer headers keys model).Ready state.val location native
  complete := by
    intro owner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native sourceType payload sourceValue sourceLocation
      environments agrees heaps reference read payloadAt cell allocated initial ready
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, final, related⟩ :=
      (CallableIndexedOwnedMarkedAllocation.producer headers keys model).complete allocation annotation same definitions registered
        environments agrees heaps reference read payloadAt cell allocated initial.val ready
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame,
      ⟨final, initial.property.prepend request.binder.id request.payloadType
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))⟩, related⟩

def markedProducer (callerPrefix : Nat) :
    ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys callerPrefix)
      compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model :=
  CallableIndexedOwnedPhysicalState.markedProducer (slotsMarked model callerPrefix)

theorem readyAt_of_stableOwner (callerPrefix : Nat) {location : Location} {native : NativeFrame}
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      (markedProducer (headers := headers) (keys := keys) model callerPrefix).toOrdinary location native := by
  intro index state read
  exact CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner (headers := headers) model stable state.base.val read

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCanonicalState
