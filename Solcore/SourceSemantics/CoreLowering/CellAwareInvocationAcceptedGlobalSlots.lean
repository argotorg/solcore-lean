import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCanonicalState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCellAllocationProducer

/-! Cell allocation for the canonical caller protocol that retains every
physical global slot and the physical cache. The same genuine cell allocation
of the ordinary pool runs underneath; its new canonical cell shifts the slots
with the scope, and its administrative frame preserves the cache. With the
existing bindings, administrative transport and ordinary caller carrier, this
lets an accepted body keep the `Globals` facts that direct-call sites read. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedGlobalSlots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedHistory
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {catalog : SourceCoreDataCatalog.Catalog}

/-- The ordinary pool's cell allocation with the slot facts carried along. -/
def slotsProducer (callerPrefix : Nat) (model : GenericHeap.CellModel compiled.indexed.layouts.definitions) :
    ProtectedStateTransition.CellAllocation.Producer (catalog := catalog)
      (CallableIndexedOwnedPhysicalCanonicalState.slotsProtocol headers keys callerPrefix)
      compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model where
  Ready := fun state location native =>
    (CallableIndexedOwnedCellAllocationProducer.producer (catalog := catalog) headers keys model).Ready
      state.val location native
  complete := by
    intro owner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native
      sourceCell payload sourceLocation environments agrees heaps reference read payloadAt cell allocated initial ready
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, final, related⟩ :=
      (CallableIndexedOwnedCellAllocationProducer.producer (catalog := catalog) headers keys model).complete
        allocation annotation same definitions registered environments agrees heaps reference read payloadAt cell
        allocated initial.val ready
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame,
      ⟨⟨final, initial.property.prepend request.binder.id request.payloadType
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))⟩, related⟩⟩

/-- The physical layer over `slotsProducer`: the allocation's administrative
frame extends the cache authority of the input state. -/
def producer (callerPrefix : Nat) (model : GenericHeap.CellModel compiled.indexed.layouts.definitions) :
    ProtectedStateTransition.CellAllocation.Producer (catalog := catalog)
      (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys callerPrefix)
      compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model where
  Ready := fun state location native =>
    (slotsProducer (catalog := catalog) (headers := headers) (keys := keys) callerPrefix model).Ready
      state.base location native
  complete := by
    intro owner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native
      sourceCell payload sourceLocation environments agrees heaps reference read payloadAt cell allocated initial ready
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, final, related⟩ :=
      (slotsProducer (catalog := catalog) (headers := headers) (keys := keys) callerPrefix model).complete
        allocation annotation same definitions registered environments agrees heaps reference read payloadAt cell
        allocated initial.base ready
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame,
      ⟨⟨final, initial.physical.extend frame⟩, related⟩⟩

/-- Readiness of the wrapped producer is the ordinary pool's readiness. -/
theorem ready_iff (callerPrefix : Nat) (model : GenericHeap.CellModel compiled.indexed.layouts.definitions)
    {index : ProtectedStateTransition.Index}
    (state : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys callerPrefix).State index)
    (location : Location) (native : NativeFrame) :
    (producer (catalog := catalog) callerPrefix model).Ready state location native ↔
      (CallableIndexedOwnedCellAllocationProducer.producer (catalog := catalog) headers keys model).Ready
        state.base.val location native :=
  Iff.rfl

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedGlobalSlots
