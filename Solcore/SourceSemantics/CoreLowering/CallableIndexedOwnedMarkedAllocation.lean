import Solcore.SourceSemantics.CoreLowering.ProtectedStateMarkedAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationProducer

/-! A live authority row supplies the actual marked allocation even when its
independent source cell keeps a type erased by the compiler's marker binder.
The selected row registers the same captured snapshot before the payload. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMarkedAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAllocationProducer (Ready)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

def producer {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program))
    (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions) :
    ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
      compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model where
  Ready := Ready
  complete := by
    intro owner active request globals allocate allocation annotation same _definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native sourceType payload sourceValue sourceLocation
      environments agrees heaps reference _read payloadAt cell allocated initial ready
    obtain ⟨selected, metadata, physicalOwner, current, history⟩ := ready
    subst contextLocation
    subst native
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, _boundEnvironment,
      frame, final, related, _selectedRecords, _otherRecords⟩ :=
      CallableIndexedOwnedOrdinaryAllocation.completed_bind_for_type allocation annotation same registered initial selected
        history environments agrees heaps reference payloadAt cell allocated
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, final, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMarkedAllocation
