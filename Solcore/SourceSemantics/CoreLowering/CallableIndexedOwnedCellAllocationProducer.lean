import Solcore.SourceSemantics.CoreLowering.ProtectedStateCellAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationProducer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCellAllocation

/-! A live authority row supplies the actual marked allocation even when its
independent source cell keeps a type erased by the compiler's marker binder.
The selected row registers the same captured snapshot before the payload. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCellAllocationProducer
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAllocationProducer (Ready)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

def producer {catalog : SourceCoreDataCatalog.Catalog}
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program))
    (model : GenericHeap.CellModel compiled.indexed.layouts.definitions) :
    ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) (protocol headers keys)
      compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model where
  Ready := Ready
  complete := by
    intro owner active request globals allocate allocation annotation same _definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native sourceCell payload sourceLocation
      environments agrees heaps reference _read payloadAt cell allocated initial ready
    obtain ⟨selected, metadata, physicalOwner, current, history⟩ := ready
    subst contextLocation
    subst native
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, _boundEnvironment,
      frame, final, related, _selectedRecords, _otherRecords⟩ :=
      CallableIndexedOwnedCellAllocation.completed_bind allocation annotation same registered initial selected
        history environments agrees heaps reference payloadAt cell allocated
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, final, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCellAllocationProducer
