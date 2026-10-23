import Solcore.SourceSemantics.CoreLowering.CellAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.ProtectedStateMarkedAllocation

/-! The ordinary instance of the cell allocator uses the same actual marked
allocation and its original readiness condition. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion
universe u v

def MarkedAllocation.Producer.toCells {Records : Type v}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {protocol : Protocol.{u, v} Records}
    {layouts : SourceCoreAllocationLayouts.Prepared} {layout : SourceCoreCallableIndexedFrames.Layout}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (producer : MarkedAllocation.Producer protocol layouts layout model) :
    CellAllocation.Producer (catalog := catalog) protocol layouts layout (.ordinary model) where
  Ready := producer.Ready
  complete := by
    intro owner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native
      sourceCell payload sourceLocation environments agrees heaps reference read payloadAt cell allocated initial ready
    cases allocated with
    | ordinary allocated =>
      obtain ⟨captured, captures, typed, evaluated, finalHeaps, finalReference, preservation, transition⟩ :=
        producer.complete allocation annotation same definitions registered environments agrees
          (GenericHeap.ordinaryHeap_iff.mp heaps) reference read payloadAt cell allocated initial ready
      exact ⟨captured, captures, typed, evaluated, GenericHeap.ordinaryHeap_iff.mpr finalHeaps,
        finalReference, preservation, transition⟩
    | generalized allocated => cases cell

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
