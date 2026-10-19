import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows

/-! A genuine Source descriptor read recovers the actual allocation row from
the mixed heap relation. The binding and lexical context remain existential
until authentic allocation or capture provenance identifies the read caller. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows
open Core Frontend SourceInference GeneralHeap GenericHeap
open GeneralizedLocalDescriptorHeap

variable {definitions : DataEnvironment} {catalog : SourceCoreDataCatalog.Catalog}
  {projects : GenericHeap.Projection} {ordinary : PayloadModel catalog projects definitions}
  {instances : InstanceModel definitions}

theorem of_heap_read {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {location : Dynamic.Location} {cell : Dynamic.Cell} {function : Dynamic.GeneralizedClosure}
    (heaps : CellHeapRepresents (cellModel ordinary instances) mapping world heap store)
    (sourceRead : Dynamic.Heap.Reads heap location cell)
    (descriptor : cell.generalized = some function) :
    ∃ binding lexical, Nonempty (Located instances function binding lexical location mapping world heap store) := by
  obtain ⟨target, bundle, payload, reference, nativeRead, stored⟩ :=
    GeneralizedLocalDescriptorHeap.read heaps sourceRead descriptor
  cases stored with
  | bundle binding lexical registered captures origin binder initializer rows =>
    exact ⟨binding, lexical, ⟨⟨⟨registered, captures, origin, binder, initializer⟩,
      cell, sourceRead, descriptor, target, reference, _, rows, nativeRead⟩⟩⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows
