import Solcore.SourceSemantics.CoreLowering.DataPlaceCommitReflection

/-! The final mapped write for the projection-parametric shared heap.
This reuses the source write relation; compatibility changes the payload model,
not the store operation, location map, or administrative frame invariant. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceCommitReflection
open Core Frontend SourceInference GeneralHeap DataEquality

/-- Any completed actual storeCell commits precisely the reconstructed source
root once. The mapped heap and old administrative cells are preserved at the
same world; helper allocations have already been reflected before this step. -/
theorem reflects_storeCell {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {model : GenericHeap.PayloadModel catalog projects}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store finalStore : Store}
    {location : Dynamic.Location} {target : Location} {cell : Dynamic.Cell} {type : Ty}
    {sourceValue : Dynamic.Value} {value result : Value}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (reference : ReferenceRepresents mapping world location target type)
    (read : Dynamic.Heap.Reads heap location cell)
    (represented : model.Represents mapping world cell.type sourceValue value type)
    {environment : Environment} {referenceExpression valueExpression : Expr}
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType type) target))
    (valueSelected : Selects environment valueExpression value)
    (completed : Evaluates environment store
      (.storeCell referenceExpression (.inRight .unit valueExpression)) result finalStore) :
    ∃ after, result = .unit ∧ Dynamic.Heap.Writes heap location (some sourceValue) after ∧
      GenericHeap.HeapRepresents model mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧
      Dynamic.HeapMetadataExtend heap after ∧
      finalStore.read? target = some (.inRight .unit value) := by
  have written := DataPlaceCommitReflection.source_writes read sourceValue
  obtain ⟨updated, coreWritten, finalHeaps, frame⟩ := heaps.write_initialized reference read represented written
  obtain ⟨_, optional, _, _, _, coreRead, _⟩ := heaps.cells reference.mapped
  have actual : Evaluates environment store
      (.storeCell referenceExpression (.inRight .unit valueExpression)) .unit updated :=
    .storeCell (referenceSelected.evaluates store) coreRead (.inRight (valueSelected.evaluates store)) coreWritten
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed actual
  exact ⟨_, rfl, written, finalHeaps, frame, .of_write written, Store.write?_reads_written coreWritten⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceCommitReflection
