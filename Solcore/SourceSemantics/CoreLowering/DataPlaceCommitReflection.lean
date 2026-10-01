import Solcore.SourceSemantics.CoreLowering.DataPlaceSetterReflection
import Solcore.SourceSemantics.CoreLowering.DataPlaceModifierReflection

/-! Reflect execute's final mapped write. The source write is constructed from
the live source cell and the authenticated reconstructed root. No source write
or continuation execution is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceCommitReflection
open Core Frontend Frontend.SourceInference GeneralHeap DataPayload DataEquality

/-- Existing source locations can be updated without changing their declaration
metadata or any other source cell. -/
theorem source_writes {heap : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell}
    (read : Dynamic.Heap.Reads heap location cell) (value : Dynamic.Value) :
    Dynamic.Heap.Writes heap location (some value)
      ⟨heap.cells.set location.index {cell with value := some value}⟩ := by
  have replace : ∀ {cells : List Dynamic.Cell} {index : Nat} {old : Dynamic.Cell},
      Dynamic.Heap.CellAt cells index old →
      Dynamic.Heap.CellsWrite cells index {old with value := some value}
        (cells.set index {old with value := some value}) := by
    intro cells index old selected
    induction selected with
    | head => exact .head
    | tail selected ih => exact .tail ih
  cases read with
  | intro selected => exact .intro (.intro selected) (replace selected)

/-- A constant leaf replacement can be reinterpreted as any independently
proved source modifier producing that value. Traversal and insertion order are
preserved, including duplicate mapping keys. -/
theorem update_of_replacement {Modify : Option Dynamic.Value → Dynamic.Value → Prop}
    {replacement updated : Dynamic.Value} {initial : Option Dynamic.Value}
    {projections : List Dynamic.EvaluatedProjection}
    (changed : Dynamic.ProjectionsUpdate (fun _ value => value = replacement) initial projections updated)
    (modified : ∀ snapshot, Modify snapshot replacement) :
    Dynamic.ProjectionsUpdate Modify initial projections updated := by
  induction changed with
  | leaf same => exact .leaf (same ▸ modified _)
  | indexFound found _ inserted ih => exact .indexFound found ih inserted
  | indexDefault absent defaulted _ inserted ih => exact .indexDefault absent defaulted ih inserted
  | member selected _ replaced ih => exact .member selected ih replaced

/-- Any completed actual storeCell commits precisely the reconstructed source
root once. The mapped heap and old administrative cells are preserved at the
same world; helper allocations have already been reflected before this step. -/
theorem reflects_storeCell {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
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
  have written := source_writes read sourceValue
  obtain ⟨updated, coreWritten, finalHeaps, frame⟩ := heaps.write_initialized reference read represented written
  obtain ⟨_, optional, _, _, _, coreRead, _⟩ := heaps.cells reference.mapped
  have actual : Evaluates environment store
      (.storeCell referenceExpression (.inRight .unit valueExpression)) .unit updated :=
    .storeCell (referenceSelected.evaluates store) coreRead (.inRight (valueSelected.evaluates store)) coreWritten
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed actual
  exact ⟨_, rfl, written, finalHeaps, frame, .of_write written, Store.write?_reads_written coreWritten⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceCommitReflection
