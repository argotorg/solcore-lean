import Solcore.SourceSemantics.CoreLowering.GenericCellHeap

/-! Ordinary operations in a heap which may also retain generalized cells.
Only the cell actually read or written needs an ordinary storage receipt.
The other cells, the source heap and the native location map stay intact. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericHeap
open Core Frontend SourceInference TypeSystem GeneralHeap

structure OrdinaryCells {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection}
    {definitions : DataEnvironment} (payloads : PayloadModel catalog projects definitions)
    (cells : CellModel definitions) : Prop where
  inject : ∀ {mapping world cell value type},
    CellRepresents payloads mapping world cell value type →
    cells.Represents mapping world cell value type
  project : ∀ {mapping world cell value type},
    cells.Represents mapping world cell value type → cell.generalized = none →
    CellRepresents payloads mapping world cell value type

theorem OrdinaryCells.ordinary {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection}
    {definitions : DataEnvironment} (payloads : PayloadModel catalog projects definitions) :
    OrdinaryCells payloads (.ordinary payloads) := ⟨fun value => value, fun value _ => value⟩

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection} {definitions : DataEnvironment}
  {payloads : PayloadModel catalog projects definitions} {cells : CellModel definitions}

theorem CellHeapRepresents.fresh_unmapped {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} (heaps : CellHeapRepresents cells mapping world heap store) :
    ∀ {source : Nat}, mapping[source]? ≠ some store.length := by
  intro source mapped
  exact Nat.lt_irrefl _ (heaps.target_lt mapped)

theorem CellHeapRepresents.read_ordinary (ordinary : OrdinaryCells payloads cells)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (heaps : CellHeapRepresents cells mapping world heap store)
    (read : Dynamic.Heap.Reads heap location cell) (absent : cell.generalized = none) :
    ∃ target value type, ReferenceRepresents mapping world location target type ∧
      store.read? target = some value ∧ CellRepresents payloads mapping world cell value type := by
  obtain ⟨target, value, type, reference, found, related⟩ := heaps.read read
  exact ⟨target, value, type, reference, found, ordinary.project related absent⟩

theorem CellHeapRepresents.write_initialized (ordinary : OrdinaryCells payloads cells)
    {mapping : LocationMap} {world : StoreTyping} {heap after : Dynamic.Heap} {store : Store}
    {location : Dynamic.Location} {target : Core.Location} {type : Core.Ty}
    {cell : Dynamic.Cell} {source : Dynamic.Value} {native : Core.Value}
    (heaps : CellHeapRepresents cells mapping world heap store)
    (reference : ReferenceRepresents mapping world location target type)
    (read : Dynamic.Heap.Reads heap location cell) (absent : cell.generalized = none)
    (represented : payloads.Represents mapping world cell.type source native type)
    (written : Dynamic.Heap.Writes heap location (some source) after) :
    ∃ updated, store.write? target (.inRight .unit native) = some updated ∧
      CellHeapRepresents cells mapping world after updated ∧
      AdministrativePreserved mapping store mapping updated := by
  cases written with
  | @intro previous sourceCells previousRead written =>
      have same := read.functional previousRead
      subst previous
      have replacement : cells.Represents mapping world {cell with value := some source}
          (.inRight .unit native) type := by
        apply ordinary.inject
        cases cell
        simp only at absent represented ⊢
        subst_vars
        exact .initialized represented
      obtain ⟨updated, coreWritten, final⟩ := heaps.replace reference written replacement
      exact ⟨updated, coreWritten, final,
        AdministrativePreserved.write (List.mem_of_getElem? reference.mapped) coreWritten⟩

theorem CellHeapRepresents.bind_ordinary (ordinary : OrdinaryCells payloads cells)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment} {canonical : Core.Environment}
    {heap after : Dynamic.Heap} {store : Store} {id : Resolved.LocalId}
    {sourceType : TypeSystem.Ty} {sourceValue : Option Dynamic.Value} {location : Dynamic.Location}
    {value : Core.Value} {type : Core.Ty}
    (environments : EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : CellHeapRepresents cells mapping world heap store)
    (represented : CellRepresents payloads mapping world ⟨sourceType, sourceValue, none⟩ value type)
    (allocated : Dynamic.Heap.Allocates heap sourceType sourceValue location after) :
    EnvRepresents catalog (mapping ++ [store.length]) (world ++ [OptionalCell.cellType type])
      administrative ((id, type) :: scope) ((id, location) :: environment)
      (.cellRef (OptionalCell.cellType type) store.length :: canonical) definitions ∧
      CellHeapRepresents cells (mapping ++ [store.length]) (world ++ [OptionalCell.cellType type])
        after (store.allocate value).1 := by
  obtain ⟨next, reference⟩ := heaps.allocate_ordinary (ordinary.inject represented) allocated
  exact ⟨.cons reference (environments.extend ⟨_, rfl⟩ ⟨_, rfl⟩), next⟩

end Solcore.SourceSemantics.CoreLowering.GenericHeap
