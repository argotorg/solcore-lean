import Solcore.SourceSemantics.CoreLowering.CompatibleHeap
import Solcore.SourceSemantics.CoreLowering.GenericCellHeapOperations
import Solcore.SourceSemantics.CoreLowering.CellMappingHeap

/-! Only the selected writable root is ordinary. Getter and setter helpers
retain all other cells, including captured generalized descriptors. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceRoot
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open SourceCoreCompatibleDataPlaces CompatiblePlaceLiveRoot CompatibleHeap

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {cells : GenericHeap.CellModel ambient.definitions}
  (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel checked registry functions) cells)
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}

include ordinaryCells in
/-- Recover the exact optional payload at an existing represented reference.
Native world lookup equates payload types; source cell identity comes from the
independent heap read, never from native type equality. -/
theorem read_at {location : Dynamic.Location} {target : Location} {type : Ty} {cell : Dynamic.Cell}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (reference : ReferenceRepresents mapping world location target type)
    (read : Dynamic.Heap.Reads heap location cell) (ordinary : cell.generalized = none) :
    ∃ value, store.read? target = some value ∧
      GenericHeap.CellRepresents (payloadModel checked registry functions) mapping world cell value type := by
  obtain ⟨actual, value, payload, sourceRead, typed, native, represented⟩ := heaps.cells reference.mapped
  have same := sourceRead.functional read
  subst actual
  have samePayload : payload = type := by
    simpa [OptionalCell.cellType] using Option.some.inj (typed.symm.trans reference.typed)
  subst payload
  exact ⟨value, native, ordinaryCells.project represented ordinary⟩

include ordinaryCells in
/-- Live initialized-root facts are consequences of the common heap relation. -/
theorem initialized_root {prepared : Prepared} {sourceType : TypeSystem.Ty}
    {location : Dynamic.Location} {target : Location} {sourceRoot : Dynamic.Value}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨sourceType, some sourceRoot, none⟩) :
    ∃ value, RootRead checked registry functions mapping world prepared heap store location target
      ⟨sourceType, some sourceRoot, none⟩ (.inRight .unit value) sourceRoot value := by
  obtain ⟨optional, native, represented⟩ := read_at ordinaryCells heaps reference read rfl
  cases represented with
  | initialized related => exact ⟨_, read, reference, native, .initialized, related⟩

/-- The declared mapping remains absent on both heaps while the actual
compiler's encoded empty/default value is supplied to the structural getter. -/
theorem virtual_root {context : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    {functions : FunctionModel context.checked.catalog ambient} {prepared : Prepared}
    {key valueType : TypeSystem.Ty} {location : Dynamic.Location} {target : Location}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel context.checked registry functions) cells)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨.mapping key valueType, none, none⟩)
    (generated : CompatibleMapping.VirtualRoot.Generated context prepared.route key valueType)
    (extension : SourceCoreRawMetadata.Extends context.registry registry) :
    ∃ value, RootRead context.checked registry functions mapping world prepared heap store location target
      ⟨.mapping key valueType, none, none⟩ (.inLeft prepared.route.rootType .unit) (.mapping key valueType []) value := by
  obtain ⟨optional, native, represented⟩ := read_at ordinaryCells heaps reference read rfl
  cases represented with
  | uninitialized projection => exact RootRead.virtual generated extension projection read reference native


/-- The independent Source initial-root receipt selects the actual heap payload. -/
theorem root_of_initial {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {prepared : Prepared} {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location} {target : Location}
    {cell : Dynamic.Cell} {sourceRoot : Dynamic.Value}
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location cell)
    (ordinary : cell.generalized = none)
    (initial : Dynamic.RootInitialValue cell (some sourceRoot))
    (virtual : ∀ key value, cell.type = .mapping key value → CompatibleMapping.VirtualRoot.Generated compilation prepared.route key value)
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry) :
    ∃ optional rootValue, RootRead compilation.checked registry functions mapping world prepared heap store
      location target cell optional sourceRoot rootValue := by
  cases cell with
  | mk type value descriptor =>
   cases ordinary
   cases initial with
   | initialized =>
    obtain ⟨value, root⟩ := initialized_root ordinaryCells heaps reference read
    exact ⟨_, value, root⟩
   | emptyMapping key value =>
    obtain ⟨native, root⟩ := virtual_root ordinaryCells heaps reference read
      (virtual key value rfl) extension
    exact ⟨_, native, root⟩


end Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceRoot
