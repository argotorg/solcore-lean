import Solcore.SourceSemantics.CoreLowering.GenericHeap
import Solcore.SourceSemantics.CoreLowering.DataMappingHeap
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceSnapshot

/-! The compatible carrier instantiates the existing generic heap relation.
The storage catalog supplies only identical Core definitions and environment
layout. Its strict source projection is never used: the explicit projection
relation is the actual compatible catalog projection. Registry extension
transports authenticated payloads while preserving the same physical store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleHeap
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open SourceCoreCompatibleDataPlaces CompatiblePlaceLiveRoot

abbrev projects (catalog : SourceCoreCompatibleCatalog.Catalog) : GenericHeap.Projection :=
  fun source payload => catalog.project source = .ok payload

def payloadModel (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :
    GenericHeap.PayloadModel (storageCatalog checked.catalog) (projects checked.catalog) ambient.definitions where
  Represents := ValueRep checked registry functions
  projection := ValueRep.projection
  runtime_hasType := ValueRep.runtime_hasType
  extend := fun related maps worlds => related.extend (.refl _) maps worlds

abbrev HeapRepresents (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :=
  GenericHeap.HeapRepresents (payloadModel checked registry functions)

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store}

theorem cell_extend_registry {future : SourceCoreRawMetadata.Registry} {cell : Dynamic.Cell} {value : Value} {type : Ty}
    (represented : GenericHeap.CellRepresents (payloadModel checked registry functions) mapping world cell value type)
    (extension : SourceCoreRawMetadata.Extends registry future) :
    GenericHeap.CellRepresents (payloadModel checked future functions) mapping world cell value type := by
  cases represented with
  | uninitialized projected => exact .uninitialized projected
  | initialized related => exact .initialized (related.extend extension (.refl _) (.refl _))

theorem HeapRepresents.extend_registry {future : SourceCoreRawMetadata.Registry}
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (extension : SourceCoreRawMetadata.Extends registry future) :
    HeapRepresents checked future functions mapping world heap store := by
  refine ⟨heaps.length_eq, heaps.injective, heaps.runtime_hasTypes, ?_⟩
  intro source target mapped
  obtain ⟨cell, value, type, read, typed, native, related⟩ := heaps.cells mapped
  exact ⟨cell, value, type, read, typed, native, cell_extend_registry related extension⟩

/-- Recover the exact optional payload at an existing represented reference.
Native world lookup equates payload types; source cell identity comes from the
independent heap read, never from native type equality. -/
theorem HeapRepresents.read_at {location : Dynamic.Location} {target : Location} {type : Ty} {cell : Dynamic.Cell}
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (reference : ReferenceRepresents mapping world location target type)
    (read : Dynamic.Heap.Reads heap location cell) :
    ∃ value, store.read? target = some value ∧
      GenericHeap.CellRepresents (payloadModel checked registry functions) mapping world cell value type := by
  obtain ⟨actual, value, payload, sourceRead, typed, native, represented⟩ := heaps.cells reference.mapped
  have same := sourceRead.functional read
  subst actual
  have samePayload : payload = type := by
    simpa [OptionalCell.cellType] using Option.some.inj (typed.symm.trans reference.typed)
  subst payload
  exact ⟨value, native, represented⟩

/-- Live initialized-root facts are consequences of the common heap relation. -/
theorem HeapRepresents.initialized_root {prepared : Prepared} {sourceType : TypeSystem.Ty}
    {location : Dynamic.Location} {target : Location} {sourceRoot : Dynamic.Value}
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨sourceType, some sourceRoot, none⟩) :
    ∃ value, RootRead checked registry functions mapping world prepared heap store location target
      ⟨sourceType, some sourceRoot, none⟩ (.inRight .unit value) sourceRoot value := by
  obtain ⟨optional, native, represented⟩ := heaps.read_at reference read
  cases represented with
  | initialized related => exact ⟨_, read, reference, native, .initialized, related⟩

/-- The declared mapping remains absent on both heaps while the actual
compiler's encoded empty/default value is supplied to the structural getter. -/
theorem HeapRepresents.virtual_root {context : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    {functions : FunctionModel context.checked.catalog ambient} {prepared : Prepared}
    {key valueType : TypeSystem.Ty} {location : Dynamic.Location} {target : Location}
    (heaps : HeapRepresents context.checked registry functions mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨.mapping key valueType, none, none⟩)
    (generated : CompatibleMapping.VirtualRoot.Generated context prepared.route key valueType)
    (extension : SourceCoreRawMetadata.Extends context.registry registry) :
    ∃ value, RootRead context.checked registry functions mapping world prepared heap store location target
      ⟨.mapping key valueType, none, none⟩ (.inLeft prepared.route.rootType .unit) (.mapping key valueType []) value := by
  obtain ⟨optional, native, represented⟩ := heaps.read_at reference read
  cases represented with
  | uninitialized projection => exact RootRead.virtual generated extension projection read reference native

/-- All source cells survive the snapshot's administrative suffix. No new
source location or source heap update is introduced by a virtual read. -/
theorem HeapRepresents.after_snapshot {futureWorld : StoreTyping} {after suffix : Store}
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (extension : WorldExtends world futureWorld)
    (typed : RuntimeStoreHasTypes futureWorld after ambient.definitions)
    (appended : after = store ++ suffix) :
    HeapRepresents checked registry functions mapping futureWorld heap after := by
  subst after
  exact DataMappingHeap.heap_append heaps extension typed

end Solcore.SourceSemantics.CoreLowering.CompatibleHeap
