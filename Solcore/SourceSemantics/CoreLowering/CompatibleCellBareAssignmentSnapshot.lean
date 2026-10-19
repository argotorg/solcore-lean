import Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentSnapshot
import Solcore.SourceSemantics.CoreLowering.GenericCellHeapOperations
import Solcore.SourceSemantics.CoreLowering.CompatibleCellReadCompletion

/-! A writable monomorphic root selects an ordinary cell in the actual mixed
heap. The snapshot and native getter retain the existing transaction layout. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution

variable {registry : SourceCoreRawMetadata.Registry}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment}
  {actual : Environment} {heap : Dynamic.Heap} {store : Store}
  {mapping : LocationMap} {world : StoreTyping} {index : Nat}

/-- Resolve the real lexical reference, then select its optional snapshot.
The source heap, native store, and location map are unchanged. -/
theorem snapshot_of_cell_heap {compilation : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
    {context : SourceSemantics.Context} {scope : Scope} {administrativeContext : Core.Context}
    {canonical : Environment} {ξ : Renaming}
    (layout : Layout compilation prepared) (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    {cells : GenericHeap.CellModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells
      (payloadModel compilation.checked registry functions) cells)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped context heap)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType) :
    ∃ snapshot : Snapshot compilation.checked registry functions prepared place environment actual heap store mapping world (ξ index),
      snapshot.cell.generalized = none := by
  classical
  obtain ⟨scheme, schemeLookup, _, monomorphic, bodyEq⟩ := rootTyped.scheme
  obtain ⟨location, cell, lookup, read, cellType, _⟩ := locals.lookup schemeLookup
  have cellType := cellType.trans bodyEq
  obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible lookup slot
  have nativeLookup := agrees nativeLookup
  obtain ⟨actualCell, optional, payload, actualRead, payloadType, nativeRead, represented⟩ :=
    heaps.cells reference.mapped
  have sameCell := read.functional actualRead
  subst actualCell
  have samePayload : payload = prepared.route.rootType := by
    simpa [OptionalCell.cellType] using Option.some.inj (payloadType.symm.trans reference.typed)
  subst payload
  have ordinary := locals.descriptor_empty_of_monomorphic heapTyped schemeLookup lookup read monomorphic
  have represented := ordinaryCells.project represented ordinary
  cases represented with
  | uninitialized projected =>
    by_cases isMapping : ∃ key value, prepared.route.rootSourceType = .mapping key value
    · obtain ⟨key, value, declared⟩ := isMapping
      have sourceType := cellType.trans declared
      simp only at sourceType
      obtain ⟨native, root⟩ := CompatiblePlaceLiveRoot.RootRead.virtual (layout.virtual key value declared)
        extension (sourceType ▸ projected) (sourceType ▸ read) reference nativeRead
      exact ⟨⟨_, _, _, _, _, _, lookup, read, cellType, reference, nativeLookup, nativeRead,
        (sourceType.symm ▸ root.input.initial), .present (declared.symm ▸ root.payload), root.input.normalize _ store _ (.first (.var rfl))⟩, rfl⟩
    · have noVirtual := layout.ordinary (fun key value same => isMapping ⟨key, value, same⟩)
      refine ⟨⟨_, _, _, _, _, _, lookup, read, cellType, reference, nativeLookup, nativeRead,
        .uninitialized ?_, .absent, ?_⟩, rfl⟩
      · rintro ⟨key, value, same⟩
        exact isMapping ⟨key, value, cellType.symm.trans same⟩
      · simpa only [normalizeRoot, noVirtual] using
          (Evaluates.first (Evaluates.var (index := 0) rfl) :
            Evaluates (.pair (.inLeft prepared.route.rootType .unit) .unit :: keysEnvironment prepared.route.rootType target .unit actual)
              store (.first (.var 0)) (.inLeft prepared.route.rootType .unit) store)
  | initialized related =>
    have root := CompatiblePlaceLiveRoot.RootRead.initialized read reference nativeRead related
    exact ⟨⟨_, _, _, _, _, _, lookup, read, cellType, reference, nativeLookup, nativeRead,
      .initialized, .present (cellType ▸ related), root.input.normalize _ store _ (.first (.var rfl))⟩, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
