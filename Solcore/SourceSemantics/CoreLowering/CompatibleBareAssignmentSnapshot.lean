import Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentNative
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhs
import Solcore.SourceSemantics.CoreLowering.TypedGenericExpressionMeaning

/-! Empty projection paths retain an optional snapshot. A declared mapping can
supply an authenticated virtual empty value while its physical cell remains
absent. All native phases run in the actual renamed environment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}

inductive SnapshotRep (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (mapping : LocationMap) (world : StoreTyping) (sourceType : TypeSystem.Ty) (type : Ty) :
    Option Dynamic.Value → Value → Prop where
  | absent : SnapshotRep checked registry functions mapping world sourceType type none (.inLeft type .unit)
  | present {source value} (related : ValueRep checked registry functions mapping world sourceType source value type) :
      SnapshotRep checked registry functions mapping world sourceType type (some source) (.inRight .unit value)

theorem SnapshotRep.runtime_hasType {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {type : Ty} {source : Option Dynamic.Value} {value : Value}
    (related : SnapshotRep checked registry functions mapping world sourceType type source value) :
    RuntimeValueHasType world value (OptionalCell.cellType type) ambient.definitions := by
  cases related with
  | absent => exact .inLeft .unit
  | present related => exact .inRight related.runtime_hasType

theorem SnapshotRep.extend {mapping nextMap : LocationMap} {world nextWorld : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {source : Option Dynamic.Value} {value : Value}
    (related : SnapshotRep checked registry functions mapping world sourceType type source value)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld) :
    SnapshotRep checked registry functions nextMap nextWorld sourceType type source value := by
  cases related with
  | absent => exact .absent
  | present related => exact .present (related.extend (.refl _) maps worlds)

structure Snapshot (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (prepared : Prepared) (place : PlaceResolution) (environment : Dynamic.Environment) (actual : Environment)
    (heap : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping) (index : Nat) where
  location : Dynamic.Location
  target : Location
  cell : Dynamic.Cell
  optional : Value
  initial : Option Dynamic.Value
  value : Value
  lookup : Dynamic.Environment.LooksUp environment place.root location
  read : Dynamic.Heap.Reads heap location cell
  type : cell.type = prepared.route.rootSourceType
  reference : ReferenceRepresents mapping world location target prepared.route.rootType
  nativeLookup : actual[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target)
  nativeRead : store.read? target = some optional
  root : Dynamic.RootInitialValue cell initial
  represented : SnapshotRep checked registry functions mapping world prepared.route.rootSourceType prepared.route.rootType initial value
  normalized : Evaluates (.pair optional .unit :: keysEnvironment prepared.route.rootType target .unit actual)
    store (normalizeRoot prepared (.first (.var 0))) value store

variable {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat}

abbrev Snapshot.resolved (snapshot : Snapshot checked registry functions prepared place environment actual heap store mapping world index) :
    Dynamic.ResolvedPlace := ⟨snapshot.location, snapshot.cell.type, place.type, [], snapshot.initial⟩

theorem Snapshot.resolves {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} (snapshot : Snapshot checked registry functions prepared place environment actual heap store mapping world index)
    (bare : place.projections = []) :
    Dynamic.SourcePlaceResolves program context evidence source environment heap place snapshot.resolved heap :=
  .intro snapshot.lookup snapshot.read (bare ▸ .nil) snapshot.read snapshot.root .nil

theorem Snapshot.resolve_unique {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} (snapshot : Snapshot checked registry functions prepared place environment actual heap store mapping world index)
    (bare : place.projections = []) {resolved : Dynamic.ResolvedPlace} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceResolves program context evidence source environment heap place resolved after) :
    resolved = snapshot.resolved ∧ after = heap := by
  cases trace with
  | intro lookup _ projections read initial selected =>
    rw [bare] at projections
    cases projections
    have same := lookup.functional snapshot.lookup
    cases same
    have same := read.functional snapshot.read
    cases same
    have selectedEq := selected.functional (.nil)
    have initialEq := initial.functional snapshot.root
    exact ⟨by simp only [Snapshot.resolved, selectedEq, initialEq], rfl⟩

theorem Snapshot.getter {compilation : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
    (layout : Layout compilation prepared)
    (snapshot : Snapshot compilation.checked registry functions prepared place environment actual heap store mapping world index) :
    Evaluates (keysEnvironment prepared.route.rootType snapshot.target .unit actual) store
      (.apply (getter prepared .unit) (.pair (.loadCell (.var 1)) (.var 0))) (.inRight .word snapshot.value) store :=
  getter_evaluates layout snapshot.nativeRead snapshot.normalized

theorem Snapshot.runtimeTyped {actualContext : Core.Context}
    (snapshot : Snapshot checked registry functions prepared place environment actual heap store mapping world index)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions) :
    RuntimeEnvironmentHasTypes world (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
      (OptionalCell.cellType prepared.route.rootType :: .unit :: OptionalCell.referenceType prepared.route.rootType :: actualContext)
      ambient.definitions :=
  .cons snapshot.represented.runtime_hasType (.cons .unit (.cons (.cellRef snapshot.reference.typed) typed))

/-- Resolve the real lexical reference, then select its optional snapshot.
The source heap, native store, and location map are unchanged. -/
theorem snapshot_of_heap {compilation : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
    {context : SourceSemantics.Context} {scope : Scope} {administrativeContext : Core.Context}
    {canonical : Environment} {ξ : Renaming}
    (layout : Layout compilation prepared) (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType) :
    Nonempty (Snapshot compilation.checked registry functions prepared place environment actual heap store mapping world (ξ index)) := by
  classical
  obtain ⟨scheme, schemeLookup, _, _, bodyEq⟩ := rootTyped.scheme
  obtain ⟨location, cell, lookup, read, cellType, _⟩ := locals.lookup schemeLookup
  have cellType := cellType.trans bodyEq
  obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible lookup slot
  have nativeLookup := agrees nativeLookup
  obtain ⟨optional, nativeRead, represented⟩ := heaps.read_at reference read
  cases represented with
  | uninitialized projected =>
    by_cases isMapping : ∃ key value, prepared.route.rootSourceType = .mapping key value
    · obtain ⟨key, value, declared⟩ := isMapping
      have sourceType := cellType.trans declared
      simp only at sourceType
      obtain ⟨native, root⟩ := CompatiblePlaceLiveRoot.RootRead.virtual (layout.virtual key value declared)
        extension (sourceType ▸ projected) (sourceType ▸ read) reference nativeRead
      exact ⟨⟨_, _, _, _, _, _, lookup, read, cellType, reference, nativeLookup, nativeRead,
        (sourceType.symm ▸ root.input.initial), .present (declared.symm ▸ root.payload), root.input.normalize _ store _ (.first (.var rfl))⟩⟩
    · have noVirtual := layout.ordinary (fun key value same => isMapping ⟨key, value, same⟩)
      refine ⟨⟨_, _, _, _, _, _, lookup, read, cellType, reference, nativeLookup, nativeRead,
        .uninitialized ?_, .absent, ?_⟩⟩
      · rintro ⟨key, value, same⟩
        exact isMapping ⟨key, value, cellType.symm.trans same⟩
      · simpa only [normalizeRoot, noVirtual] using
          (Evaluates.first (Evaluates.var (index := 0) rfl) :
            Evaluates (.pair (.inLeft prepared.route.rootType .unit) .unit :: keysEnvironment prepared.route.rootType target .unit actual)
              store (.first (.var 0)) (.inLeft prepared.route.rootType .unit) store)
  | initialized related =>
    have root := CompatiblePlaceLiveRoot.RootRead.initialized read reference nativeRead related
    exact ⟨⟨_, _, _, _, _, _, lookup, read, cellType, reference, nativeLookup, nativeRead,
      .initialized, .present (cellType ▸ related), root.input.normalize _ store _ (.first (.var rfl))⟩⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
