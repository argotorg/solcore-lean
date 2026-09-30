import Solcore.SourceSemantics.CoreLowering.DataPayloadReadPaths
import Solcore.SourceSemantics.CoreLowering.DataPlacePathHelpers
import Solcore.SourceSemantics.CoreLowering.DataMappingHeap

/-! Snapshot extraction uses the actual optional cell and source root rule.
Mapping defaults remain virtual: only comparator administrative cells are
allocated by the getter. The static root-layout receipt authenticates the
empty mapping; runtime typing alone does not authenticate its source metadata.
-/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceSnapshot
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open SourceCoreDataPlaces DataPayloadReadPaths

inductive RootLayout (catalog : SourceCoreDataCatalog.Catalog) (prepared : Prepared) : TypeSystem.Ty → Prop where
  | ordinary {sourceType : TypeSystem.Ty}
      (notMapping : ¬ ∃ key value, sourceType = .mapping key value)
      (layout : prepared.route.rootMapping = none) : RootLayout catalog prepared sourceType
  | mapping {key value : TypeSystem.Ty} {layout : Core.OrderedMapping.Layout}
      (selected : prepared.route.rootMapping = some layout)
      (identity : catalog.identity? (.mapping key value) = some layout.dataType)
      (keyProjected : catalog.project key = .ok layout.keyType)
      (valueProjected : catalog.project value = .ok layout.valueType)
      (registered : layout.Registered catalog.definitions) : RootLayout catalog prepared (.mapping key value)

/-- The optional source snapshot is distinct from a language-result wrapper. -/
inductive OptionalRep (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel catalog) (mapping : LocationMap) (world : StoreTyping)
    (sourceType : TypeSystem.Ty) (type : Ty) : Option Dynamic.Value → Value → Prop where
  | absent : OptionalRep catalog signatures functions mapping world sourceType type none (.inLeft type .unit)
  | present {source : Dynamic.Value} {value : Value}
      (represented : ValueRep catalog signatures functions mapping world sourceType source value type) :
      OptionalRep catalog signatures functions mapping world sourceType type (some source) (.inRight .unit value)

theorem OptionalRep.extend {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {source : Option Dynamic.Value} {value : Value}
    (represented : OptionalRep catalog signatures functions mapping world sourceType type source value)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    OptionalRep catalog signatures functions futureMapping futureWorld sourceType type source value := by
  cases represented with
  | absent => exact .absent
  | present represented => exact .present (represented.extend maps worlds)

theorem OptionalRep.runtime_hasType {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {source : Option Dynamic.Value} {value : Value}
    (represented : OptionalRep catalog signatures functions mapping world sourceType type source value) :
    RuntimeValueHasType world value (OptionalCell.cellType type) catalog.definitions := by
  cases represented with
  | absent => exact .inLeft .unit
  | present represented => exact .inRight represented.runtime_hasType

theorem root_present {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {prepared : Prepared} {cell : Dynamic.Cell} {optional : Value} {source : Dynamic.Value}
    (layout : RootLayout catalog prepared cell.type)
    (represented : GenericHeap.CellRepresents (payloadModel catalog signatures functions) mapping world
      cell optional prepared.route.rootType)
    (initial : Dynamic.RootInitialValue cell (some source)) :
    ∃ value, DataPlacePathHelpers.Root prepared cell optional source value ∧
      ValueRep catalog signatures functions mapping world cell.type source value prepared.route.rootType := by
  cases initial with
  | initialized =>
    cases represented with
    | initialized represented => exact ⟨_, .initialized _ _ _, represented⟩
  | emptyMapping key value =>
    cases layout with
    | ordinary notMapping => exact (notMapping ⟨key, value, rfl⟩).elim
    | @mapping _ _ coreLayout selected identity keyProjected valueProjected registered =>
      cases represented with
      | uninitialized projected =>
        have empty : ValueRep catalog signatures functions mapping world (.mapping key value)
            (.mapping key value []) (Core.OrderedMapping.encode coreLayout []) coreLayout.type :=
          .mapping identity keyProjected valueProjected registered (.empty _ _ _ _)
        have same := Except.ok.inj (empty.projection.symm.trans projected)
        exact ⟨_, by simpa only [← same] using DataPlacePathHelpers.Root.emptyMapping (prepared := prepared) key value selected,
          same ▸ empty⟩

theorem root_absent {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {prepared : Prepared} {cell : Dynamic.Cell} {optional : Value}
    (layout : RootLayout catalog prepared cell.type)
    (represented : GenericHeap.CellRepresents (payloadModel catalog signatures functions) mapping world
      cell optional prepared.route.rootType)
    (initial : Dynamic.RootInitialValue cell none) :
    prepared.route.rootMapping = none ∧ optional = .inLeft prepared.route.rootType .unit := by
  cases initial with
  | uninitialized notMapping =>
    cases layout with
    | ordinary _ empty => cases represented; exact ⟨empty, rfl⟩
    | mapping => exact (notMapping ⟨_, _, rfl⟩).elim

private theorem read_present {source : Dynamic.Value} {projections : List Dynamic.EvaluatedProjection}
    {selected : Option Dynamic.Value} (read : Dynamic.ProjectionsRead (some source) projections selected) :
    ∃ value, selected = some value := by
  generalize initialEq : some source = initial at read
  induction read generalizing source with
  | nil => exact ⟨source, initialEq.symm⟩
  | indexFound _ _ ih => exact ih rfl
  | indexDefault _ _ _ ih => exact ih rfl
  | member _ _ ih => exact ih rfl

theorem path_empty {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {keys : List Value} {root leaf : TypeSystem.Ty} {type leafType : Ty} {steps : List PreparedStep} {count : Nat}
    (path : Path checked signatures functions mapping world keys root type steps [] leaf leafType count) :
    steps = [] ∧ type = leafType ∧ count = 0 := by
  generalize projectionsEq : ([] : List Dynamic.EvaluatedProjection) = projections at path
  induction path with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | member => cases projectionsEq
  | index => cases projectionsEq
  | comptime _ ih => exact ih projectionsEq

/-- The argument is actually evaluated, so it may contain the live loadCell
emitted by execute. All recursive getter evaluations follow from the full
payload and independent projection trace, with no child execution premise. -/
theorem getter_evaluates {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : DataEquality.IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    (prepared : Prepared) {keys : List Value} (keyLength : prepared.keyTypes.length = keys.length)
    {cell : Dynamic.Cell} {optional : Value} {initial selected : Option Dynamic.Value}
    {projections : List Dynamic.EvaluatedProjection} {leaf : TypeSystem.Ty} {count : Nat}
    (rootLayout : RootLayout checked.catalog prepared cell.type)
    (cellRep : GenericHeap.CellRepresents (payloadModel checked.catalog signatures functions) mapping world
      cell optional prepared.route.rootType)
    (root : Dynamic.RootInitialValue cell initial)
    (read : Dynamic.ProjectionsRead initial projections selected)
    (path : Path checked signatures functions mapping world keys cell.type prepared.route.rootType
      prepared.steps projections leaf prepared.route.leafType count)
    {environment : Environment} {before store : Store} {keyType : Ty} {argument : Expr}
    (argumentEvaluated : Evaluates environment before argument (.pair optional (packValues keys)) store) :
    ∃ snapshot finalStore administrative,
      OptionalRep checked.catalog signatures functions mapping world leaf prepared.route.leafType selected snapshot ∧
      Evaluates environment before (.apply (getter prepared keyType) argument) (.inRight .word snapshot) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  cases initial with
  | none =>
    cases read
    obtain ⟨empty, same, rfl⟩ := path_empty path
    obtain ⟨noMapping, rfl⟩ := root_absent rootLayout cellRep root
    refine ⟨.inLeft prepared.route.leafType .unit, store, [], .absent, ?_, by simp, rfl⟩
    apply Evaluates.apply .lambda argumentEvaluated
    simp only [empty, normalizeRoot, noMapping, LanguageResult.success]
    rw [← same]
    exact .inRight (.first (.var rfl))
  | some source =>
    obtain ⟨sourceLeaf, rfl⟩ := read_present read
    obtain ⟨value, normalized, represented⟩ := root_present rootLayout cellRep root
    have tree := path.read_tree observations layouts prepared represented read
    obtain ⟨leafValue, finalStore, administrative, _, leafRep, evaluated, extended, counted⟩ :=
      tree.preserves faithful keyLength (value :: .pair optional (packValues keys) :: environment) store
        (.var 0) (.second (.var 1)) (.var rfl) (.second (.var rfl))
    cases stepsEq : prepared.steps with
    | nil =>
      have empty : Evaluates (value :: .pair optional (packValues keys) :: environment) store
          (select prepared prepared.steps (.var 0) (.second (.var 1))) (.inRight .word (.inRight .unit value)) store := by
        rw [stepsEq]; exact .inRight (.inRight (.var rfl))
      obtain ⟨same, stores⟩ := evaluation_deterministic evaluated empty
      have values := (Value.inRight.inj (Value.inRight.inj same).2).2
      subst leafValue
      rw [stores] at extended
      exact ⟨_, store, administrative, .present leafRep,
        .apply .lambda argumentEvaluated (by simp only [stepsEq]; exact .inRight (normalized.normalizes (.first (.var rfl)) store)),
        extended, counted⟩
    | cons step steps =>
      exact ⟨_, finalStore, administrative, .present leafRep,
        .apply .lambda argumentEvaluated (by
          simp only [stepsEq]
          exact .caseRight (normalized.normalizes (.first (.var rfl)) store) (by simpa only [stepsEq] using evaluated)),
        extended, counted⟩

/-- Read at the already resolved source reference. The runtime world fixes
the optional cell payload type even when other administrative cells coexist. -/
theorem read_at {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {sourceLocation : Dynamic.Location} {target : Location} {type : Ty} {cell : Dynamic.Cell}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (reference : ReferenceRepresents mapping world sourceLocation target type)
    (read : Dynamic.Heap.Reads heap sourceLocation cell) :
    ∃ optional, store.read? target = some optional ∧
      GenericHeap.CellRepresents model mapping world cell optional type := by
  obtain ⟨found, optional, actualType, actualReference, coreRead, represented⟩ := heaps.read read
  have locationEq := Option.some.inj (actualReference.mapped.symm.trans reference.mapped)
  subst found
  have typeEq := Option.some.inj (actualReference.typed.symm.trans reference.typed)
  have same := Ty.sum.inj typeEq
  cases same.2
  exact ⟨optional, coreRead, represented⟩

/-- Complete live-root snapshot phase. The emitted argument performs its own
load; the source heap is unchanged while the Core world includes exactly the
getter's appended administrative cells. -/
theorem preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : DataEquality.IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    (prepared : Prepared) {keys : List Value} (keyLength : prepared.keyTypes.length = keys.length)
    {heap : Dynamic.Heap} {store : Store} {sourceLocation : Dynamic.Location} {target : Location}
    {cell : Dynamic.Cell} {initial selected : Option Dynamic.Value}
    {projections : List Dynamic.EvaluatedProjection} {leaf : TypeSystem.Ty} {count : Nat}
    (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world heap store)
    (reference : ReferenceRepresents mapping world sourceLocation target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap sourceLocation cell)
    (rootLayout : RootLayout checked.catalog prepared cell.type)
    (root : Dynamic.RootInitialValue cell initial)
    (selection : Dynamic.ProjectionsRead initial projections selected)
    (path : Path checked signatures functions mapping world keys cell.type prepared.route.rootType
      prepared.steps projections leaf prepared.route.leafType count)
    {environment : Environment} {context : Core.Context} {keyType : Ty} {referenceExpression keyExpression : Expr}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (helperTyped : HasType context
      (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    (referenceSelected : DataEquality.Selects environment referenceExpression
      (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : DataEquality.Selects environment keyExpression (packValues keys)) :
    ∃ snapshot finalStore futureWorld administrative,
      OptionalRep checked.catalog signatures functions mapping futureWorld leaf prepared.route.leafType selected snapshot ∧
      Evaluates environment store
        (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
        (.inRight .word snapshot) finalStore ∧
      WorldExtends world futureWorld ∧
      GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping futureWorld heap finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨optional, coreRead, cellRep⟩ := read_at heaps reference read
  have argument : Evaluates environment store (.pair (.loadCell referenceExpression) keyExpression)
      (.pair optional (packValues keys)) store :=
    .pair (.loadCell (referenceSelected.evaluates store) coreRead) (keysSelected.evaluates store)
  obtain ⟨snapshot, finalStore, administrative, represented, evaluated, extended, counted⟩ :=
    getter_evaluates observations faithful layouts prepared keyLength rootLayout cellRep root selection path argument
  obtain ⟨futureWorld, extension, finalHeaps, _, frame⟩ :=
    DataMappingHeap.evaluation_preserves_frame heaps environmentTyped helperTyped evaluated extended
  exact ⟨snapshot, finalStore, futureWorld, administrative, represented.extend (.refl _) extension,
    evaluated, extension, finalHeaps, frame, extended, counted⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceSnapshot
