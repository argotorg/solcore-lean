import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceKeyTyping
import Solcore.SourceSemantics.CoreLowering.DataPlaceChildExpressions

/-! Effectful key evaluation and the actual compatible live getter implement
target resolution before the RHS starts. The common heap is transported over
the getter's real administrative allocations; virtual mapping roots remain
uninitialized. No child or helper execution is a static premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceResolution
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceLiveRoot

private theorem packed_type (codes : List SourceCoreBasic.LoweredExpr) :
    SourceCoreDataMatches.bundleType (codes.map (·.type)) = (SourceCoreCalls.packArguments codes).type := by
  induction codes with
  | nil => rfl
  | cons code codes ih => cases codes with
    | nil => rfl
    | cons => exact congrArg (Ty.product code.type) ih

theorem values_typed {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel catalog projects} {mapping : LocationMap} {world : StoreTyping}
    {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {sources : List Dynamic.Value} {values : List Value}
    (represented : DataExpressionSequence.Values model mapping world sourceTypes (codes.map (·.type)) sources values) :
    RuntimeValueHasType world (packValues values) (SourceCoreCalls.packArguments codes).type catalog.definitions := by
  rw [← packed_type]
  generalize typesEq : codes.map (·.type) = types at represented ⊢
  clear typesEq codes
  induction represented with
  | nil => exact .unit
  | cons head tail ih => cases tail with
    | nil => exact model.runtime_hasType head
    | cons => exact .pair (model.runtime_hasType head) ih

private theorem path_length {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf) : steps.length = projections.length := by
  induction path with
  | nil => rfl
  | member _ _ _ _ ih | index _ _ _ ih => exact congrArg Nat.succ ih

private theorem shape_length {projections : List PlaceProjection} {sources : List Dynamic.Value}
    {resolved : List Dynamic.EvaluatedProjection} (shape : DataPlaceKeyOrder.Values projections sources resolved) :
    resolved.length = projections.length := by
  induction shape with
  | nil => rfl
  | member _ ih | index _ ih => exact congrArg Nat.succ ih

private theorem read_present {root : Dynamic.Value} {projections : List Dynamic.EvaluatedProjection}
    {selected : Option Dynamic.Value} (read : Dynamic.ProjectionsRead (some root) projections selected) :
    ∃ value, selected = some value := by
  generalize initialEq : some root = initial at read
  induction read generalizing root with
  | nil => exact ⟨root, initialEq.symm⟩
  | indexFound _ _ ih | indexDefault _ _ _ ih | member _ _ ih => exact ih rfl

/-- The source selected value and exact key/snapshot native runs are outputs
of resolution. The source heap is unchanged by snapshot helper allocation. -/
structure Execution (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    (functions : FunctionModel checked.catalog) (prepared : Prepared)
    (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (leaf : TypeSystem.Ty) (sourceTarget : Dynamic.ResolvedPlace)
    (environment : Environment) (initialStore : Store) (initialMap : LocationMap)
    (initialWorld : StoreTyping) (before after : Dynamic.Heap) where
  target : Location
  sources : List Dynamic.Value
  values : List Value
  selected : Dynamic.Value
  snapshot : Value
  keyStore : Store
  store : Store
  mapping : LocationMap
  world : StoreTyping
  selectedEq : sourceTarget.selected = some selected
  currentCell : Dynamic.Cell
  currentRead : Dynamic.Heap.Reads after sourceTarget.location currentCell
  currentType : currentCell.type = prepared.route.rootSourceType
  reference : ReferenceRepresents mapping world sourceTarget.location target prepared.route.rootType
  shaped : DataPlaceKeyOrder.Values place.projections sources sourceTarget.projections
  keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType target environment) initialStore
    (shift 1 (SourceCoreCalls.packArguments codes).expression) (.inRight .word (packValues values)) keyStore
  snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType target (packValues values) environment) keyStore
    (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
    (.inRight .word (.inRight .unit snapshot)) store
  keysRelated : DataExpressionSequence.Values (payloadModel checked registry functions) mapping world
    sourceTypes (codes.map (·.type)) sources values
  snapshotRelated : ValueRep checked registry functions mapping world leaf selected snapshot prepared.route.leafType
  heaps : HeapRepresents checked registry functions mapping world after store
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before after

/-- Successful source resolution constructs the actual key and getter runs.
The universal child theorem covers every intermediate key heap and hidden
reference slot. Independent writable-local typing and environment agreement
recover the exact raw root declaration type. -/
theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel compilation.checked.catalog}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (path : PreparedPath compilation.checked source site prepared.route.rootSourceType place.projections
      0 prepared.steps prepared.keys leaf)
    (views : KeyViews path sourceTypes)
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    (keyTypes : prepared.keyTypes = codes.map (·.type))
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (virtual : ∀ key value, prepared.route.rootSourceType = .mapping key value →
      CompatibleMapping.VirtualRoot.Generated compilation prepared.route key value)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
        (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
      (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) compilation.checked.catalog.definitions)
    (meaning : Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {sourceTarget : Dynamic.ResolvedPlace} {index : Nat}
    (environments : DataHeap.EnvRepresents (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget after) :
    ∃ execution : Execution compilation.checked registry functions prepared codes sourceTypes place leaf sourceTarget
      coreEnvironment store mapping world before after,
      coreEnvironment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) execution.target) := by
  cases trace with
  | @intro _ _ _ _ _ _ _ sourceLocation initialCell currentCell projections initial selected
      lookup initialRead evaluate currentRead initialValue selection =>
    obtain ⟨target, coreLookup, reference⟩ := environments.lookup_visible lookup slot
    have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
      intro _ _ found; exact found
    obtain ⟨sources, values, keyStore, keyMap, keyWorld, shaped, keyEvaluated, keysRelated,
      keyHeaps, keyMaps, keyWorlds, keyFrame, metadata⟩ :=
      DataPlaceKeyOrder.preserves children meaning environments heaps locals
        (DataPlaceChildExpressions.prefix_agrees sameEnvironment [.cellRef (OptionalCell.cellType prepared.route.rootType) target]) evaluate
    have keyEvaluation : Evaluates (referenceEnvironment prepared.route.rootType target coreEnvironment) store
        (shift 1 (SourceCoreCalls.packArguments codes).expression) (.inRight .word (packValues values)) keyStore := by
      simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using keyEvaluated
    obtain ⟨scheme, staticLookup, _, _, bodyEq⟩ := rootTyped.scheme
    obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
    have locationEq := lookup.functional staticLookupRuntime
    subst staticLocation
    have cellEq := initialRead.functional staticRead
    subst staticCell
    obtain ⟨updated, updatedRead, updatedType, _⟩ := metadata _ _ initialRead
    have currentEq := currentRead.functional updatedRead
    subst updated
    have rootType : currentCell.type = prepared.route.rootSourceType := updatedType.trans (staticCellType.trans bodyEq)
    have currentReference := reference.extend keyMaps keyWorlds
    have arguments := views.arguments shaped keysRelated (fun _ _ found => by simpa only [Nat.zero_add] using found)
    have keyLength : prepared.keyTypes.length = values.length := keyTypes ▸ keysRelated.length.2
    have typedEnvironment : RuntimeEnvironmentHasTypes keyWorld
        (keysEnvironment prepared.route.rootType target (packValues values) coreEnvironment)
        ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
          (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) compilation.checked.catalog.definitions :=
      .cons (values_typed keysRelated)
        (.cons (.cellRef currentReference.typed) ((environments.extend keyMaps keyWorlds).runtime_hasTypes))
    have resolvedNonempty : projections ≠ [] := by
      intro empty
      have length := (path_length path).trans (shape_length shaped).symm
      rw [empty, List.length_nil] at length
      exact nonempty (List.eq_nil_of_length_eq_zero length)
    have present : ∃ sourceRoot, initial = some sourceRoot := by
      cases initial with
      | some value => exact ⟨value, rfl⟩
      | none => cases selection with | nil => exact (resolvedNonempty rfl).elim
    obtain ⟨sourceRoot, rfl⟩ := present
    obtain ⟨selectedValue, rfl⟩ := read_present selection
    have rootExists : ∃ optional rootValue,
        RootRead compilation.checked registry functions keyMap keyWorld prepared after keyStore sourceLocation target
          currentCell optional sourceRoot rootValue := by
      cases initialValue with
      | initialized =>
        obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root keyHeaps currentReference currentRead
        exact ⟨_, value, root⟩
      | emptyMapping key value =>
        obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root keyHeaps currentReference currentRead (virtual key value rootType.symm) registryExtension
        exact ⟨_, native, root⟩
    obtain ⟨optional, rootValue, root⟩ := rootExists
    have represented : ValueRep compilation.checked registry functions keyMap keyWorld
        prepared.route.rootSourceType sourceRoot rootValue prepared.route.rootType := by
      simpa only [← rootType] using root.payload
    have tree := arguments.readTree represented leafProjected selection prepared
    have tree : CompatibleMapping.MixedPaths.ReadTree compilation.checked registry functions keyMap keyWorld prepared values
        leaf prepared.route.leafType currentCell.type sourceRoot rootValue prepared.steps projections selectedValue
        (readCost compilation.checked prepared.steps) := by simpa only [rootType] using tree
    obtain ⟨snapshot, finalStore, administrative, _, _, related, evaluated, appended, _⟩ :=
      readTree_at root tree nonempty faithful observations keyLength
        (keysEnvironment prepared.route.rootType target (packValues values) coreEnvironment)
        (SourceCoreCalls.packArguments codes).type (.var 1) (.var 0) (.var rfl) (.var rfl)
    obtain ⟨finalWorld, extension, typedStore, _, frame⟩ :=
      evaluation_frame (mapping := keyMap) keyHeaps.runtime_hasTypes typedEnvironment getterTyped evaluated appended
    refine ⟨{ target := target
              sources := sources
              values := values
              selected := selectedValue
              snapshot := snapshot
              keyStore := keyStore
              store := finalStore
              mapping := keyMap
              world := finalWorld
              selectedEq := rfl
              currentCell := currentCell
              currentRead := currentRead
              currentType := rootType
              reference := currentReference.extend (.refl _) extension
              shaped := shaped
              keysEvaluated := keyEvaluation
              snapshotEvaluated := evaluated
              keysRelated := keysRelated.extend (.refl _) extension
              snapshotRelated := related.extend (.refl _) (.refl _) extension
              heaps := CompatibleHeap.HeapRepresents.after_snapshot keyHeaps extension typedStore appended
              maps := keyMaps
              worlds := keyWorlds.trans extension
              frame := keyFrame.trans frame
              metadata := metadata }, coreLookup⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceResolution
