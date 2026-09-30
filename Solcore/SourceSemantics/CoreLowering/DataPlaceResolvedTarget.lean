import Solcore.SourceSemantics.CoreLowering.DataPlaceSnapshot
import Solcore.SourceSemantics.CoreLowering.DataPlaceChildExpressions

/-! The actual key vector and live-root getter implement source target
resolution. Layout is a static typing/data-layout obligation. Execution is
an output witness constructed from the universal expression theorem and the
independent source trace; it is never an input to the compiler certificate.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceResolvedTarget
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open GenericExpressionMeaning SourceCoreDataPlaces DataPlaceExecution

private theorem packed_type (codes : List SourceCoreBasic.LoweredExpr) :
    SourceCoreDataMatches.bundleType (codes.map (·.type)) = (SourceCoreCalls.packArguments codes).type := by
  induction codes with
  | nil => rfl
  | cons code codes ih => cases codes with
    | nil => rfl
    | cons => exact congrArg (Ty.product code.type) ih

theorem values_typed {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {mapping : LocationMap} {world : StoreTyping} {sourceTypes : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {sources : List Dynamic.Value} {values : List Value}
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

/-- All fields are static metadata, compiler receipts or Core typing. Paths
instantiates those layouts with already related keys; it assumes no runtime
evaluation of a child expression, comparison, default or helper. -/
structure Layout (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel checked.catalog) (source : TypedSource)
    (certificate : Certificate) (scope : Scope) (place : PlaceResolution) (prepared : Prepared)
    (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty) (context : Core.Context) : Prop where
  keys : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes
  keyTypes : prepared.keyTypes = codes.map (·.type)
  root : DataPlaceSnapshot.RootLayout checked.catalog prepared prepared.route.rootSourceType
  paths : ∀ {mapping world sources values projections},
    DataPlaceKeyOrder.Values place.projections sources projections →
    DataExpressionSequence.Values (payloadModel checked.catalog signatures functions) mapping world
      sourceTypes (codes.map (·.type)) sources values →
    ∃ count, DataPayloadReadPaths.Path checked signatures functions mapping world values
      prepared.route.rootSourceType prepared.route.rootType prepared.steps projections place.type prepared.route.leafType count
  getterTyped : HasType ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType :: context)
    (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
    (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions

/-- This is a semantic output witness, including the exact code inserted by
execute. The source heap is the post-index heap throughout getter execution. -/
structure Execution (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel checked.catalog) (prepared : Prepared)
    (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty) (place : PlaceResolution)
    (sourceTarget : Dynamic.ResolvedPlace) (environment : Environment) (initialStore : Store)
    (initialMap : LocationMap) (initialWorld : StoreTyping) (before after : Dynamic.Heap) where
  target : Location
  sources : List Dynamic.Value
  values : List Value
  snapshot : Value
  keyStore : Store
  store : Store
  mapping : LocationMap
  world : StoreTyping
  reference : ReferenceRepresents mapping world sourceTarget.location target prepared.route.rootType
  shaped : DataPlaceKeyOrder.Values place.projections sources sourceTarget.projections
  keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType target environment) initialStore
    (shift 1 (SourceCoreCalls.packArguments codes).expression) (.inRight .word (packValues values)) keyStore
  snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType target (packValues values) environment) keyStore
    (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
    (.inRight .word snapshot) store
  keysRelated : DataExpressionSequence.Values (payloadModel checked.catalog signatures functions) mapping world
    sourceTypes (codes.map (·.type)) sources values
  snapshotRelated : DataPlaceSnapshot.OptionalRep checked.catalog signatures functions mapping world
    place.type prepared.route.leafType sourceTarget.selected snapshot
  heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world after store
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before after

theorem preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : Layout checked signatures functions source certificate scope place prepared codes sourceTypes
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
    (meaning : Preserves (payloadModel checked.catalog signatures functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : DataEquality.IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {sourceTarget : Dynamic.ResolvedPlace} {index : Nat}
    (environments : DataHeap.EnvRepresents checked.catalog mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootType : sourceTarget.rootType = prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget after) :
    ∃ execution : Execution checked signatures functions prepared codes sourceTypes place sourceTarget coreEnvironment
      store mapping world before after,
      coreEnvironment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) execution.target) := by
  cases trace with
  | @intro _ _ _ _ _ _ _ sourceLocation initialCell currentCell projections initial selected
      lookup initialRead evaluate currentRead initialValue selection =>
    obtain ⟨target, coreLookup, reference⟩ := environments.lookup_visible lookup slot
    have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
      intro i v found; exact found
    obtain ⟨sources, values, keyStore, keyMap, keyWorld, shaped, keyEvaluated, keysRelated,
      keyHeaps, keyMaps, keyWorlds, keyFrame, metadata⟩ :=
      DataPlaceKeyOrder.preserves layout.keys meaning environments heaps locals
        (DataPlaceChildExpressions.prefix_agrees sameEnvironment
          [.cellRef (OptionalCell.cellType prepared.route.rootType) target]) evaluate
    have keyEvaluation : Evaluates (referenceEnvironment prepared.route.rootType target coreEnvironment) store
        (shift 1 (SourceCoreCalls.packArguments codes).expression) (.inRight .word (packValues values)) keyStore := by
      simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment] using keyEvaluated
    have currentReference := reference.extend keyMaps keyWorlds
    obtain ⟨count, path⟩ := layout.paths shaped keysRelated
    have keyLength : prepared.keyTypes.length = values.length := layout.keyTypes ▸ keysRelated.length.2
    have rootLayout : DataPlaceSnapshot.RootLayout checked.catalog prepared currentCell.type := by
      simpa only [← rootType] using layout.root
    have currentPath : DataPayloadReadPaths.Path checked signatures functions keyMap keyWorld values
        currentCell.type prepared.route.rootType prepared.steps projections place.type prepared.route.leafType count := by
      simpa only [← rootType] using path
    have typedEnvironment : RuntimeEnvironmentHasTypes keyWorld
        (keysEnvironment prepared.route.rootType target (packValues values) coreEnvironment)
        ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
          (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) checked.catalog.definitions :=
      .cons (values_typed keysRelated)
        (.cons (.cellRef currentReference.typed) ((environments.extend keyMaps keyWorlds).runtime_hasTypes))
    obtain ⟨snapshot, finalStore, finalWorld, administrative, snapshotRelated, snapshotEvaluated,
      extension, finalHeaps, frame, _, _⟩ :=
      DataPlaceSnapshot.preserves observations faithful layouts prepared keyLength keyHeaps currentReference
        currentRead rootLayout initialValue selection currentPath typedEnvironment layout.getterTyped (.var rfl) (.var rfl)
    refine ⟨{ target := target
              sources := sources
              values := values
              snapshot := snapshot
              keyStore := keyStore
              store := finalStore
              mapping := keyMap
              world := finalWorld
              reference := currentReference.extend (.refl _) extension
              shaped := shaped
              keysEvaluated := keyEvaluation
              snapshotEvaluated := snapshotEvaluated
              keysRelated := keysRelated.extend (.refl _) extension
              snapshotRelated := snapshotRelated
              heaps := finalHeaps
              maps := keyMaps
              worlds := keyWorlds.trans extension
              frame := keyFrame.trans frame
              metadata := metadata }, coreLookup⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceResolvedTarget
