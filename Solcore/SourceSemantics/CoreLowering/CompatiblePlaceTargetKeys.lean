import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceResolution

/-! The common target prefix evaluates every key once and then reads the live
source root metadata. It does not assume that structural selection succeeds.
The receipt below is a semantic output; compiler certificates remain static. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceTargetKeys
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution

structure Execution (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (prepared : Prepared) (place : PlaceResolution)
    (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (location : Dynamic.Location) (resolved : List Dynamic.EvaluatedProjection)
    (coreEnvironment : Environment) (before after : Dynamic.Heap) (store : Store)
    (mapping : LocationMap) (world : StoreTyping) (index : Nat) where
  target : Location
  sources : List Dynamic.Value
  values : List Value
  keyStore : Store
  keyMap : LocationMap
  keyWorld : StoreTyping
  cell : Dynamic.Cell
  read : Dynamic.Heap.Reads after location cell
  type : cell.type = prepared.route.rootSourceType
  reference : ReferenceRepresents keyMap keyWorld location target prepared.route.rootType
  selected : coreEnvironment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target)
  shaped : DataPlaceKeyOrder.Values place.projections sources resolved
  evaluated : Evaluates (referenceEnvironment prepared.route.rootType target coreEnvironment) store
    (shift 1 (SourceCoreCalls.packArguments codes).expression) (.inRight .word (packValues values)) keyStore
  related : DataExpressionSequence.Values (payloadModel checked registry functions) keyMap keyWorld sourceTypes (codes.map (·.type)) sources values
  heaps : HeapRepresents checked registry functions keyMap keyWorld after keyStore
  maps : LocationMap.Extends mapping keyMap
  worlds : WorldExtends world keyWorld
  frame : AdministrativePreserved mapping store keyMap keyStore
  metadata : Dynamic.HeapMetadataExtend before after

/-- Successful key expressions supply the current root after all their effects.
Exact declared source type comes from WritableLocal and environment agreement. -/
theorem preserves {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {prepared : Prepared} {place : PlaceResolution}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    (meaning : Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {resolved : List Dynamic.EvaluatedProjection} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after) :
    Nonempty (Execution checked registry functions prepared place codes sourceTypes location resolved coreEnvironment before after store mapping world index) := by
  obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slot
  have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by intro _ _ found; exact found
  obtain ⟨sources, values, keyStore, keyMap, keyWorld, shaped, evaluated, related, keyHeaps, maps, worlds, frame, metadata⟩ :=
    DataPlaceKeyOrder.preserves children meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees sameEnvironment [.cellRef (OptionalCell.cellType prepared.route.rootType) target]) trace
  obtain ⟨scheme, staticLookup, _, _, bodyEq⟩ := rootTyped.scheme
  obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
  have locationEq := lookup.functional staticLookupRuntime
  subst staticLocation
  have cellEq := initialRead.functional staticRead
  subst staticCell
  obtain ⟨currentCell, currentRead, currentType, _⟩ := metadata _ _ initialRead
  exact ⟨⟨target, sources, values, keyStore, keyMap, keyWorld, currentCell, currentRead,
    currentType.trans (staticCellType.trans bodyEq), reference.extend maps worlds, selected, shaped,
    by simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
      List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated,
    related, keyHeaps, maps, worlds, frame, metadata⟩⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceTargetKeys
