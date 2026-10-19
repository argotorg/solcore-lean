import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceResolution
import Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceRoot
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeAuthority
import Solcore.SourceSemantics.CoreLowering.DataPlaceChildExpressions

/-! Effectful key evaluation and the actual compatible live getter implement
target resolution before the RHS starts. The common heap is transported over
the getter's real administrative allocations; virtual mapping roots remain
uninitialized. No child or helper execution is a static premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceResolution
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceLiveRoot

/-- The source selected value and exact key/snapshot native runs are outputs
of resolution. The source heap is unchanged by snapshot helper allocation. -/
structure Execution (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (cells : GenericHeap.CellModel ambient.definitions)
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions) (prepared : Prepared)
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
  ordinary : currentCell.generalized = none
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
  heaps : GenericHeap.CellHeapRepresents cells mapping world after store
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before after
  effect : CellAwareScopeAuthority.Effect instances initialMap initialWorld before initialStore mapping world after store


end Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceResolution
