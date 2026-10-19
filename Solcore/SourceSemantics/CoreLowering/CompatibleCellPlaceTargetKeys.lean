import Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceResolution

/-! The common target prefix evaluates every key once and then reads the live
source root metadata. It does not assume that structural selection succeeds.
The receipt below is a semantic output; compiler certificates remain static. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceTargetKeys
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution

structure Execution (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (cells : GenericHeap.CellModel ambient.definitions)
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions) (prepared : Prepared) (place : PlaceResolution)
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
  ordinary : cell.generalized = none
  type : cell.type = prepared.route.rootSourceType
  reference : ReferenceRepresents keyMap keyWorld location target prepared.route.rootType
  selected : coreEnvironment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target)
  shaped : DataPlaceKeyOrder.Values place.projections sources resolved
  evaluated : Evaluates (referenceEnvironment prepared.route.rootType target coreEnvironment) store
    (shift 1 (SourceCoreCalls.packArguments codes).expression) (.inRight .word (packValues values)) keyStore
  related : DataExpressionSequence.Values (payloadModel checked registry functions) keyMap keyWorld sourceTypes (codes.map (·.type)) sources values
  heaps : GenericHeap.CellHeapRepresents cells keyMap keyWorld after keyStore
  maps : LocationMap.Extends mapping keyMap
  worlds : WorldExtends world keyWorld
  frame : AdministrativePreserved mapping store keyMap keyStore
  metadata : Dynamic.HeapMetadataExtend before after
  effect : CellAwareScopeAuthority.Effect instances mapping world before store keyMap keyWorld after keyStore


end Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceTargetKeys
