import Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceRhs
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhsReflection

/-! The actual successful RHS retains the saved leaf, latest mixed heap and
exact descriptor effect before the structural writeback suffix. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceRhsReflection
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

structure Execution (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (cells : GenericHeap.CellModel ambient.definitions)
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (environment : Dynamic.Environment) (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr)
    (sourceTypes : List TypeSystem.Ty) (place : PlaceResolution) (leaf : TypeSystem.Ty)
    (target : Dynamic.ResolvedPlace) (coreEnvironment : Environment)
    (initialStore : Store) (initialMap : LocationMap) (initialWorld : StoreTyping) (before targetHeap : Dynamic.Heap)
    (resolution : CompatibleCellPlaceResolution.Execution checked registry functions cells instances prepared codes sourceTypes place leaf target
      coreEnvironment initialStore initialMap initialWorld before targetHeap)
    (id : ExpressionId) (node : ExpressionNode) (lowered : SourceCoreBasic.LoweredExpr) where
  right : Dynamic.Value
  value : Value
  heap : Dynamic.Heap
  store : Store
  mapping : LocationMap
  world : StoreTyping
  meaning : CompatibleCellPlaceRhs.Result (program := program) (context := context) (evidence := evidence) (source := source)
    (faults := faults) resolution id node lowered environment (.value right) heap (.inRight .word value) store mapping world
  related : ValueRep checked registry functions mapping world leaf right value prepared.route.leafType


end Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceRhsReflection
