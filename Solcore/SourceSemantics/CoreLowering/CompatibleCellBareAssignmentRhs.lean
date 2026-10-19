import Solcore.SourceSemantics.CoreLowering.CompatibleCellBareAssignmentSnapshot
import Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentRhs
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeAuthority

/-! A completed RHS retains the original snapshot and reads the same ordinary
root from its actual later mixed heap. Descriptor retention is an executed
child effect, never a compiler premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat}
  {faults : FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}

variable {cells : GenericHeap.CellModel ambient.definitions}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}

variable (snapshot : Snapshot checked registry functions prepared place environment actual heap store mapping world (ξ index))

structure CellRhsResult (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (value : Value)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop where
  trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id outcome after
  evaluated : Evaluates (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
    store (shift 3 (lowered.expression.rename ξ)) value finalStore
  represented : ResultRepresents (payloadModel checked registry functions) finalMap finalWorld node.type lowered.type faults outcome value
  heaps : GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore
  maps : LocationMap.Extends mapping finalMap
  worlds : WorldExtends world finalWorld
  frame : AdministrativePreserved mapping store finalMap finalStore
  metadata : Dynamic.HeapMetadataExtend heap after
  effect : CellAwareScopeAuthority.Effect instances mapping world heap store finalMap finalWorld after finalStore
  latest : Nonempty (CompatiblePlaceRhs.Latest checked registry functions finalMap finalWorld prepared snapshot.resolved snapshot.target after finalStore)

theorem latest_of_cell_heap
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel checked registry functions) cells)
    (ordinary : snapshot.cell.generalized = none) {nextMap : LocationMap} {nextWorld : StoreTyping} {after : Dynamic.Heap} {finalStore : Store}
    (heaps : GenericHeap.CellHeapRepresents cells nextMap nextWorld after finalStore)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    Nonempty (CompatiblePlaceRhs.Latest checked registry functions nextMap nextWorld prepared snapshot.resolved snapshot.target after finalStore) := by
  obtain ⟨cell, read, sameType, sameDescriptor⟩ := metadata _ _ snapshot.read
  have reference := snapshot.reference.extend maps worlds
  obtain ⟨selected, optional, payload, selectedRead, payloadType, nativeRead, represented⟩ :=
    heaps.cells reference.mapped
  have sameCell := read.functional selectedRead
  subst selected
  have samePayload : payload = prepared.route.rootType := by
    simpa [OptionalCell.cellType] using Option.some.inj (payloadType.symm.trans reference.typed)
  subst payload
  have represented := ordinaryCells.project represented (sameDescriptor.trans ordinary)
  exact ⟨⟨cell, optional, read, sameType.trans snapshot.type, reference, nativeRead, represented⟩⟩

/-- Package a completed child and derive its latest ordinary root from the
actual heap metadata extension. -/
theorem cell_rhs_of_expression
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel checked registry functions) cells)
    (ordinary : snapshot.cell.generalized = none)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap} {value : Value}
    {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id outcome after)
    (evaluated : Evaluates (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
      store (shift 3 (lowered.expression.rename ξ)) value finalStore)
    (represented : ResultRepresents (payloadModel checked registry functions) finalMap finalWorld node.type lowered.type faults outcome value)
    (heaps : GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore)
    (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
    (frame : AdministrativePreserved mapping store finalMap finalStore)
    (metadata : Dynamic.HeapMetadataExtend heap after)
    (effect : CellAwareScopeAuthority.Effect instances mapping world heap store finalMap finalWorld after finalStore) :
    CellRhsResult (cells := cells) (instances := instances) (program := program) (context := context) (evidence := evidence) (source := source)
      (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot
      outcome after value finalStore finalMap finalWorld :=
  ⟨trace, evaluated, represented, heaps, maps, worlds, frame, metadata, effect,
    latest_of_cell_heap snapshot ordinaryCells ordinary heaps maps worlds metadata⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
