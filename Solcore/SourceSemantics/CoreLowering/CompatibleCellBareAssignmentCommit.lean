import Solcore.SourceSemantics.CoreLowering.CompatibleCellBareAssignmentRhs
import Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentCommit

/-! The final setter writes the post-RHS ordinary root while using the saved
pre-RHS snapshot for the modifier. Actual descriptor rows retain their source
metadata and native values through the completed write. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution CoreProof

variable {registry : SourceCoreRawMetadata.Registry}
  {mapping : LocationMap} {world : StoreTyping}

variable {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {index : Nat} {ξ : Renaming}
  {faults : FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}

/-- A successful RHS and modifier produce an exact whole-prefix agreement,
including typed seven slots for the real renamed continuation. -/
theorem cell_commit_with_write {compilation : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells (payloadModel compilation.checked registry functions) cells)
    (layout : Layout compilation prepared)
    (snapshot : Snapshot compilation.checked registry functions prepared place environment actual heap store mapping world (ξ index))
    (bare : place.projections = [])
    {right updated : Dynamic.Value} {rightValue updatedValue : Value} {rhsHeap : Dynamic.Heap}
    {rhsStore : Store} {rhsMap : LocationMap} {rhsWorld : StoreTyping} {operator : Syntax.ValueAssignOp} {invalid : Word}
    (rhs : CellRhsResult (cells := cells) (instances := instances) (program := program) (context := context) (evidence := evidence) (source := source)
      (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot (.value right) rhsHeap
        (.inRight .word rightValue) rhsStore rhsMap rhsWorld)
    (rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld prepared.route.rootSourceType right rightValue prepared.route.rootType)
    (replacement : ValueRep compilation.checked registry functions rhsMap rhsWorld prepared.route.rootSourceType updated updatedValue prepared.route.rootType)
    (applied : Dynamic.AssignmentValueApplies operator snapshot.initial right updated)
    (modified : Evaluates (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual) rhsStore
      (modified prepared.route.leafType (binaryOperator (prepared.route.leafType = .integer) operator) false (.var 1) (.var 0) invalid)
      (.inRight .word updatedValue) rhsStore)
    {actualContext : Core.Context} (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions) :
    ∃ after finalStore,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment heap place id updated after ∧
      Dynamic.Heap.Writes rhsHeap snapshot.location (some updated) after ∧
      GenericHeap.CellHeapRepresents cells rhsMap rhsWorld after finalStore ∧
      AdministrativePreserved mapping store rhsMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      RuntimeEnvironmentHasTypes rhsWorld
        (writtenEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue updatedValue updatedValue actual)
        (writtenContext prepared actualContext) ambient.definitions ∧
      AdministrativePreserved rhsMap rhsStore rhsMap finalStore ∧
      Dynamic.HeapMetadataExtend rhsHeap after ∧
      CellAwareScopeAuthority.Effect instances mapping world heap store rhsMap rhsWorld after finalStore ∧
      ∀ next outputType, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (writtenEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue updatedValue updatedValue actual)
        finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨latest⟩ := rhs.latest
  obtain ⟨initial, initialValue⟩ := cell_initial latest.related
  have written := DataPlaceCommitReflection.source_writes latest.read updated
  obtain ⟨finalStore, coreWritten, finalHeaps, writeFrame⟩ :=
    rhs.heaps.write_initialized ordinaryCells latest.reference latest.read latest.related.ordinary
      (latest.type.symm ▸ replacement) written
  have writeEffect : CellAwareScopeAuthority.Effect instances rhsMap rhsWorld rhsHeap rhsStore rhsMap rhsWorld
      ⟨rhsHeap.cells.set snapshot.location.index {latest.cell with value := some updated}⟩ finalStore :=
    .write_ordinary rhs.heaps.injective latest.read latest.related.ordinary latest.reference written coreWritten
  have trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment heap place id updated
        ⟨rhsHeap.cells.set snapshot.location.index {latest.cell with value := some updated}⟩ := by
    cases rhs.trace with
    | value right =>
      exact .intro (snapshot.resolves bare) right
        (.intro latest.read (latest.type.trans snapshot.type.symm) initialValue (.leaf applied) written)
  refine ⟨_, finalStore, trace, written, finalHeaps, rhs.frame.trans writeFrame, rhs.metadata.trans (.of_write written), ?_, writeFrame, .of_write written, rhs.effect.trans writeEffect, ?_⟩
  · exact .cons .unit (.cons replacement.runtime_hasType (.cons replacement.runtime_hasType
      (.cons rightRep.runtime_hasType (.cons (snapshot.represented.extend rhs.maps rhs.worlds).runtime_hasType
        (.cons .unit (.cons (.cellRef latest.reference.typed) (actualTyped.weaken rhs.worlds)))))))
  · intro next outputType
    exact (snapshot_prefix layout snapshot _ _ _ _ _).trans
      ((ContinuationAgreement.bind rhs.evaluated).trans
        ((ContinuationAgreement.bind modified).trans
          ((ContinuationAgreement.bind (setter_evaluates layout snapshot.value rightValue updatedValue latest.nativeRead)).trans
            (ContinuationAgreement.letE (.storeCell (.var rfl) latest.nativeRead (.inRight (.var rfl)) coreWritten)))))
end Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
