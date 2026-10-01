import Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentRhs
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceModifier
import Solcore.SourceSemantics.CoreLowering.DataPlaceCommitReflection

/-! A bare transaction either fails at the optional snapshot modifier or
writes its represented replacement to the post-RHS live cell. The generated
setter and final store operation run in their actual captured environments. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution CoreProof

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping}

/-- Both modifier outcomes are constructed from authenticated saved/RHS
values. An absent compound snapshot fails after the RHS has completed. -/
theorem modifier_total {sourceType : TypeSystem.Ty} {type : Ty} {initial : Option Dynamic.Value}
    {snapshot rightCore : Value} {right : Dynamic.Value} {operator : Syntax.ValueAssignOp}
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog functions identities)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType sourceType = .word ∨
      SourceCoreRawMetadata.runtimeType sourceType = .integer)
    (saved : SnapshotRep checked registry functions mapping world sourceType type initial snapshot)
    (rightRep : ValueRep checked registry functions mapping world sourceType right rightCore type)
    {environment : Environment} {snapshotExpression rightExpression : Expr}
    (snapshotSelected : DataEquality.Selects environment snapshotExpression snapshot)
    (rightSelected : DataEquality.Selects environment rightExpression rightCore) (store : Store) (invalid : Word) :
    (Dynamic.AssignmentOperandsInvalid operator initial right ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshotExpression rightExpression invalid)
        (.inLeft type (.word invalid)) store) ∨
    ∃ result value, ValueRep checked registry functions mapping world sourceType result value type ∧
      Dynamic.AssignmentValueApplies operator initial right result ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshotExpression rightExpression invalid)
        (.inRight .word value) store := by
  cases saved with
  | present related =>
    obtain ⟨result, value, related, applied, evaluated, _⟩ :=
      CompatiblePlaceModifier.initialized_success observations profile related rightRep snapshotSelected rightSelected store invalid
    exact .inr ⟨result, value, related, applied, evaluated⟩
  | absent =>
    by_cases equal : operator = .equal
    · subst operator
      exact .inr ⟨right, rightCore, rightRep, .equal _ _, .inRight (rightSelected.evaluates store)⟩
    · refine .inl ⟨.uninitialized equal, ?_⟩
      cases operator <;> first
      | exact (equal rfl).elim
      | (by_cases integer : type = .integer <;>
          simp only [binaryOperator, integer, ite_true, ite_false, modified] <;>
          exact .caseLeft (snapshotSelected.evaluates store) (.inLeft .word))

theorem cell_initial {cell : Dynamic.Cell} {value : Value} {type : Ty}
    (related : GenericHeap.CellRepresents (payloadModel checked registry functions) mapping world cell value type) :
    ∃ initial, Dynamic.RootInitialValue cell initial := by
  classical
  cases related with
  | initialized _ => exact ⟨_, .initialized⟩
  | @uninitialized sourceType _ =>
    by_cases isMapping : ∃ key value, sourceType = .mapping key value
    · obtain ⟨key, value, rfl⟩ := isMapping
      exact ⟨_, .emptyMapping key value⟩
    · exact ⟨_, .uninitialized isMapping⟩

def writtenContext (prepared : Prepared) (context : Core.Context) : Core.Context :=
  .unit :: prepared.route.rootType :: prepared.route.rootType :: prepared.route.rootType ::
    OptionalCell.cellType prepared.route.rootType :: .unit :: OptionalCell.referenceType prepared.route.rootType :: context

variable {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {index : Nat} {ξ : Renaming}
  {faults : FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}

/-- A successful RHS and modifier produce an exact whole-prefix agreement,
including typed seven slots for the real renamed continuation. -/
theorem commit {compilation : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
    (layout : Layout compilation prepared)
    (snapshot : Snapshot compilation.checked registry functions prepared place environment actual heap store mapping world (ξ index))
    (bare : place.projections = [])
    {right updated : Dynamic.Value} {rightValue updatedValue : Value} {rhsHeap : Dynamic.Heap}
    {rhsStore : Store} {rhsMap : LocationMap} {rhsWorld : StoreTyping} {operator : Syntax.ValueAssignOp} {invalid : Word}
    (rhs : RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
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
      HeapRepresents compilation.checked registry functions rhsMap rhsWorld after finalStore ∧
      AdministrativePreserved mapping store rhsMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      RuntimeEnvironmentHasTypes rhsWorld
        (writtenEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue updatedValue updatedValue actual)
        (writtenContext prepared actualContext) ambient.definitions ∧
      ∀ next outputType, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (writtenEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue updatedValue updatedValue actual)
        finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨latest⟩ := rhs.latest
  obtain ⟨initial, initialValue⟩ := cell_initial latest.related
  have written := DataPlaceCommitReflection.source_writes latest.read updated
  obtain ⟨finalStore, coreWritten, finalHeaps, writeFrame⟩ :=
    rhs.heaps.write_initialized latest.reference latest.read (latest.type.symm ▸ replacement) written
  have trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment heap place id updated
        ⟨rhsHeap.cells.set snapshot.location.index {latest.cell with value := some updated}⟩ := by
    cases rhs.trace with
    | value right =>
      exact .intro (snapshot.resolves bare) right
        (.intro latest.read (latest.type.trans snapshot.type.symm) initialValue (.leaf applied) written)
  refine ⟨_, finalStore, trace, written, finalHeaps, rhs.frame.trans writeFrame, rhs.metadata.trans (.of_write written), ?_, ?_⟩
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
