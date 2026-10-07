import Solcore.SourceSemantics.CoreLowering.ProtectedStatePlaceAssignment
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceAssignmentContracts

/-! Actual key prefixes retain source measurements and the original strict
native continuation grade, together with their concrete reached state. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStatePlaceAssignmentContracts
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution
universe u v

inductive KeyResultAt {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records) (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (scope : SourceCoreLocalCell.Scope) (canonical : Environment)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩) (index : Nat)
    (rhs next : Expr) (outputType : Ty) (operator : Option BinaryOp) (bitNot : Bool) (invalid : Word)
    (result : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (sourceFault : SourceExecutionSize.SourcePlaceFaults program sourceSize context evidence source environment before place reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (post : ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      KeyResultAt protocol size checked registry functions program context evidence source faults prepared codes sourceTypes place environment
        coreEnvironment before store mapping world scope canonical initialState index rhs next outputType operator bitNot invalid result finalStore
  | keys {sourceSize remainingSize : Nat} {location : Dynamic.Location} {resolved : List Dynamic.EvaluatedProjection} {after : Dynamic.Heap}
      (lookup : Dynamic.Environment.LooksUp environment place.root location)
      (trace : SourceExecutionSize.SourceProjectionsEvaluate program sourceSize context evidence source environment before place.projections resolved after)
      (execution : CompatiblePlaceTargetKeys.Execution checked registry functions prepared place codes sourceTypes location resolved
        coreEnvironment before after store mapping world index)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (keysEnvironment prepared.route.rootType execution.target (packValues execution.values) coreEnvironment)
        execution.keyStore (CompatiblePlaceKeyReflection.remainder prepared (SourceCoreCalls.packArguments codes).type rhs next outputType operator bitNot invalid) result finalStore)
      (post : ProtectedStateTransition.Transition protocol initialState ⟨scope, execution.keyMap, execution.keyWorld, after, execution.keyStore, canonical⟩) :
      KeyResultAt protocol size checked registry functions program context evidence source faults prepared codes sourceTypes place environment
        coreEnvironment before store mapping world scope canonical initialState index rhs next outputType operator bitNot invalid result finalStore


theorem KeyResultAt.forget {Records : Type v} {protocol : ProtectedStateTransition.Protocol.{u, v} Records} {size : Nat} {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {faults : FaultRep}
    {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    {place : PlaceResolution} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩} {index : Nat}
    {rhs next : Expr} {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word}
    {result : Value} {finalStore : Store}
    (receipt : KeyResultAt protocol size checked registry functions program context evidence source faults prepared codes sourceTypes place environment
        coreEnvironment before store mapping world scope canonical initialState index rhs next outputType operator bitNot invalid result finalStore) :
    RecursiveNamedPlaceAssignmentContracts.KeyResultAt size checked registry functions program context evidence source faults prepared codes sourceTypes place environment
        coreEnvironment before store mapping world index rhs next outputType operator bitNot invalid result finalStore := by
  cases receipt with
  | fault trace same represented heaps maps worlds frame metadata _ =>
    exact .fault trace same represented heaps maps worlds frame metadata
  | keys lookup trace execution bounded remaining _ =>
    exact .keys lookup trace execution bounded remaining
end Solcore.SourceSemantics.CoreLowering.ProtectedStatePlaceAssignmentContracts
