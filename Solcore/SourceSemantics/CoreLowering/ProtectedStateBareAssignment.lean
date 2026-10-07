import Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBareAssignmentContracts

/-! Actual bare-assignment prefix endpoints retain the expression-produced state
and the real seven-slot continuation. Grades come from the existing Source and
Core derivations. Compatibility uses a constant proof witness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateBareAssignment
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleBareAssignment
open SourceCoreCompatibleDataPlaces DataPlaceExecution
open GenericExpressionMeaning (FaultRep)
open ProtectedStateTransition
universe u v

def unitProtocol : Protocol Unit where
  State _ := Unit
  records _ := ()
  Relates _ _ := True
  refl _ := trivial
  trans _ _ := trivial

def unitTransport : AdministrativeTransport unitProtocol where
  extend := fun {_} _ {_ _ _ _} _ _ _ _ => ()
  related := by intros; trivial
  records_eq := by intros; rfl

inductive ResultAt {Records : Type v} (protocol : Protocol.{u, v} Records) (size : Nat) (compilation : SourceCoreCompatibleDataPlaces.Context) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions} (functions : FunctionModel compilation.checked.catalog ambient)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (faults : FaultRep) (prepared : Prepared) (place : PlaceResolution) (operator : Syntax.ValueAssignOp)
    (scope : Scope) (canonical : Environment)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (rhs : ExpressionId) (actual : Environment) (actualContext : Core.Context) (ξ : Renaming)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (outputType : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap} {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program sourceSize context evidence source environment before place operator rhs reason after)
      (result : value = .inLeft outputType (.word token)) (represented : faults reason token)
      (heaps : HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (post : Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      ResultAt protocol size compilation registry functions program context evidence source faults prepared place operator scope canonical environment before store mapping world
        rhs actual actualContext ξ initial next outputType value finalStore
  | success {sourceSize remainingSize : Nat} {updated : Dynamic.Value} {updatedValue : Value} {after : Dynamic.Heap} {commitStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : SourceExecutionSize.SourcePlaceAssignment program sourceSize context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after)
      (represented : ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updated updatedValue prepared.route.rootType)
      (heaps : HeapRepresents compilation.checked registry functions finalMap finalWorld after commitStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap commitStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions)
      (bounded : remainingSize < size)
      (continuation : EvaluationSize remainingSize (slots ++ actual) commitStore (shift 7 (next.rename ξ)) value finalStore)
      (post : Transition protocol initial ⟨scope, finalMap, finalWorld, after, commitStore, canonical⟩) :
      ResultAt protocol size compilation registry functions program context evidence source faults prepared place operator scope canonical environment before store mapping world
        rhs actual actualContext ξ initial next outputType value finalStore


theorem ResultAt.forget {Records : Type v} {protocol : Protocol.{u, v} Records}
    {size : Nat} {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {faults : FaultRep} {prepared : Prepared} {place : PlaceResolution} {operator : Syntax.ValueAssignOp}
    {scope : Scope} {canonical : Environment} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    {store : Store} {mapping : LocationMap} {world : StoreTyping} {rhs : ExpressionId}
    {actual : Environment} {actualContext : Core.Context} {ξ : Renaming}
    {initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩}
    {next : Expr} {outputType : Ty} {value : Value} {finalStore : Store}
    (result : ResultAt protocol size compilation registry functions program context evidence source faults prepared place operator
      scope canonical environment before store mapping world rhs actual actualContext ξ initial next outputType value finalStore) :
    RecursiveNamedBareAssignmentContracts.ResultAt size compilation registry functions program context evidence source faults prepared place operator
      environment before store mapping world rhs actual actualContext ξ next outputType value finalStore := by
  cases result with
  | fault trace same represented heaps maps worlds frame metadata _ =>
    exact .fault trace same represented heaps maps worlds frame metadata
  | success trace represented heaps maps worlds frame metadata count typed bounded continuation _ =>
    exact .success trace represented heaps maps worlds frame metadata count typed bounded continuation

end Solcore.SourceSemantics.CoreLowering.ProtectedStateBareAssignment
