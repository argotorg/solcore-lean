import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceAssignmentContracts

/-! One dynamic result for bare and projected assignment heads. Source costs
remain independent of the original Core continuation size. Real entry, heap,
and slot receipts are outputs of execution reflection, never static Head fields. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedAssignmentHeadContracts
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning

inductive ResultAt (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (faults : FunctionCalls.FaultRep) (entry : ProtectedExpressionMeaning.Entry) (scope : Scope) (writtenContext : Core.Context)
    (place : PlaceResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program sourceSize context evidence source environment before place operator rhs reason after)
      (same : value = .inLeft output (.word token)) (matched : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (installed : entry scope finalMap finalWorld after finalStore canonical) :
      ResultAt size checked registry functions program context evidence source faults entry scope writtenContext place operator rhs
        environment canonical actual before store mapping world next output value finalStore
  | success {sourceSize remainingSize : Nat} {updated : Dynamic.Value} {after : Dynamic.Heap}
      {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : SourceExecutionSize.SourcePlaceAssignment program sourceSize context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext ambient.definitions)
      (installed : entry scope finalMap finalWorld after written canonical)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (shift 7 next) value finalStore) :
      ResultAt size checked registry functions program context evidence source faults entry scope writtenContext place operator rhs
        environment canonical actual before store mapping world next output value finalStore

theorem ResultAt.erase {size : Nat} {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {faults : FunctionCalls.FaultRep} {entry : ProtectedExpressionMeaning.Entry} {scope : Scope} {writtenContext : Core.Context}
    {place : PlaceResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (result : ResultAt size checked registry functions program context evidence source faults entry scope writtenContext place operator rhs
      environment canonical actual before store mapping world next output value finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after ∧
      HeapRepresents checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext ambient.definitions ∧
      entry scope finalMap finalWorld after written canonical ∧
      Evaluates (slots ++ actual) written (shift 7 next) value finalStore) := by
  cases result with
  | fault trace same matched heaps maps worlds frame metadata installed =>
    exact .inl ⟨_, _, _, _, _, trace.sound, same, matched, heaps, maps, worlds, frame, metadata, installed⟩
  | success trace heaps maps worlds frame metadata count typed installed _ remaining =>
    exact .inr ⟨_, _, _, _, _, _, trace.sound, heaps, maps, worlds, frame, metadata, count, typed, installed, remaining.sound⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedAssignmentHeadContracts
