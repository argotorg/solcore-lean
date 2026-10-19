import Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedBitNotTail
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStagedProjectedBitNotAdmission
import Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatementHead

/-! Projected unary heads retain the actual key row, snapshot, write and reached caller.
The Unit temporary is administrative and has no Source RHS trace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)


inductive ResultAt (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (context : SourceSemantics.Context) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
    (faults : RecursiveStageMeaning.FaultRep) (scope : Scope) (writtenContext : Core.Context)
    (assignment : AssignmentResolution)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | keyFault {keySize : Nat} {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target)
      (trace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size checked registry functions context stages invocation faults scope writtenContext assignment
        environment canonical actual before store mapping world initial next output value finalStore
  | getterFault {keySize : Nat} {sources : List Dynamic.Value} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) after)
      (failed : Staging.Recursive.ProjectedTarget.GetterFault environment before after assignment.target sources reason)
      (same : value = .inLeft output (.word token)) (matched : faults (.semantic reason) token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size checked registry functions context stages invocation faults scope writtenContext assignment
        environment canonical actual before store mapping world initial next output value finalStore
  | success {keySize remainingSize : Nat} {target : Dynamic.ResolvedPlace}
      {updated : Dynamic.Value} {after : Dynamic.Heap}
      {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      {sources : List Dynamic.Value} {targetHeap : Dynamic.Heap}
      (keys : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) targetHeap)
      (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before targetHeap assignment.target sources target)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        targetHeap target updated after)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext ambient.definitions)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (related : callerProtocol.Relates initial reached) (admitted : Admission bridge context reached)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (shift 7 next) value finalStore) :
      ResultAt size checked registry functions context stages invocation faults scope writtenContext assignment
        environment canonical actual before store mapping world initial next output value finalStore

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads
