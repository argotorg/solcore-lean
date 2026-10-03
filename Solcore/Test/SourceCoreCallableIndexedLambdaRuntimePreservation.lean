import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimePreservation
import Solcore.Test.SourceCoreCallableIndexedLambdaRuntimeBody

/-! The independent source success/fault consumers retain the full real heap
and caller catalog restored by the actual payload application. The source
allocation is matched to the generated prefix, without an old Entry identity.
The native regression reuses the seven actual builtin-body lambda cases. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaRuntimePreservation
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

abbrev actual_prefix_preserves := @CallableIndexedLambdaRuntimePreservation.entry_preserves
abbrev independent_call_preserves := @CallableIndexedLambdaRuntimePreservation.preserves

variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : SourceSemantics.Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : CallableIndexedLambdaRuntimeBody.Body code program registry faults)
  (profile : values.checked.catalog.callableContracts = true)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}

variable {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  {currentMetadata : Option MetadataState}
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include body extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in
theorem source_value_completes {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {payload : Dynamic.Value} {after : Dynamic.Heap}
    (executed : Dynamic.CallableApplies program callerContext callerEvidence function.evidence before
      (.closure function) arguments payload after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload (.inRight .word value) finalStore ∧
      (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile)).Represents
        finalMap finalWorld function.resultType payload value code.receipt.resultCore ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, related, rest⟩ :=
    CallableIndexedLambdaRuntimePreservation.preserves captured code history body profile extension uninitialized missing escaped
      initial sameFrame represented heaps locals reference read currentCarried allowed (.value executed)
  cases related with
  | value related => exact ⟨_, finalStore, finalMap, finalWorld, evaluated, related, rest⟩

include body extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in
theorem source_fault_completes {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (executed : Dynamic.CallableFaults program callerContext callerEvidence function.evidence before
      (.closure function) arguments reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload (.inLeft code.receipt.resultCore (.word token)) finalStore ∧
      faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, related, rest⟩ :=
    CallableIndexedLambdaRuntimePreservation.preserves captured code history body profile extension uninitialized missing escaped
      initial sameFrame represented heaps locals reference read currentCarried allowed (.fault executed)
  cases related with
  | fault related => exact ⟨_, finalStore, finalMap, finalWorld, evaluated, related, rest⟩

include represented in
/-- Empty native arity is linked to the actual ordered source parameters. -/
theorem empty_parameters (empty : nativeArguments = []) : function.parameters = [] := by
  have count : code.receipt.loweredParameters.length = 0 := by simpa [empty] using represented.length.2
  rw [CallableIndexedLambdaEntryPrefix.parameters code, List.eq_nil_of_length_eq_zero count]
  rfl

/-- Two independent allocations for the actual closure inputs give the same
source environment and full heap. No equality of native prefix receipts follows. -/
theorem actual_allocation
    (entry : CallableIndexedLambdaRuntimeBody.Entry captured code history body profile arguments nativeArguments before store location current currentGhost)
    {environment : Dynamic.Environment} {bound : Dynamic.Heap}
    (allocated : Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound) :
    entry.entry.environment = environment ∧ entry.entry.heap = bound :=
  FunctionCallBody.allocations_same entry.entry.allocation allocated

/-- Reuse the actual whole for/while/match/default/fault/empty-arity bodies. -/
def run : IO Unit := Tests.SourceCoreCallableIndexedLambdaRuntimeBody.run

end Tests.SourceCoreCallableIndexedLambdaRuntimePreservation
