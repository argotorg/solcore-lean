import Solcore.Test.SourceCoreClosedOwnedMethodBootstrap
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalBuiltinBounds

/-! A genuine selected method and typed bootstrap drive a real Boolean argument
through the authentic principal packet body family and caller restoration.
Original builtin bodies close internally; all observations use the actual
returned pool and independent Source/native grades. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedMethodPrincipalBuiltin
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodPrincipal
open Tests.SourceCoreClosedOwnedMethodBootstrap

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : Principal compiled method)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profileFlag : compiled.compatible.checked.catalog.callableContracts = true)

/-- Whole preparation and the full method selector construct the native and
Source bootstrap together; the test requires no external initial heap law. -/
theorem typed_bootstrap {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (TypedCapture (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      principal.cached principal.dictionary profileFlag) :=
  typed_capture_of_selected principal.cached principal.dictionary profileFlag accepted principal.selected wellFormed

variable
  (bootstrap : TypedCapture (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    principal.cached principal.dictionary profileFlag)
  (profile : Profile principal.cached.compilation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody principal.dictionary
    bootstrap.capture.administrative registry faults)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (physical : owner.key.frameLocation = 0)
  (locations : ∀ header, header ∈ headers → owner.key.locations header =
    RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
  (initial : State headers keys ⟨[], [], bootstrap.world, ⟨[]⟩,
    RecursiveNamedCatalogPreparedInitialization.store compiled,
    RecursiveNamedCatalogPreparedInitialization.environment compiled⟩)
  {binder : TypedBinder}
  (bindings : principal.named.inputs = [(binder, .bool)])
  (binderType : binder.scheme.body = .bool)
  (boolean : Bool)

include bindings binderType in
private theorem boolean_arguments : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
    [] bootstrap.world principal.named.inputs [.bool boolean] [.bool boolean] := by
  rw [bindings]
  apply CallableIndexedParameterMeaning.Arguments.cons _ .nil
  change ValueRep compiled.compatible.checked registry
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
    [] bootstrap.world binder.scheme.body (.bool boolean) (.bool boolean) .bool
  rw [binderType]
  exact .bool boolean

variable
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
  (escaped : faults .controlEscapedFunction principal.cached.compilation.own.table.escapedReason)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location)
    (principal.cached.diagnostics.reasonAt principal.named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((principal.cached.diagnostics.reasonAt principal.named.signature.key id).add tag))

include profile physical locations bindings binderType extension faithful observations functionTypes escaped uninitialized missing in
/-- Actual Source method execution consumes a genuine Bool parameter and the
closed principal packet family. It restores the same reached body pool. -/
theorem boolean_source_post {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) size
      principal.sourceBody principal.dictionary ⟨[]⟩ [.bool boolean] outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues [Value.bool boolean] :: bootstrap.capture.installed.captured)
        (RecursiveNamedCatalogPreparedInitialization.store compiled)
        (principal.cached.compilation.output.rename bootstrap.capture.installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
        finalMap finalWorld principal.sourceBody.resultType principal.named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends bootstrap.world finalWorld ∧
      AdministrativePreserved [] (RecursiveNamedCatalogPreparedInitialization.store compiled) finalMap finalStore ∧
      Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
      ∃ reached : State headers keys ⟨[], finalMap, finalWorld, after, finalStore,
        RecursiveNamedCatalogPreparedInitialization.environment compiled⟩,
        Relates initial reached ∧
        (∀ row, RecordPrefix (records initial row) (records reached row)) ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        (∀ row record, record ∈ records initial row → record ∈ records reached row) := by
  have arguments := boolean_arguments principal profileFlag bootstrap bindings binderType boolean
  have observed := CallableIndexedOwnedMethodCaptureReceipts.BootstrapCapture.globals_for_owner
    principal.cached principal.dictionary (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
    bootstrap.capture owner locations
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedMethodPrincipalBuiltinBounds.invocation_preserves principal owner profile
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) extension faithful observations functionTypes
      escaped uninitialized missing bootstrap.capture.installed arguments initial observed
      (bootstrap.capture.frame_eq.trans physical.symm) bootstrap.heaps trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata,
    reached, related, Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related⟩

include profile physical locations bindings binderType extension faithful observations functionTypes escaped uninitialized missing in
/-- Whole native completion reflects through the actual authentic parameter
packet, closed builtin body and reached-pool restoration. Source grade is independent. -/
theorem boolean_native_post {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues [Value.bool boolean] :: bootstrap.capture.installed.captured)
      (RecursiveNamedCatalogPreparedInitialization.store compiled)
      (principal.cached.compilation.output.rename bootstrap.capture.installed.embedding.lift) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        principal.sourceBody principal.dictionary ⟨[]⟩ [.bool boolean] outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
        finalMap finalWorld principal.sourceBody.resultType principal.named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends bootstrap.world finalWorld ∧
      AdministrativePreserved [] (RecursiveNamedCatalogPreparedInitialization.store compiled) finalMap finalStore ∧
      Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
      ∃ reached : State headers keys ⟨[], finalMap, finalWorld, after, finalStore,
        RecursiveNamedCatalogPreparedInitialization.environment compiled⟩,
        Relates initial reached ∧
        (∀ row, RecordPrefix (records initial row) (records reached row)) ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        (∀ row record, record ∈ records initial row → record ∈ records reached row) := by
  have arguments := boolean_arguments principal profileFlag bootstrap bindings binderType boolean
  have observed := CallableIndexedOwnedMethodCaptureReceipts.BootstrapCapture.globals_for_owner
    principal.cached principal.dictionary (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
    bootstrap.capture owner locations
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedMethodPrincipalBuiltinBounds.invocation_reflects principal owner profile
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) extension faithful observations functionTypes
      escaped uninitialized missing bootstrap.capture.installed arguments initial observed
      (bootstrap.capture.frame_eq.trans physical.symm) bootstrap.heaps completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata,
    reached, related, Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related⟩

end Tests.SourceCoreClosedOwnedMethodPrincipalBuiltin
