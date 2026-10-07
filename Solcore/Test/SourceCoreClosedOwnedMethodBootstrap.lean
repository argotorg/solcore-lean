import Solcore.Test.SourceCoreClosedOwnedLexicalBody
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodCaptureReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodySourceAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodBuiltinBounds

/-! Genuine selected methods consume the same actual typed bootstrap capture,
raw Source admission and closed builtin profile. Every parameter/body post and
caller restoration retains its actual reached pool. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedMethodBootstrap
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodCaptureReceipts
open Tests.SourceCoreClosedOwnedLexicalBody (reached_pool_observations)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (cached : CallablePreparedMethodSelection.Cached compiled method.specialized)
  (dictionary : Dynamic.EvidenceEnvironment)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profileFlag : compiled.compatible.checked.catalog.callableContracts = true)

/-- Complete typed capture from the actual factory, including the whole store.
The Source heap is empty; native administrative closures remain fully typed. -/
structure TypedCapture where
  world : StoreTyping
  typed : RuntimeStoreHasTypes world (RecursiveNamedCatalogPreparedInitialization.store compiled) compiled.indexed.layouts.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) [] world ⟨[]⟩
    (RecursiveNamedCatalogPreparedInitialization.store compiled)
  capture : BootstrapCapture cached dictionary (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) world

/-- The genuine Source selector and actual preparation construct every field;
no native capture, initial heap relation or execution law is assumed. -/
theorem typed_capture_of_selected {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context caller traitName methodName
      requirements (sourceBody (compiled := compiled) (method := method)) dictionary)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (TypedCapture (headers := headers) (keys := keys) (registry := registry) (faults := faults) cached dictionary profileFlag) := by
  obtain ⟨world, typed, heaps, ⟨capture⟩⟩ := of_selected_with_heap cached dictionary
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) accepted selected wellFormed
  exact ⟨⟨world, typed, heaps, capture⟩⟩

section Invocation
variable (bootstrap : TypedCapture (headers := headers) (keys := keys) (registry := registry) (faults := faults) cached dictionary profileFlag)
  (profile : Profile cached.compilation (.initial compiled.compatible.checked) (CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody (compiled := compiled) (method := method)) dictionary bootstrap.capture.administrative registry faults)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
    [] bootstrap.world cached.named.inputs arguments payloads)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (physical : owner.key.frameLocation = 0)
  (initial : State headers keys ⟨[], [], bootstrap.world, ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
    RecursiveNamedCatalogPreparedInitialization.environment compiled⟩)
  {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
  {traitName methodName : String} {requirements : List RequirementId}
  (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) callerContext callerEvidence traitName methodName
    requirements (sourceBody (compiled := compiled) (method := method)) dictionary)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

include profile represented physical selected wellFormed in
/-- The real marked parameter producer's own allocation drives original full
Source admission. The reached heap, environments and pool are the same witness. -/
theorem selected_parameter_admission
    (rawTyped : Dynamic.ValuesHaveTypes (sourceBody (compiled := compiled) (method := method)).context ⟨[]⟩ arguments profile.types) :
    ∃ environment heap canonical store mapping world,
      Dynamic.BindersAllocate [] ⟨[]⟩ (methodFunction cached.compilation (sourceBody (compiled := compiled) (method := method)) dictionary).parameters
        arguments environment heap ∧
      Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) profile.context
        (sourceBody (compiled := compiled) (method := method)).source ∧ dictionary.Covers profile.context ∧
      Dynamic.HeapWellTyped profile.context heap ∧ Dynamic.EnvironmentAgrees heap profile.context.locals environment ∧
      (∃ facts finalContext,
        StatementsHaveType (sourceBody (compiled := compiled) (method := method)).source
          { returnType := (sourceBody (compiled := compiled) (method := method)).resultType } profile.context
          cached.compilation.statements finalContext facts ∧
        BodyCompletes (sourceBody (compiled := compiled) (method := method)).resultType facts) ∧
      ∃ reached : State headers keys ⟨cached.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
        mapping, world, heap, store, canonical⟩,
        Relates initial reached ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame mapping store record) := by
  have sameFrame := bootstrap.capture.frame_eq.trans physical.symm
  obtain ⟨_origin, _index, _metadata, _owned, _history, _emitted, entry, _added, _length, _spine, reached, related⟩ :=
    CallableIndexedOwnedMethodInvocationBounds.parameters_with_state cached.compilation
      (CallablePreparedMethodCatalogHookMeaning.of_builtin cached.compilation profile)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) bootstrap.capture.installed
      represented owner initial sameFrame bootstrap.heaps
  have emptyTyped : Dynamic.HeapWellTyped (sourceBody (compiled := compiled) (method := method)).context ⟨[]⟩ := by
    intro cell impossible; simp at impossible
  obtain ⟨runtime, covers, typed, locals, facts, finalContext, bodyTyped, completes⟩ :=
    CallableIndexedOwnedBodySourceAdmission.admission_at_selected_method_parameters profile.extended entry.allocation
      emptyTyped rawTyped wellFormed selected bootstrap.capture.sourceFrame
  exact ⟨entry.environment, entry.heap, entry.canonical, entry.store, entry.mapping, entry.world,
    entry.allocation, runtime, covers, typed, locals, ⟨facts, finalContext, bodyTyped, completes⟩,
    reached, related, fun row record member => record_snapshot reached row member⟩

include profile physical selected wellFormed in
/-- A genuine one-Boolean method signature supplies raw and native arguments
internally. Its actual parameter producer creates the one Source cell, while
all record observations come from that same actual reached pool. -/
theorem boolean_parameter_admission {binder : TypedBinder} (boolean : Bool)
    (bindings : cached.named.inputs = [(binder, .bool)]) (binderType : binder.scheme.body = .bool) :
    ∃ canonical store mapping world,
      Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) profile.context
        (sourceBody (compiled := compiled) (method := method)).source ∧ dictionary.Covers profile.context ∧
      Dynamic.HeapWellTyped profile.context ⟨[⟨.bool, some (.bool boolean), none⟩]⟩ ∧
      ∃ reached : State headers keys ⟨cached.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
        mapping, world, ⟨[⟨.bool, some (.bool boolean), none⟩]⟩, store, canonical⟩,
        Relates initial reached ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame mapping store record) := by
  have arguments : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
      [] bootstrap.world cached.named.inputs [.bool boolean] [.bool boolean] := by
    rw [bindings]
    apply CallableIndexedParameterMeaning.Arguments.cons _ .nil
    change ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
      [] bootstrap.world binder.scheme.body (.bool boolean) (.bool boolean) .bool
    rw [binderType]
    exact .bool boolean
  have parameters : (methodFunction cached.compilation (sourceBody (compiled := compiled) (method := method)) dictionary).parameters = [binder] := by
    change (sourceBody (compiled := compiled) (method := method)).source.inputs = [binder]
    simpa only [bindings, List.map_cons, List.map_nil] using profile.parameters
  have rawTypes : profile.types = [.bool] := by
    rw [← Dynamic.MonoBindersExtend.bodyTypes_eq profile.extended, profile.parameters, bindings]
    simp only [List.map_cons, List.map_nil, binderType]
  have rawTyped : Dynamic.ValuesHaveTypes (sourceBody (compiled := compiled) (method := method)).context ⟨[]⟩
      [.bool boolean] profile.types := by
    rw [rawTypes]
    exact .cons (.bool boolean) .nil
  obtain ⟨environment, heap, canonical, store, mapping, world, allocated, runtime, covers, typed, _locals, _body, reached, related, snapshots⟩ :=
    selected_parameter_admission cached dictionary profileFlag bootstrap profile arguments owner physical initial selected wellFormed rawTyped
  have actualHeap : heap = ⟨[⟨.bool, some (.bool boolean), none⟩]⟩ := by
    rw [parameters] at allocated
    cases allocated with
    | cons head tail =>
      cases tail with
      | nil =>
        cases head
        simp only [binderType, List.nil_append]
  subst heap
  exact ⟨canonical, store, mapping, world, runtime, covers, typed, reached, related, snapshots⟩

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
  (escaped : faults .controlEscapedFunction cached.compilation.own.table.escapedReason)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location)
    (cached.diagnostics.reasonAt cached.named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((cached.diagnostics.reasonAt cached.named.signature.key id).add tag))

include profile represented physical extension faithful observations functionTypes escaped uninitialized missing in
/-- This Source method invocation uses the genuine bootstrap and internally
closed builtin body family; its actual reached pool supplies restoration. -/
theorem selected_source_post {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) size
      (sourceBody (compiled := compiled) (method := method)) dictionary ⟨[]⟩ arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: bootstrap.capture.installed.captured)
        (RecursiveNamedCatalogPreparedInitialization.store compiled)
        (cached.compilation.output.rename bootstrap.capture.installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
        finalMap finalWorld (sourceBody (compiled := compiled) (method := method)).resultType cached.named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends bootstrap.world finalWorld ∧
      AdministrativePreserved [] (RecursiveNamedCatalogPreparedInitialization.store compiled) finalMap finalStore ∧
      Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
      ∃ reached : State headers keys ⟨[], finalMap, finalWorld, after, finalStore, RecursiveNamedCatalogPreparedInitialization.environment compiled⟩,
        Relates initial reached ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame finalMap finalStore record) := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedMethodBuiltinBounds.invocation_preserves cached.compilation profile
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) extension faithful observations functionTypes
      escaped uninitialized missing bootstrap.capture.installed represented owner initial
      (bootstrap.capture.frame_eq.trans physical.symm) bootstrap.heaps trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata,
    reached, related, fun row record member => record_snapshot reached row member⟩

include profile represented physical extension faithful observations functionTypes escaped uninitialized missing in
/-- Original whole hook completion reconstructs its independent Source grade
and retains the exact restored pool with every reached snapshot authenticated. -/
theorem selected_native_post {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: bootstrap.capture.installed.captured)
      (RecursiveNamedCatalogPreparedInitialization.store compiled)
      (cached.compilation.output.rename bootstrap.capture.installed.embedding.lift) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        (sourceBody (compiled := compiled) (method := method)) dictionary ⟨[]⟩ arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
        finalMap finalWorld (sourceBody (compiled := compiled) (method := method)).resultType cached.named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends bootstrap.world finalWorld ∧
      AdministrativePreserved [] (RecursiveNamedCatalogPreparedInitialization.store compiled) finalMap finalStore ∧
      Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
      ∃ reached : State headers keys ⟨[], finalMap, finalWorld, after, finalStore, RecursiveNamedCatalogPreparedInitialization.environment compiled⟩,
        Relates initial reached ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame finalMap finalStore record) := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, original, represented, heaps, maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedMethodBuiltinBounds.invocation_reflects cached.compilation profile
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) extension faithful observations functionTypes
      escaped uninitialized missing bootstrap.capture.installed represented owner initial
      (bootstrap.capture.frame_eq.trans physical.symm) bootstrap.heaps completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, original, represented, heaps, maps, worlds, frame, metadata,
    reached, related, fun row record member => record_snapshot reached row member⟩
end Invocation
end Tests.SourceCoreClosedOwnedMethodBootstrap
