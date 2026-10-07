import Solcore.Test.SourceCoreClosedOwnedMethodBootstrap
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodNestedEntries

/-! A genuine method selector and typed bootstrap drive a real Boolean marked
parameter allocation. The actual parameter pool enters a principal packet with
its own complete Source seed. Native completion keeps its original strict child
and the same parameter post. No body meaning or lambda support is assumed. -/
set_option autoImplicit false
namespace Tests.SourceCoreOwnedMethodPrincipalParameters
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

include profile bindings binderType in
private theorem boolean_source_types :
    Dynamic.ValuesHaveTypes principal.sourceBody.context ⟨[]⟩ [.bool boolean] profile.types := by
  have rawTypes : profile.types = [.bool] := by
    rw [← Dynamic.MonoBindersExtend.bodyTypes_eq profile.extended, profile.parameters, bindings]
    simp only [List.map_cons, List.map_nil, binderType]
  rw [rawTypes]
  exact .cons (.bool boolean) .nil

include profile physical locations bindings binderType in
/-- The actual marked allocation supplies both original Source admission and
the selected row's own authenticated method seed at the same reached pool. -/
theorem boolean_source_packet
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ environment heap canonical store mapping world,
      Dynamic.BindersAllocate [] ⟨[]⟩ principal.sourceFunction.parameters
        [.bool boolean] environment heap ∧
      Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) profile.context principal.sourceBody.source ∧
      principal.dictionary.Covers profile.context ∧ Dynamic.HeapWellTyped profile.context heap ∧
      Dynamic.EnvironmentAgrees heap profile.context.locals environment ∧
      ∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named).State
        ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)), mapping, world, heap, store, canonical⟩,
        Relates initial reached.val ∧
        (CallableIndexedOwnedOriginCanonicalState.protocol owner principal.named).records reached = records reached.val ∧
        (∀ row record, record ∈ records reached.val row → CallableIndexedSnapshots.Holds
          compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame mapping store record) := by
  have arguments := boolean_arguments principal profileFlag bootstrap bindings binderType boolean
  have rawTyped := boolean_source_types principal profileFlag bootstrap profile bindings binderType boolean
  have sameFrame := bootstrap.capture.frame_eq.trans physical.symm
  obtain ⟨_origin, _index, _metadata, selected, history, _emitted, entry, added, length, spine, reached, related⟩ :=
    CallableIndexedOwnedMethodInvocationBounds.parameters_with_state principal.cached.compilation
      (CallablePreparedMethodCatalogHookMeaning.of_builtin principal.cached.compilation profile)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) bootstrap.capture.installed
      arguments owner initial sameFrame bootstrap.heaps
  have observed := CallableIndexedOwnedMethodCaptureReceipts.BootstrapCapture.globals_for_owner
    principal.cached principal.dictionary (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
    bootstrap.capture owner locations
  have packet := CallableIndexedOwnedMethodNestedEntries.source_packet principal
    (CallablePreparedMethodCatalogHookMeaning.of_builtin principal.cached.compilation profile)
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
    bootstrap.capture.installed owner observed selected history entry added length spine reached
  have emptyTyped : Dynamic.HeapWellTyped principal.sourceBody.context ⟨[]⟩ := by
    intro cell impossible; simp at impossible
  obtain ⟨runtime, covers, typed, locals, _facts, _finalContext, _bodyTyped, _completes⟩ :=
    CallableIndexedOwnedBodySourceAdmission.admission_at_selected_method_parameters profile.extended entry.allocation
      emptyTyped rawTyped wellFormed principal.selected bootstrap.capture.sourceFrame
  exact ⟨entry.environment, entry.heap, entry.canonical, entry.store, entry.mapping, entry.world,
    entry.allocation, runtime, covers, typed, locals, ⟨reached, packet⟩, related, rfl,
    fun row record member => record_snapshot reached row member⟩

include profile physical locations bindings binderType in
/-- Original native hook inversion retains its measured body child and real
parameter pool. The packet observes that pool's actual ghost and every record. -/
theorem boolean_native_packet {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues [Value.bool boolean] :: bootstrap.capture.installed.captured)
      (RecursiveNamedCatalogPreparedInitialization.store compiled)
      (principal.cached.compilation.output.rename bootstrap.capture.installed.embedding.lift) value finalStore) :
    ∃ prefixSize childSize environment heap canonical store mapping world actualBody embedding bodyStore,
      prefixSize < size ∧ childSize < prefixSize ∧
      EvaluationSize childSize actualBody store (principal.cached.compilation.body.rename embedding) value bodyStore ∧
      Dynamic.BindersAllocate [] ⟨[]⟩ principal.sourceFunction.parameters [.bool boolean] environment heap ∧
      finalStore = bodyStore.set owner.key.frameLocation
        (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame
          (initial.rows owner.position).authority.current) ∧
      ∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named).State
        ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)), mapping, world, heap, store, canonical⟩,
        Relates initial reached.val ∧
        (CallableIndexedOwnedOriginCanonicalState.protocol owner principal.named).records reached = records reached.val ∧
        (∀ row record, record ∈ records reached.val row → CallableIndexedSnapshots.Holds
          compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame mapping store record) := by
  have arguments := boolean_arguments principal profileFlag bootstrap bindings binderType boolean
  have sameFrame := bootstrap.capture.frame_eq.trans physical.symm
  obtain ⟨_origin, _index, _metadata, prefixSize, bodyStore, selected, history, strict, restored,
      entry, added, length, spine, reached, related⟩ :=
    CallableIndexedOwnedMethodInvocationBounds.body_prefix_with_state principal.cached.compilation
      (CallablePreparedMethodCatalogHookMeaning.of_builtin principal.cached.compilation profile)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) bootstrap.capture.installed
      arguments owner initial sameFrame bootstrap.heaps completed
  have observed := CallableIndexedOwnedMethodCaptureReceipts.BootstrapCapture.globals_for_owner
    principal.cached principal.dictionary (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
    bootstrap.capture owner locations
  have packet := CallableIndexedOwnedMethodNestedEntries.native_packet principal
    (CallablePreparedMethodCatalogHookMeaning.of_builtin principal.cached.compilation profile)
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
    bootstrap.capture.installed owner observed selected history entry added length spine reached
  have nonempty : principal.named.inputs ≠ [] := by rw [bindings]; simp
  exact ⟨prefixSize, entry.childSize, entry.environment, entry.heap, entry.canonical, entry.store, entry.mapping,
    entry.world, entry.actualBody, entry.embedding, bodyStore, strict, entry.strict nonempty, entry.completed,
    entry.allocation, restored, ⟨reached, packet⟩, related, rfl,
    fun row record member => record_snapshot reached row member⟩

end Tests.SourceCoreOwnedMethodPrincipalParameters
