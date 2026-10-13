import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionSourceArguments
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodInvocationBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodPhysicalCaptures
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredArgumentAlignment
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableCoercionSpineEvaluation

/-! Each actual conversion call uses the shared marked method entry engine.
The saved native closure is identified by the reached full physical cache;
independent Source selection supplies its body and complete dictionary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedStagedCoercionAuthority (Port)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {sourceCaller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {input output : SourceCoreBasic.LoweredExpr} {coercion : SourceInference.CoercionStep}
  {call : CallableCoercionSpine.Call}
  (step : CallableCoercionSpine.Step compiled.sourceProgram project compilation sourceCaller available
    scope node policy input coercion output call)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {stages : Staging.Recursive.Registry}
  (port : Port step context invocation.evidence stages)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} (faults : RecursiveStageMeaning.FaultRep)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

/-- A strict Source body callback at an authentic reached argument state. -/
def SourceBodies (budget : Nat) : Prop :=
  ∀ {mapping world heap store callerScope canonical administrative arguments payloads}
    (caller : State headers keys ⟨callerScope, mapping, world, heap, store, canonical⟩)
    (installed : CallablePreparedMethodRuntimeMeaning.Installed port.principal.cached.compilation
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := port.principal.sourceBody) (administrative := administrative)
      functions mapping world heap store canonical),
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs arguments payloads →
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap →
    Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments port.sourceAt.types →
    CallableIndexedOwnedIndirectExpressionHeads.StableRows caller →
    ∀ {child}, stages.Closure port.principal.sourceFunction child →
    SelectedCompilationMethodInvocationBounds.SourceContinuation
      (program := Program.ofChecked compiled.sourceProgram) (registry := receiving)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) (faults := faults)
      port.principal.cached.compilation port.sourceAt functions installed budget

/-- The native counterpart uses the same independently typed argument heap. -/
def NativeBodies (budget : Nat) : Prop :=
  ∀ {mapping world heap store callerScope canonical administrative arguments payloads}
    (caller : State headers keys ⟨callerScope, mapping, world, heap, store, canonical⟩)
    (installed : CallablePreparedMethodRuntimeMeaning.Installed port.principal.cached.compilation
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := port.principal.sourceBody) (administrative := administrative)
      functions mapping world heap store canonical),
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs arguments payloads →
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap →
    Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments port.sourceAt.types →
    CallableIndexedOwnedIndirectExpressionHeads.StableRows caller →
    ∀ {child}, stages.Closure port.principal.sourceFunction child →
    SelectedCompilationMethodInvocationBounds.NativeContinuation
      (program := Program.ofChecked compiled.sourceProgram) (registry := receiving)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) (faults := faults)
      port.principal.cached.compilation port.sourceAt functions installed budget

theorem represented_arguments {mapping : LocationMap} {world : StoreTyping}
    {source : Dynamic.Value} {value : Value}
    (represented : ValueRep compiled.compatible.checked receiving functions mapping world
      coercion.source source value call.signature.parameterType) :
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs [source] [value] := by
  have row : DataExpressionSequence.Values model mapping world [coercion.source]
      [call.signature.parameterType] [source] [value] := .cons represented .nil
  apply CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles port.principal.named.inputs row
  · have lengths := congrArg List.length port.parameters
    simpa only [List.length_map, List.length_cons, List.length_nil] using lengths.symm
  · rw [port.parameters]
  · change call.signature.parameterType = _
    rw [← port.signature]
    exact port.sourceAt.parameterType

/-- Reached Source input typing is transported by the selected method's genuine
closed body certificate, keeping its complete dictionary and raw singleton row. -/
theorem source_arguments {source : TypedSource}
    (certified : ∃ facts, Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
    port.principal.sourceBody port.sourceAt.types port.sourceAt.context facts)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    {heap : Dynamic.Heap} {value : Dynamic.Value}
    (heapTyped : Dynamic.HeapWellTyped context heap)
    (valueTyped : Dynamic.ValueHasType context heap value coercion.source) :
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap ∧
      Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap [value] port.sourceAt.types := by
  obtain ⟨facts, certificate⟩ := certified
  have signatures := certificate.signatures_eq.trans runtime.signatures.symm
  have bodyHeap := heapTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have bodyValue := valueTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have bodyArguments := Dynamic.ValuesHaveTypes.cons bodyValue Dynamic.ValuesHaveTypes.nil
  have row := port.sourceAt.extended.bodyTypes_eq
  rw [port.sourceAt.parameters, List.map_map] at row
  change port.principal.named.inputs.map (fun binding => binding.1.scheme.body) = port.sourceAt.types at row
  rw [port.parameters] at row
  exact ⟨port.principal.source_frame.context.symm ▸ bodyHeap,
    port.principal.source_frame.context.symm ▸ (row ▸ bodyArguments)⟩

theorem result_at_value {source : TypedSource}
    (certified : ∃ facts, Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
      port.principal.sourceBody port.sourceAt.types port.sourceAt.context facts)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    {before after : Dynamic.Heap} {value : Dynamic.Value}
    (preserved : Dynamic.ExpressionEvaluationPreserved port.principal.sourceBody.context
      before after value coercion.target) :
    Dynamic.ExpressionEvaluationPreserved context before after value coercion.target := by
  obtain ⟨facts, certificate⟩ := certified
  have signatures := runtime.signatures.trans certificate.signatures_eq.symm
  exact ⟨preserved.value_typed.transportClosed signatures
      certificate.type_parameters_empty runtime.closed
      certificate.type_variables_empty runtime.residual_variables_open,
    preserved.heap_typed.transportClosed signatures
      certificate.type_parameters_empty runtime.closed
      certificate.type_variables_empty runtime.residual_variables_open,
    preserved.heap_extends⟩

private theorem capture_read {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap}
    {store : Store} {canonical : Environment}
    (capture : CallableIndexedOwnedMethodPhysicalCaptures.Capture port.principal.cached port.principal.dictionary
      functions mapping world heap store canonical)
    (authority : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store) :
    store.read? (CallableIndexedOwnedPhysicalGlobals.location compiled port.principal.cached.index) = some (.inRight .unit
      (.closure port.principal.named.signature.parameterType (LanguageResult.resultType port.principal.named.signature.resultType)
        (port.principal.cached.compilation.output.rename capture.installed.embedding.lift) capture.installed.captured)) := by
  have cachedCode : compiled.indexed.secondPass.closures[port.principal.cached.index]? = some
      (.lambda port.principal.named.signature.parameterType (LanguageResult.resultType port.principal.named.signature.resultType)
        port.principal.cached.compilation.output) := by
    simpa only [port.principal.cached.compilation.emitted] using port.principal.cached.cached
  simpa only [capture.embedding_eq, capture.captured_eq] using (authority.cached cachedCode).2

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {ξ : Renaming}
  (pool : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (ownerFrame : owner.key.frameLocation = 0)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled compilation.administrativePrefix scope canonical)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
  {source : Dynamic.Value} {value : Value}
  (represented : ValueRep compiled.compatible.checked receiving functions mapping world coercion.source source value call.signature.parameterType)
  (headerHeap : Dynamic.HeapWellTyped port.principal.sourceFunction.context before)
  (headerArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context before [source] port.sourceAt.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows pool)
  (certified : ∃ facts, Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
    port.principal.sourceBody port.sourceAt.types port.sourceAt.context facts)

include ownerFrame physical slots agrees heaps represented headerHeap headerArguments stable certified in
theorem preserves (budget : Nat)
    (bodyMeaning : SourceBodies (headers := headers) (receiving := receiving) step port owner functions faults budget)
    (ledger : context.solvedRequirements = sourceCaller.function.solvedRequirements)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.CoercionStep (Program.ofChecked compiled.sourceProgram) stages size
      invocation context before coercion source outcome after)
    (within : size ≤ budget) :
    ∃ result finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke actual compilation.internalReason (call.rename ξ) store (.inRight .word value) result finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld coercion.target call.signature.resultType faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) pool
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      ∀ value, outcome = .value value →
        Dynamic.ExpressionEvaluationPreserved port.principal.sourceBody.context before after value coercion.target := by
  obtain ⟨bodySize, bodyEnvironment, bound, finalContext, bodyOutcome, child, selected, allocated, bodyTrace, matched, strict⟩ :=
    CallableIndexedOwnedPreparedStagedCoercionSourceArguments.body step port ledger trace
  have parameters := represented_arguments step port functions represented
  obtain ⟨capture⟩ := SelectedCompilationMethodPhysicalCaptures.of_certificate
    port.principal.cached port.principal.dictionary functions owner pool ownerFrame
    physical heaps.runtime_hasTypes slots port.selected (by obtain ⟨facts, typed⟩ := certified; exact ⟨_, _, facts, typed⟩)
  have capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] capture.installed.canonical := by
    rw [capture.canonical_eq]
    exact CallableIndexedOwnedPhysicalGlobals.environment_slots compiled
  obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, resultRep, finalHeaps, maps, worlds, frame, metadata, finalState, preserved⟩ :=
    SelectedCompilationMethodInvocationBounds.preserves
      port.principal.cached.compilation port.sourceAt functions capture.installed parameters owner pool
      (capture.frame_eq.trans ownerFrame.symm) heaps physical capturedSlots budget
      (bodyMeaning pool capture.installed parameters headerHeap headerArguments stable selected)
      allocated bodyTrace matched (Nat.lt_of_lt_of_le strict within)
  have reference := agrees (slots _ _ (CallableIndexedPreparedInventories.cached_global_at compiled port.principal.cached.selected))
  have read := capture_read step port functions capture physical
  refine ⟨result, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, metadata, finalState, ?_⟩
  · apply CallableCoercionSpine.Invoke.applied (location := CallableIndexedOwnedPhysicalGlobals.location compiled port.principal.cached.index)
      (body := port.principal.cached.compilation.output.rename capture.installed.embedding.lift)
      (captured := capture.installed.captured)
    · simpa only [CallableCoercionSpine.Call.rename, step.location, ← port.slot] using reference
    · exact read
    · simpa only [DataPatternValues.packValues] using evaluated
  · simpa only [port.result, port.signature] using resultRep
  · intro value same
    simpa only [port.result] using preserved value same

include ownerFrame physical slots agrees heaps represented headerHeap headerArguments stable certified in
theorem reflects (budget : Nat)
    (bodyMeaning : NativeBodies (headers := headers) (receiving := receiving) step port owner functions faults budget)
    {result : Value} {finalStore : Store}
    (completed : CallableCoercionSpine.InvokeSized budget actual compilation.internalReason (call.rename ξ)
      store (.inRight .word value) result finalStore) :
    ∃ size outcome after finalMap finalWorld,
      Staging.Recursive.Size.CoercionStep (Program.ofChecked compiled.sourceProgram) stages size
        invocation context before coercion source outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld coercion.target call.signature.resultType faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) pool
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      ∀ value, outcome = .value value →
        Dynamic.ExpressionEvaluationPreserved port.principal.sourceBody.context before after value coercion.target := by
  have parameters := represented_arguments step port functions represented
  obtain ⟨capture⟩ := SelectedCompilationMethodPhysicalCaptures.of_certificate
    port.principal.cached port.principal.dictionary functions owner pool ownerFrame
    physical heaps.runtime_hasTypes slots port.selected (by obtain ⟨facts, typed⟩ := certified; exact ⟨_, _, facts, typed⟩)
  have capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] capture.installed.canonical := by
    rw [capture.canonical_eq]
    exact CallableIndexedOwnedPhysicalGlobals.environment_slots compiled
  have reference := agrees (slots _ _ (CallableIndexedPreparedInventories.cached_global_at compiled port.principal.cached.selected))
  have referenceAt : actual[(call.rename ξ).index]? = some
      (.cellRef (OptionalCell.cellType port.principal.named.signature.functionType)
        (CallableIndexedOwnedPhysicalGlobals.location compiled port.principal.cached.index)) := by
    simpa only [CallableCoercionSpine.Call.rename, step.location, ← port.slot] using reference
  have read := capture_read step port functions capture physical
  cases completed with
  | absent reference actualRead =>
      cases Option.some.inj (reference.symm.trans referenceAt)
      cases Option.some.inj (actualRead.symm.trans read)
  | applied reference actualRead evaluation smaller =>
      cases Option.some.inj (reference.symm.trans referenceAt)
      cases Option.some.inj (actualRead.symm.trans read)
      obtain ⟨bodySize, bodyEnvironment, bound, finalContext, bodyOutcome, outcome, after, finalMap, finalWorld,
          allocated, bodyTrace, matched, resultRep, finalHeaps, maps, worlds, frame, metadata, finalState, preserved⟩ :=
        SelectedCompilationMethodInvocationBounds.reflects
          port.principal.cached.compilation port.sourceAt functions capture.installed parameters owner pool
          (capture.frame_eq.trans ownerFrame.symm) heaps physical capturedSlots budget
          (bodyMeaning pool capture.installed parameters headerHeap headerArguments stable port.staged)
          (by simpa only [DataPatternValues.packValues] using evaluation) (Nat.le_of_lt smaller)
      obtain ⟨size, trace⟩ := CallableIndexedOwnedPreparedStagedCoercionSourceArguments.applied step port
        port.staged allocated bodyTrace matched
      refine ⟨size, outcome, after, finalMap, finalWorld, trace,
        by simpa only [port.result, port.signature] using resultRep,
        finalHeaps, maps, worlds, frame, metadata, finalState, ?_⟩
      intro value same
      simpa only [port.result] using preserved value same

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionInvocationBounds
