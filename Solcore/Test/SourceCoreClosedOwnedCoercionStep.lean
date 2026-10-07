import Solcore.Test.SourceCoreClosedOwnedMethodBootstrap
import Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSuffixMeaning

/-! A genuine selected Coerce method enters its actual saved slot. The original
builtin profile closes its parameters and body internally, retaining the real
returned pool. Native reflection keeps the original strict body child and
constructs a separate Source grade. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedCoercionStep
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodCaptureReceipts
open Tests.SourceCoreClosedOwnedMethodBootstrap (TypedCapture)
open Tests.SourceCoreClosedOwnedLexicalBody (reached_pool_observations)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (cached : CallablePreparedMethodSelection.Cached compiled method.specialized)
  (dictionary : Dynamic.EvidenceEnvironment)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profileFlag : compiled.compatible.checked.catalog.callableContracts = true)
  (bootstrap : TypedCapture (headers := headers) (keys := keys) (registry := registry) (faults := faults) cached dictionary profileFlag)
  (profile : Profile cached.compilation (.initial compiled.compatible.checked) (CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody (compiled := compiled) (method := method)) dictionary bootstrap.capture.administrative registry faults)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {step : CoercionStep} {call : CallableCoercionSpine.Call}

/-- Full raw edge, genuine selector/dictionary and actual cached slot association
are independent static receipts. Singleton arity follows the same binder row. -/
structure Selected where
  binder : TypedBinder
  signature : cached.named.signature = call.signature
  index : bootstrap.capture.installed.globalIndex = call.index
  bindings : cached.named.inputs = [(binder, call.signature.parameterType)]
  inputType : binder.scheme.body = step.source
  result : (sourceBody (compiled := compiled) (method := method)).resultType = step.target
  selector : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context evidence "Coerce" "coerce"
    step.requirements (sourceBody (compiled := compiled) (method := method)) dictionary

variable (selected : Selected (step := step) (call := call) (context := context) (evidence := evidence)
  cached dictionary profileFlag bootstrap)

/-- The original complete method row is assembled from these genuine receipts.
It is used only for the existing native completion inversion. -/
def method_row : CallablePreparedOperatorSuffixMeaning.Method compiled.indexed (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults
    (Program.ofChecked compiled.sourceProgram) context evidence := {
  step := step, call := call, named := cached.named, diagnostics := cached.diagnostics, code := cached.code
  compiled := cached.compilation, signature := selected.signature
  sourceBody := sourceBody (compiled := compiled) (method := method), dictionary := dictionary
  selected := selected.selector, administrative := bootstrap.capture.administrative, profile := profile
  input := selected.binder, bindings := selected.bindings, inputType := selected.inputType, result := selected.result }

include selected in
private theorem singleton_arguments {input : Dynamic.Value} {native : Value}
    (represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
      [] bootstrap.world step.source input native call.signature.parameterType) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
      [] bootstrap.world cached.named.inputs [input] [native] := by
  rw [selected.bindings]
  apply CallableIndexedParameterMeaning.Arguments.cons _ .nil
  change ValueRep _ _ _ _ _ selected.binder.scheme.body _ _ _
  simpa only [selected.inputType] using represented

/-- Source method grades are reconstructed separately from native budgets. -/
def StepOutcome (sourceSize : Nat) (input : Dynamic.Value) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  match outcome with
  | .value output => SourceExecutionSize.CoercionStepExecutes (Program.ofChecked compiled.sourceProgram)
      (SourceExecutionSize.stepSize [sourceSize]) context evidence ⟨[]⟩ step input output after
  | .fault reason => SourceExecutionSize.CoercionStepFaults (Program.ofChecked compiled.sourceProgram)
      (SourceExecutionSize.stepSize [sourceSize]) context evidence ⟨[]⟩ step input reason after

include selected in
private theorem step_of_body {sourceSize : Nat} {input : Dynamic.Value} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
      (sourceBody (compiled := compiled) (method := method)) dictionary ⟨[]⟩ [input] outcome after) :
    StepOutcome (compiled := compiled) (context := context) (evidence := evidence) (step := step) sourceSize input outcome after := by
  cases trace with
  | value trace => exact .method selected.selector trace
  | fault trace => exact .method selected.selector trace

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
  (escaped : faults .controlEscapedFunction cached.compilation.own.table.escapedReason)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (cached.diagnostics.reasonAt cached.named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((cached.diagnostics.reasonAt cached.named.signature.key id).add tag))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (physical : owner.key.frameLocation = 0)
  (initial : State headers keys ⟨[], [], bootstrap.world, ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
    RecursiveNamedCatalogPreparedInitialization.environment compiled⟩)

section Emitted
variable {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction} {available : SourceCompilationPlan.EvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
  {inputCode outputCode : SourceCoreBasic.LoweredExpr}
  (emission : CallableCoercionSpine.Step compiled.sourceProgram project compilation caller available scope node policy inputCode step outputCode call)
  (sameMethod : emission.method = method)

include profile selected extension faithful observations functionTypes escaped uninitialized missing physical emission sameMethod in
/-- A real Source method outcome enters the same observed global slot. The
closed builtin producer supplies the actual parameter/body/restoration pool. -/
theorem source_invoke {input : Dynamic.Value} {native : Value} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
      [] bootstrap.world step.source input native call.signature.parameterType)
    (trace : NamedCalls.BodyOutcome (Program.ofChecked compiled.sourceProgram)
      (sourceBody (compiled := compiled) (method := method)) dictionary ⟨[]⟩ [input] outcome after) (reason : Word) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      SourceCompilationPlan.checkedCoercionMethod compiled.sourceProgram caller node available step = .ok method ∧
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        (sourceBody (compiled := compiled) (method := method)) dictionary ⟨[]⟩ [input] outcome after ∧
      StepOutcome (compiled := compiled) (context := context) (evidence := evidence) (step := step) sourceSize input outcome after ∧
      CallableCoercionSpine.Invoke (RecursiveNamedCatalogPreparedInitialization.environment compiled) reason call
        (RecursiveNamedCatalogPreparedInitialization.store compiled) (.inRight .word native) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)) finalMap finalWorld
        step.target call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends bootstrap.world finalWorld ∧
      AdministrativePreserved [] (RecursiveNamedCatalogPreparedInitialization.store compiled) finalMap finalStore ∧
      Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
      ∃ reached : State headers keys ⟨[], finalMap, finalWorld, after, finalStore, RecursiveNamedCatalogPreparedInitialization.environment compiled⟩,
        Relates initial reached ∧ (∀ row, RecordPrefix (records initial row) (records reached row)) ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        (∀ row record, record ∈ records initial row → record ∈ records reached row) := by
  obtain ⟨sourceSize, actualTrace⟩ := RecursiveNamedCallBounds.BodyOutcome.has_size trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, frame, metadata, reached, poolRelated⟩ :=
    CallableIndexedOwnedMethodBuiltinBounds.invocation_preserves cached.compilation profile
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) extension faithful observations functionTypes
      escaped uninitialized missing bootstrap.capture.installed
      (singleton_arguments cached dictionary profileFlag bootstrap selected represented) owner initial
      (bootstrap.capture.frame_eq.trans physical.symm) bootstrap.heaps actualTrace
  have reference := bootstrap.capture.installed.globalReference
  rw [selected.index] at reference
  have invoked : CallableCoercionSpine.Invoke (RecursiveNamedCatalogPreparedInitialization.environment compiled) reason call
      (RecursiveNamedCatalogPreparedInitialization.store compiled) (.inRight .word native) value finalStore :=
    .applied reference bootstrap.capture.installed.globalRead evaluated
  have chosen : SourceCompilationPlan.checkedCoercionMethod compiled.sourceProgram caller node available step = .ok method := by
    simpa only [sameMethod] using emission.selectedMethod
  refine ⟨sourceSize, value, finalStore, finalMap, finalWorld, chosen, actualTrace,
    step_of_body cached dictionary profileFlag bootstrap selected actualTrace, invoked, ?_, heaps, maps, worlds, frame, metadata,
    reached, poolRelated, reached_pool_observations poolRelated⟩
  simpa only [selected.result, selected.signature] using related

include profile selected extension faithful observations functionTypes escaped uninitialized missing physical emission sameMethod in
/-- The real InvokeSized child remains strict in the native budget. Shared
reflection supplies an independent Source grade and the same restored pool. -/
theorem native_invoke {input : Dynamic.Value} {native value : Value} {budget : Nat} {reason : Word} {finalStore : Store}
    (represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
      [] bootstrap.world step.source input native call.signature.parameterType)
    (completed : CallableCoercionSpine.InvokeSized budget (RecursiveNamedCatalogPreparedInitialization.environment compiled) reason call
      (RecursiveNamedCatalogPreparedInitialization.store compiled) (.inRight .word native) value finalStore) :
    ∃ bodySize sourceSize outcome after finalMap finalWorld,
      SourceCompilationPlan.checkedCoercionMethod compiled.sourceProgram caller node available step = .ok method ∧
      bodySize < budget ∧ EvaluationSize bodySize (native :: bootstrap.capture.installed.captured)
        (RecursiveNamedCatalogPreparedInitialization.store compiled)
        (cached.compilation.output.rename bootstrap.capture.installed.embedding.lift) value finalStore ∧
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        (sourceBody (compiled := compiled) (method := method)) dictionary ⟨[]⟩ [input] outcome after ∧
      StepOutcome (compiled := compiled) (context := context) (evidence := evidence) (step := step) sourceSize input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)) finalMap finalWorld
        step.target call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends bootstrap.world finalWorld ∧
      AdministrativePreserved [] (RecursiveNamedCatalogPreparedInitialization.store compiled) finalMap finalStore ∧
      Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
      ∃ reached : State headers keys ⟨[], finalMap, finalWorld, after, finalStore, RecursiveNamedCatalogPreparedInitialization.environment compiled⟩,
        Relates initial reached ∧ (∀ row, RecordPrefix (records initial row) (records reached row)) ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        (∀ row record, record ∈ records initial row → record ∈ records reached row) := by
  let saved : CallablePreparedOperatorSuffixMeaning.Capture
      (method_row cached dictionary profileFlag bootstrap profile selected)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
      (RecursiveNamedCatalogPreparedInitialization.environment compiled) [] bootstrap.world ⟨[]⟩
      (RecursiveNamedCatalogPreparedInitialization.store compiled) :=
    ⟨bootstrap.capture.installed, selected.index⟩
  obtain ⟨bodySize, strict, evaluated⟩ := CallablePreparedOperatorSuffixMeaning.Capture.completed_sized
    (method := method_row cached dictionary profileFlag bootstrap profile selected)
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) saved completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, actualTrace, related, heaps, maps, worlds, frame, metadata, reached, poolRelated⟩ :=
    CallableIndexedOwnedMethodBuiltinBounds.invocation_reflects cached.compilation profile
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) extension faithful observations functionTypes
      escaped uninitialized missing bootstrap.capture.installed
      (singleton_arguments cached dictionary profileFlag bootstrap selected represented) owner initial
      (bootstrap.capture.frame_eq.trans physical.symm) bootstrap.heaps evaluated
  have chosen : SourceCompilationPlan.checkedCoercionMethod compiled.sourceProgram caller node available step = .ok method := by
    simpa only [sameMethod] using emission.selectedMethod
  refine ⟨bodySize, sourceSize, outcome, after, finalMap, finalWorld, chosen, strict, evaluated, actualTrace,
    step_of_body cached dictionary profileFlag bootstrap selected actualTrace, ?_, heaps, maps, worlds, frame, metadata,
    reached, poolRelated, reached_pool_observations poolRelated⟩
  simpa only [selected.result, selected.signature] using related
end Emitted
end Tests.SourceCoreClosedOwnedCoercionStep
