import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedInvocationLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionRegistryScalarForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionInitial
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSourceCallOutcomes

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicInputLifting
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open RecursiveNamedPublicPhysicalSessionState
open SelectedCompilationPhysicalProgramSupport (stagePrepared stages Support)
open SelectedCompilationStageBodyLiftBounds (NamedLiftsBelow)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

/-- An independent ordinary application uses the original named row and full
caller and invocation dictionaries. Its final heap is part of the judgment. -/
def PlainCall (anchor header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function, NamedSourceAt header rawD function ∧
    FunctionCallBody.Outcome (Program.ofChecked compiled.sourceProgram) anchor.function.context
      invocation.evidence function.evidence before (.global function) arguments outcome after

theorem plain_value {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {invocation : Staging.Recursive.Scope} {before after : Dynamic.Heap}
    {arguments : List Dynamic.Value} {value : Dynamic.Value}
    (trace : PlainValue anchor header invocation before arguments value after) :
    PlainCall anchor header invocation before arguments (.value value) after := by
  obtain ⟨rawD, function, retained, applied⟩ := trace
  exact ⟨rawD, function, retained, .value applied⟩

theorem plain_fault {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {invocation : Staging.Recursive.Scope} {before after : Dynamic.Heap}
    {arguments : List Dynamic.Value} {reason : Dynamic.SemanticFault}
    (trace : PlainFault anchor header invocation before arguments reason after) :
    PlainCall anchor header invocation before arguments (.fault reason) after := by
  obtain ⟨rawD, function, retained, applied⟩ := trace
  exact ⟨rawD, function, retained, .fault applied⟩

/-- Internal selected-body port. The closed root family supplies this port;
public callers supply only their original Source trace and actual input receipts. -/
def NamedBodies (support : Support compiled (headers rows) (keys compiled) initial) : Prop :=
  ∀ (receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed),
    CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
      receiving.result.context.registry receiving.result.extension receiving.result.diagnostics →
    SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry →
    ∀ (header : Header compiled (Program.ofChecked compiled.sourceProgram)), header ∈ headers rows →
    ∀ budget {child : Staging.Recursive.Scope}, (stages compiled).Closure header.function child →
      NamedLiftsBelow (headers := headers rows) (keys := keys compiled) header
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving.result.context.registry
          (SelectedCompilationPhysicalProgramSupport.functions support)) (stages compiled) child budget

/-- Actual startup and retained history derive all argument, heap and capture
preconditions at the input registry before lifting the ordinary application. -/
theorem lift_call_at_input_registry (support : Support compiled (headers rows) (keys compiled) initial)
    (bodies : NamedBodies support)
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : StartedCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputReceipts : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {plain : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : PlainCall anchor request.header invocation state.heap arguments plain after) :
    ∃ staged reached, SourceCall anchor request.header invocation state.heap arguments staged reached ∧
      Staging.Recursive.Lifting.Adapted plain after staged reached := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨receiving, contextAt, issued, extension, history⟩ := state.at_named_request prepared request
  have registry : request.encodedValues.registry = receiving.result.context.registry :=
    (congrArg SourceCoreCompatibleValues.Context.registry contextAt).symm
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicClosureHistory.History.current_arguments
      (profile := profile) (bodyTyping := support.bodyTyping) (prepared := prepared)
      (selected := request.selected) (history := history) (started := request.started)
      (inputReceipts := inputReceipts) (metadata := metadata)
  obtain ⟨rawD, function, sourceAt, plainTrace⟩ := trace
  obtain ⟨size, measured⟩ := RecursiveNamedCallBounds.CallOutcome.has_size plainTrace
  let packet := support.bodies request.header request.selected.member
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt packet.prepared packet.aligned
    request.selected.member (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
    history.physical heaps.runtime_hasTypes
  obtain ⟨descriptor⟩ := SelectedCompilationCertifiedPublicSession.header_descriptor request.header
  obtain ⟨sidecar, _issued, _same, globalSelected, _declaration, _local, _evidence, _return, _analysis⟩ :=
    CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected
      sourceAt packet.prepared packet.aligned (stagePrepared recipe.compiled) descriptor
  have selected : (stages recipe.compiled).Closure request.header.function
      (RecursiveStageRegistry.scope sidecar [] request.header.function) := by
    rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] at globalSelected
    exact globalSelected
  obtain ⟨staged, reached, lifted, adapted⟩ :=
    SelectedCompilationStageNamedInvocationLifting.lifts_invocation
      (functions := functions rows initial profile) (registry := receiving.result.context.registry)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (caller := state.caller) (header := request.header) (physicalCapture := capture) (sourceAt := sourceAt)
      packet.layouts history.physical request.selected.member support.bodyTyping.function_ids
      (support.certificates request.header request.selected.member) stable heapTyped argumentsTyped represented heaps
      selected size (bodies receiving issued extension request.header request.selected.member size selected)
      measured (Nat.le_refl _)
  obtain ⟨stagedSize, stagedTrace⟩ := Staging.Recursive.Size.Applies.of_trace lifted
  exact ⟨staged, reached, ⟨rawD, function, stagedSize, sourceAt, stagedTrace⟩, adapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicInputLifting
