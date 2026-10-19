import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialReceiver
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicInputLifting

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialDataInputLifting
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPublicSessionState (StartedCall SourceCall)
open SelectedCompilationPublicSessionInitial (Started)
open SelectedCompilationPhysicalProgramSupport (Support stagePrepared stages)
open SelectedCompilationStagePublicInputLifting (PlainCall NamedBodies)

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} (rows : Inventory inputs)
  (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
  (anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  (support : Support recipe.compiled (headers rows) (keys recipe.compiled) initial)
  {publicArtifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session publicArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

theorem lift_call
    (bodies : NamedBodies support)
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (call : StartedCall session key publicArguments options)
    (start : Started rows prepared header call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {plain : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : PlainCall anchor header invocation ⟨[]⟩ arguments plain after) :
    ∃ staged reached, SourceCall anchor header invocation ⟨[]⟩ arguments staged reached ∧
      Staging.Recursive.Lifting.Adapted plain after staged reached := by
  obtain ⟨receiving, contextAt, receiverIssued, receiverExtension⟩ :=
    SelectedCompilationPublicInitialReceiver.of_started support start
  have receiverRegistry := congrArg SourceCoreCompatibleValues.Context.registry contextAt
  have metadata : SourceCoreRawMetadata.Extends start.encodedValues.registry receiving.result.context.registry := by
    rw [receiverRegistry]
    exact .refl _
  obtain ⟨caller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicInitialArguments.initial_data_arguments
      (inputs := inputs) (rows := rows) (distinct := distinct) (completion := receiving)
      (profile := support.profile) (bodyRegistry := initial.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      (bodyTyping := support.bodyTyping) (prepared := prepared) (selected := start.selected)
      (opened := start.opened) (fresh := start.fresh) (ready := start.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl session) (atSession := start.atSession)
      (started := start.started) (inputTypes := inputTypes) (inputMeanings := inputMeanings) (metadata := metadata)
  obtain ⟨rawD, function, sourceAt, plainTrace⟩ := trace
  obtain ⟨size, measured⟩ := RecursiveNamedCallBounds.CallOutcome.has_size plainTrace
  let packet := support.bodies header start.selected.member
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt packet.prepared packet.aligned
    start.selected.member (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
    caller.physical heaps.runtime_hasTypes
  obtain ⟨descriptor⟩ := SelectedCompilationCertifiedPublicSession.header_descriptor header
  obtain ⟨sidecar, _issued, _same, globalSelected, _declaration, _local, _evidence, _return, _analysis⟩ :=
    CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected
      sourceAt packet.prepared packet.aligned (stagePrepared recipe.compiled) descriptor
  have selected : (stages recipe.compiled).Closure header.function
      (RecursiveStageRegistry.scope sidecar [] header.function) := by
    rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] at globalSelected
    exact globalSelected
  obtain ⟨staged, reached, lifted, adapted⟩ :=
    SelectedCompilationStageNamedInvocationLifting.lifts_invocation
      (functions := SelectedCompilationPhysicalProgramSupport.functions support)
      (registry := receiving.result.context.registry)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (caller := caller.base.val) (header := header) (physicalCapture := capture) (sourceAt := sourceAt)
      packet.layouts caller.physical start.selected.member support.bodyTyping.function_ids
      (support.certificates header start.selected.member) stable heapTyped argumentsTyped represented heaps
      selected size (bodies receiving receiverIssued receiverExtension header start.selected.member size selected)
      measured (Nat.le_refl _)
  obtain ⟨stagedSize, stagedTrace⟩ := Staging.Recursive.Size.Applies.of_trace lifted
  exact ⟨staged, reached, ⟨rawD, function, stagedSize, sourceAt, stagedTrace⟩, adapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialDataInputLifting
