import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicClosureHistory
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicHistorySourceInputs
import Solcore.SourceSemantics.Staging.SelectedRecursivePreservation
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFailureStep
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionRegistry

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFailureStep
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicPhysicalSessionState
open SelectedCompilationPhysicalProgramSupport (stagePrepared)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}
theorem State.failed_call_at_input_registry (support : SelectedCompilationPhysicalProgramSupport.Support compiled (headers rows) (keys compiled) initial)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies
      (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled))
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : StartedCall session key publicArguments options)
    (returned : SourceCoreExecution.Session artifact) (reason : Word)
    (failedCall : session.RunAt key publicArguments options (.ok (.failed reason returned)))
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ failure, ∃ after : State rows anchor initial profile recipe returned entries,
      SourceCall anchor request.header invocation state.heap arguments
        (.fault failure) after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
        after.receiving.result.diagnostics failure reason := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨receiving, contextAt, issued, extension, history⟩ := state.at_named_request prepared request
  have registry : request.encodedValues.registry = receiving.result.context.registry :=
    (congrArg SourceCoreCompatibleValues.Context.registry contextAt).symm
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicClosureHistory.History.current_arguments
      (profile := profile)
      (bodyTyping := support.bodyTyping) (prepared := prepared)
      (selected := request.selected) (history := history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    rows request.header request.selected.member
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).2
  obtain ⟨actual, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, failed, returnedAt, trace, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.public_run_failed_reflects
      (stagePrepared := stagePrepared recipe.compiled) (completion := receiving)
      (functions := functions rows initial profile)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (packet := support.bodies request.header request.selected.member) (reflectsBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.reflects_bodies support issued
          extension request.header request.selected.member selected budget)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := history.physical)
      (bodyTyping := support.bodyTyping)
      (selected := request.selected) (caller := state.caller)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := request.sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared)
      (started := request.started) (invocation := invocation)
      call.started request.atCheckpoint failedCall descriptor
  obtain ⟨failure, outcomeEq⟩ : ∃ failure, outcome = .fault failure := by
    have represented := result.2.1
    cases represented with
    | value _ => have impossible := failed.2.1; cases impossible
    | fault _ => exact ⟨_, rfl⟩
  subst outcome
  have fault : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
      receiving.result.diagnostics failure reason := by
    have represented := result.2.1
    cases represented with
    | fault matched =>
      have decoded := failed.2.1
      simp only [Core.LanguageResult.decode?] at decoded
      cases decoded
      exact matched
  have contexts := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).1
  have callerHeap := heapTyped.transportContext contexts
  have callerArguments := argumentsTyped.transportContext contexts
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
  have preserved := Staging.Recursive.SelectedPreservation.applies_fault selectedBodies
    (SelectedCompilationPublicHistorySourceInputs.header_runtime support.bodyTyping anchor) callerHeap
    (SelectedCompilationPublicHistorySourceInputs.source_typed support.bodyTyping request.sourceAt anchor state.heap)
    packing (packing.hasType callerArguments) trace
  obtain ⟨reached, _related, retained⟩ := history.semantic.after_failure
    (SourceCoreIndexedSession.Recipe.prepare_compiled prepared) request.started request.selected
    failed result preserved.1
  have physicalRetained := history.after_result result retained
  have returnedRegistry : actual.RegistryAt receiving.result.context.registry := by
    have actualValues := failed.2.2.2.2.1.trans request.started.values
    exact (congrArg SourceCoreCompatibleValues.Context.registry actualValues).trans registry
  let next : State rows anchor initial profile recipe returned entries := {
    artifact := state.artifact
    session := actual
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := extension
    registry := returnedRegistry
    history := physicalRetained }
  exact ⟨failure, next, ⟨request.rawD, request.function, sourceSize, request.sourceAt, trace⟩, fault⟩


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFailureStep
