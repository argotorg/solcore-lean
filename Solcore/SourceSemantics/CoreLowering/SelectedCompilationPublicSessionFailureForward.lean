import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicClosureHistory
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicHistorySourceInputs
import Solcore.SourceSemantics.Staging.SelectedRecursivePreservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalProgramSupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicBodyInvocationBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryFailures

/-! An independent Source fault determines every sufficiently fueled public
failure. The actual failed session retains the reached heap, complete physical
cache and prior exported handles. Output validation fuel is unrestricted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFailureForward
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

def FailureForwardAt (rows : Inventory inputs) (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) (recipe : SourceCoreIndexedSession.Recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (failure : Staging.Recursive.Failure) (call : StartedCall session key arguments options)
    (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution token,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ returned : SourceCoreExecution.Session artifact,
        outcome = .failed token returned ∧ returned.ExportsReady ∧
        ∃ next : State rows anchor initial profile recipe returned entries,
          next.heap = after ∧
          CallableIndexedOwnedPublicDecodedStagedCallFaults.faults next.receiving.result.diagnostics failure token

theorem forward_call (support : SelectedCompilationPhysicalProgramSupport.Support compiled (headers rows) (keys compiled) initial)
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
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (registry : request.encodedValues.registry = state.receiving.result.context.registry)
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {failure : Staging.Recursive.Failure}
    (trace : SourceCall anchor request.header invocation state.heap arguments (.fault failure) after) :
    FailureForwardAt (entries := entries) rows anchor initial profile recipe failure call after := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicClosureHistory.History.current_arguments
      (profile := profile)
      (bodyTyping := support.bodyTyping) (prepared := prepared)
      (selected := request.selected) (history := state.history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    rows request.header request.selected.member
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).2
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.preserves_root
      (stagePrepared := stagePrepared recipe.compiled) (completion := state.receiving)
      (functions := functions rows initial profile)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (packet := support.bodies request.header request.selected.member) (preservesBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.preserves_bodies support state.issued
          state.extension request.header request.selected.member selected budget)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := state.history.physical)
      (bodyTyping := support.bodyTyping)
      (selected := request.selected) (caller := state.caller)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := supports) applied
  obtain ⟨token, rfl, faultRelated⟩ : ∃ token,
      value = .inLeft request.header.output (.word token) ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics failure token := by
    have related := result.2.1
    cases related with
    | fault related => exact ⟨_, rfl, related⟩
  have completes : ∀ executionFuel, requiredExecution ≤ executionFuel →
      request.checkpoint.NativeDone executionFuel (.inLeft request.header.output (.word token)) finalStore :=
    fun fuel bound => request.started.initial.native_done_iff.mpr (enough fuel bound)
  have contextSupports := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).1
  have callerHeap := heapTyped.transportContext contextSupports
  have callerArguments := argumentsTyped.transportContext contextSupports
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
  have preserved := Staging.Recursive.SelectedPreservation.applies_fault selectedBodies
    (SelectedCompilationPublicHistorySourceInputs.header_runtime support.bodyTyping anchor) callerHeap
    (SelectedCompilationPublicHistorySourceInputs.source_typed support.bodyTyping sourceAt anchor state.heap)
    packing (packing.hasType callerArguments) applied
  have checkpointReady := request.started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp ready)
  refine ⟨requiredExecution, token, ?_⟩
  intro executionFuel outputFuel outcome executionBound resumed
  have completed := completes executionFuel executionBound
  obtain ⟨returned, outcomeEq⟩ := resumed.native_failed request.atCheckpoint completed rfl
  have failedResume : call.checkpoint.ResumeAt executionFuel outputFuel (.failed token returned) := outcomeEq ▸ resumed
  obtain ⟨actual, _generation, actualValue, actualStore, actualCompleted, failed, returnedAt⟩ :=
    failedResume.indexed_failed request.atCheckpoint
  have same := completed.symm.trans actualCompleted
  cases same
  obtain ⟨reached, _related, retained⟩ := state.history.semantic.after_failure
    rfl request.started request.selected failed result preserved.1
  have physicalRetained := state.history.after_result result retained
  have returnedRegistry : actual.RegistryAt state.receiving.result.context.registry := by
    rw [← registry]
    exact congrArg SourceCoreCompatibleValues.Context.registry (failed.2.2.2.2.1.trans request.started.values)
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
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := returnedRegistry
    history := physicalRetained }
  exact ⟨returned, outcomeEq, returnedAt.exportsReady_iff.mpr (failed.exportsReady checkpointReady),
    next, rfl, faultRelated⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFailureForward
