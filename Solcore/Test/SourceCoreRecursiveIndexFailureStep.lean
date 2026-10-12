import Solcore.Test.SourceCoreRecursiveIndexInputs
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedReflection

/-! The failed index call keeps the exact current encoder registry and all
older handle captures. The Source failure remains related to the actual token;
no injectivity assumption about diagnostic tokens is required. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {artifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session artifact} {entries : List Entry}

/-- The actual failed public call retains export authority for the next call. -/
theorem ObservedFailure.exportsReady {key : SourceCoreIndexedSession.Key}
    {arguments : List SourceCorePublicValues.Value}
    (call : ObservedFailure session key arguments) (ready : session.ExportsReady) :
    call.returned.ExportsReady := by
  have compiledAt : ∃ compiled, artifact.CompiledAt compiled := by
    rcases artifact with ⟨compiled, opened⟩
    exact ⟨compiled, rfl⟩
  obtain ⟨compiled, compiledAt⟩ := compiledAt
  obtain ⟨checkpoint, started, resumed⟩ := call.executed
  obtain ⟨_recipe, _native, indexedSession, indexedCheckpoint, _opened, atSession, atCheckpoint, actualStart⟩ :=
    SourceCoreExecution.Session.start_indexed (compiled := compiled) compiledAt started
  obtain ⟨actual, _generation, _value, _store, _completed, failed, returnedAt⟩ :=
    resumed.indexed_failed atCheckpoint
  exact returnedAt.exportsReady_iff.mpr (failed.exportsReady
    ((indexedSession.start_root_receipt actualStart).initial_registry.exportsReady
      (atSession.exportsReady_iff.mp ready)))

theorem RetainedState.select_failure
    (state : RetainedState support session entries)
    (first second : Entry) (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle)
    {key : Core.Word}
    (call : ObservedFailure session observed.selectRow.row.key [table firstHandle secondHandle, .word key])
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.returned entries, ∃ failure,
      SourceCall support support.selectHeader.header invocation state.heap
        [sourceTable first second, .word key] (.fault failure) after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics
        failure call.reason := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.makeInput, support.echoInput, support.chooseInput, support.selectInput]
    support.rows support.complete state.atRecipe state.history.current.1 state.atSession call.started
  have selected := selected_select_at support.makeHeader support.echoHeader support.chooseHeader
    support.selectHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [table firstHandle secondHandle, .word key] [sourceTable first second, .word key] := by
    rw [selected, support.selectHeader.select_input_types_source]
    exact select_inputs first second firstMember secondMember firstType secondType firstHandleEq secondHandleEq key
  have descriptor : SourceCoreCallableContracts.Descriptor
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact support.selectDescriptor
  obtain ⟨receiving, _member, contextAt, issued, extended, retained, _diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryNamedStart.named_start state.history state.registry request.started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued issued present (state.extension.trans extended) represented
  obtain ⟨actual, value, finalStore, capture, sourceSize, outcome, sourceHeap, finalMap, finalWorld,
      failed, returnedAt, trace, result, reached, _related, history⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicFailures.public_run_failed_retains
      (inputs := [support.makeInput, support.echoInput, support.chooseInput, support.selectInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := receiving) (receiver := issued)
      (profile := observed.profile) (observations := support.observations)
      (extension := receiving.result.extension) (semantic := semantic)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      (namedSupport := support.supports) (wellFormed := fixture.source_wellFormed)
      (prepared := fixture.recipePrepared) (selected := request.selected)
      (caller := state.caller) (history := retained) (atCheckpoint := request.atCheckpoint)
      (started := request.started) (inputReceipts := inputs)
      (metadata := by rw [contextAt]; exact .refl _)
      (sourceAt := request.sourceAt) (invocation := invocation) call.started call.executed descriptor
  have registryAt : actual.RegistryAt request.encodedValues.registry := by
    have values := failed.2.2.2.2.1.trans request.started.values
    rcases request with ⟨checkpoint, root, header, payloads, encodedValues, rawD, function,
      atCheckpoint, started, selected, sourceAt⟩
    cases checkpoint
    exact congrArg SourceCoreCompatibleValues.Context.registry values
  let after : RetainedState support call.returned entries := {
    artifact := state.artifact
    session := actual
    mapping := finalMap
    world := finalWorld
    heap := sourceHeap
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registryAt
    history := history }
  have represented := result.2.1
  cases represented with
  | value _ => have impossible := failed.2.1; cases impossible
  | @fault failure token matched =>
    have tokenEq : token = call.reason := by
      simpa only [Core.LanguageResult.decode?, Option.some.injEq, Core.LanguageResult.Outcome.failed.injEq] using failed.2.1
    refine ⟨after, failure, ⟨request.rawD, request.function, sourceSize, ?_, trace⟩, ?_⟩
    · exact selected ▸ request.sourceAt
    · exact tokenEq ▸ matched

end Tests.SourceCoreRecursiveIndex
