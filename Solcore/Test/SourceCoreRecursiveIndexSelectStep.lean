import Solcore.Test.SourceCoreRecursiveIndexInputs
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedStart
import Solcore.Test.SourceCoreRecursiveIndexSelection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry

/-! A genuine successful public selection extends the current retained
history with its actual selected closure. The next state is the returned session,
including the original captured heap and encoder metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicSession : SourceCoreExecution.Session publicArtifact} {entries : List Entry}

/-- An actual public mapping selection constructs Source execution and the next history.
Every older entry remains in order, followed by this call's exported handle. -/
theorem RetainedState.select_typed_handle
    (state : RetainedState support publicSession entries)
    (first second : Entry) (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle)
    {key : Core.Word}
    (call : ObservedFunctionCall publicSession observed.selectRow.row.key [table firstHandle secondHandle, .word key])
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry, entry.sourceType = .function .unit .word ∧ entry.handle = call.handle ∧
      call.handle.sourceType = .function .unit .word ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.selectHeader.header invocation state.heap [sourceTable first second, .word key]
          (.value entry.source) after.heap := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.makeInput, support.echoInput, support.chooseInput, support.selectInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selected := selected_select_at support.makeHeader support.echoHeader support.chooseHeader support.selectHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [table firstHandle secondHandle, .word key] [sourceTable first second, .word key] := by
    rw [selected, support.selectHeader.select_input_types_source]
    exact select_inputs first second firstMember secondMember firstType secondType firstHandleEq secondHandleEq key
  obtain ⟨receiving, _member, contextAt, issued, extended, retained, _diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryNamedStart.named_start state.history state.registry request.started
  have descriptor : SourceCoreCallableContracts.Descriptor
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact support.selectDescriptor
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued issued present (state.extension.trans extended) represented
  obtain ⟨actual, generation, nativeValue, finalStore, capture,
    sourceSize, outcome, heap, mapping, world, succeeded, valueEq, typeEq, budgetEq,
    returnedAt, trace, result, caller, source, payload, sourceValue, nativePayload, related, continued⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_remembers
      (inputs := [support.makeInput, support.echoInput, support.chooseInput, support.selectInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture)
      (completion := receiving)
      (receiver := issued)
      (profile := observed.profile)
      (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiving.result.extension)
      (semantic := semantic)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := retained)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (invocation := invocation) (inputReceipts := inputs)
      (metadata := by rw [contextAt]; exact .refl _)
      (sourceAt := request.sourceAt)
      call.started call.executed call.returned descriptor
  let entry : Entry := ⟨request.header.function.resultType, source, call.handle, payload,
    request.header.output, runOptions.outputValidationFuel⟩
  let after : RetainedState support call.completion.session (entries ++ [entry]) := {
    artifact := state.artifact
    session := actual.session
    mapping := mapping
    world := world
    heap := heap
    store := finalStore
    caller := caller
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := by
      have registered := request.started.returned_registry succeeded
      exact (congrArg (·.registry) contextAt).symm ▸ registered
    history := continued }
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selected, support.selectHeader.select_result_type] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans call.returned)
  refine ⟨entry, ?_, rfl, handleType, after, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · change request.header.function.resultType = .function .unit .word
    rw [selected]
    exact support.selectHeader.select_result_type
  · exact selected ▸ request.sourceAt
  · simpa only [entry, after, sourceValue] using trace

end Tests.SourceCoreRecursiveIndex
