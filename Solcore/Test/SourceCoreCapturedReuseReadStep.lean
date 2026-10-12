import Solcore.Test.SourceCoreCapturedReuseCommon
import Solcore.Test.SourceCoreCapturedReuseSelection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning

/-! A retained closure is passed to the actual read function. Its successful
public Word result identifies the independent Source result and returns the
same finite history at the new actual session and heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedReuse
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

theorem RetainedState.read {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = .function .unit .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (call : ObservedCall publicSession observed.readRow.row.key [.function handle])
    {word : Core.Word} (returned : call.completion.value = .word word)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session entries,
      SourceCall support support.readHeader.header invocation state.heap [entry.source]
        (.value (.word word)) after.heap := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.makeInput, support.readInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.readHeader.header :=
    selected_read_at support.makeHeader support.readHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.function handle] [entry.source] := by
    rw [selectedHeader, support.readHeader.read_input_types, ← entryType, ← entryHandle]
    exact .cons (.retained entry member) .nil
  have registry := request.started.function_registry state.registry
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry receiver.completion.result.context.registry := by
    rw [registry]
    exact receiver.completion.result.extension
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selectedHeader]
    exact support.readDescriptor
  obtain ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      reached, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_retains
      (inputs := [support.makeInput, support.readInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture)
      (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (profile := observed.profile) (observations := support.observations)
      (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (metadata := metadata) (sourceAt := request.sourceAt)
      (invocation := invocation) call.started call.executed descriptor
  have requested := request.started.original.result_type_at
    (show state.artifact.RecipeAt fixture.recipe from by
      have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
          RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
        fun artifact _ atRecipe => by cases artifact; exact atRecipe
      exact convert _ _ state.atRecipe)
    request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.readHeader.read_result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans returned)
    (by rw [selectedHeader]; exact support.readHeader.read_output) result
  have returnedRegistry := request.started.returned_registry succeeded
  rw [registry] at returnedRegistry
  let next : RetainedState support call.completion.session entries :=
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      returnedAt, state.atRecipe, returnedRegistry, retained⟩
  refine ⟨next, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · rw [← selectedHeader]; exact request.sourceAt
  · simpa only [outcomeValue] using trace

end Tests.SourceCoreCapturedReuse
