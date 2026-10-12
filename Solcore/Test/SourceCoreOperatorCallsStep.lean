import Solcore.Test.SourceCoreOperatorCallsIssuance
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticExtension
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryRegistryExtension
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedStart

/-! A retained actual named handle is passed through both branches of the same checked operator expression. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

theorem RetainedState.select {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (state : RetainedState support session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = functionType)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {flag : Bool} {value returned : Core.Word}
    (call : ObservedCall session observed.selectRow.row.key (selectArguments handle flag value) returned)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session entries,
      SourceCall support support.selectHeader.header invocation state.heap
        [entry.source, .bool flag, .word value] (.value (.word returned)) after.heap := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.identityInput, support.selectInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.selectHeader.header :=
    selected_select_at support.identityHeader support.selectHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      (selectArguments handle flag value) [entry.source, .bool flag, .word value] := by
    rw [selectedHeader, support.selectHeader.select_input_types]
    change RecursiveNamedPublicFunctionHistoryInputs.Inputs entries support.selectHeader.header.function.context
      [functionType, .bool, .word] [.function handle, .bool flag, .word value]
      [entry.source, .bool flag, .word value]
    refine .cons ?_ (.cons (.data ?_ ?_) (.cons (.data ?_ ?_) .nil))
    · rw [← entryType, ← entryHandle]; exact .retained entry member
    · exact ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
    · exact ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
    · exact ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
    · exact ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
  obtain ⟨receiving, _receiverMember, contextAt, issued, extended, retained, _diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryNamedStart.named_start state.history state.registry request.started
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]; exact .refl _
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selectedHeader]; exact support.selectDescriptor
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued issued present (state.extension.trans extended) represented
  obtain ⟨actual, generation, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      reached, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_retains
      (inputs := [support.identityInput, support.selectInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := receiving)
      (receiver := issued) (profile := observed.profile) (observations := support.observations)
      (extension := receiving.result.extension) (semantic := semantic)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := retained)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (metadata := metadata) (sourceAt := request.sourceAt)
      (invocation := invocation) call.started call.executed descriptor
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.selectHeader.result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans call.returned) (by rw [selectedHeader]; exact support.selectHeader.output) result
  have returnedRegistry := request.started.returned_registry succeeded
  rw [← contextAt] at returnedRegistry
  let next : RetainedState support call.completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := returnedRegistry
    history := retained }
  refine ⟨next, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · rw [← selectedHeader]; exact request.sourceAt
  · simpa only [outcomeValue] using trace

end Tests.SourceCoreOperatorCalls
