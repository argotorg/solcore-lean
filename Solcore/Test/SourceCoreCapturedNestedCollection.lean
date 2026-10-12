import Solcore.Test.SourceCoreCapturedNestedIssuance
import Solcore.Test.SourceCoreCapturedNestedSelectionMeaning
import Solcore.Test.SourceCoreCapturedNestedEchoMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollection

/-! The real mapping echo exports and collects its three ordered function
occurrences. Their Source values are recovered from the actual echo trace. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedNested
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

theorem mapping_input {entries : List Entry} {context : SourceSemantics.Context}
    (first second : Entry) (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = .function .unit .word)
    (secondType : second.sourceType = .function .unit .word)
    {a b : SourceCorePublicValues.Handle} (firstHandle : first.handle = a) (secondHandle : second.handle = b) :
    RecursiveNamedPublicFunctionHistoryInputs.Input entries context containerType
      (mappingArgument a b a) (sourceArgument first.source second.source) := by
  have firstInput := RecursiveNamedPublicFunctionHistoryInputs.Input.retained (context := context) first firstMember
  have secondInput := RecursiveNamedPublicFunctionHistoryInputs.Input.retained (context := context) second secondMember
  rw [firstType, firstHandle] at firstInput
  rw [secondType, secondHandle] at secondInput
  have wordInput (word : Core.Word) : RecursiveNamedPublicFunctionHistoryInputs.Input entries context
      .word (.word word) (.word word) :=
    .data ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩
  exact .mapping (.entry (wordInput _) firstInput (.entry (wordInput _) secondInput
    (.entry (wordInput _) firstInput (.empty _ _))))

def CollectedAt {fixture : CompiledFixture} {publicArtifact : SourceCoreExecution.Artifact}
    (completion : SourceCoreExecution.Completion publicArtifact)
    (a b c : SourceCorePublicValues.Handle) (returned : completion.value = mappingArgument a b c)
    (source : Dynamic.Value) (added : List Entry) : Prop :=
  ∃ (artifact : SourceCoreIndexedSession.Artifact) (actual : SourceCoreIndexedSession.Completion artifact)
    (native : Core.Value) (type : Core.Ty), completion.IndexedAt actual ∧
    RecursiveNamedPublicNestedOutputSelections.Selected fixture.recipe.compiled.compatible.checked actual.session
      (returned.symm ▸ outputSelection a b c) source native type runOptions.outputValidationFuel added

theorem collect {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (echo first second : Entry) (echoMember : echo ∈ entries)
    (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (echoType : echo.sourceType = .function containerType containerType)
    (firstType : first.sourceType = .function .unit .word)
    (secondType : second.sourceType = .function .unit .word)
    (echoSource : echo.source = .global (CallableNamedReversal.global (CallableNamedMetadata.global
      support.readPacket.header.named.specialized support.readInput.prepared.available)))
    {handle a b : SourceCorePublicValues.Handle}
    (echoHandle : echo.handle = handle) (firstHandle : first.handle = a) (secondHandle : second.handle = b)
    (call : ObservedEcho publicSession handle a b) (invocation : Staging.Recursive.Scope) :
    ∃ (added : List Entry) (_collected : Collected first.source second.source
        call.firstOutput call.secondOutput call.repeatedOutput added)
      (next : RetainedState support call.completion.session (entries ++ added)),
      SourceCall support support.readHeader.header invocation state.heap
        [sourceArgument first.source second.source] (.value (sourceArgument first.source second.source)) next.heap ∧
      CollectedAt (fixture := fixture) call.completion call.firstOutput call.secondOutput call.repeatedOutput
        call.returned (sourceArgument first.source second.source) added := by
  have input := mapping_input (context := support.makeHeader.header.function.context)
    first second firstMember secondMember firstType secondType firstHandle secondHandle
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
    nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, source, payload, after,
    finalMap, finalWorld, reached, added, contextAt, issued, extended, _diagnostics, started, _parameterView, _resultView,
    succeeded, actualAt, packing, trace, _resultAt, _nativeValue, selected, _handles, _related, retained, returnedRegistry⟩ :=
    RecursiveNamedPublicActualRegistryOutputCollection.public_invoke_succeeded_collects
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      support.supports fixture.source_wellFormed state.history echo echoMember echoType input state.atRecipe
      state.registry state.atSession (by simpa only [echoHandle] using call.executed)
      (call.returned.symm ▸ outputSelection call.firstOutput call.secondOutput call.repeatedOutput) invocation
  have sourcesEq : sources = [sourceArgument first.source second.source] := by cases packing; rfl
  have sourceTrace : SourceCall support support.readHeader.header invocation state.heap
      [sourceArgument first.source second.source] (.value source) after := by
    refine ⟨support.readInput.prepared.available, CallableNamedReversal.global
      (CallableNamedMetadata.global support.readPacket.header.named.specialized support.readInput.prepared.available),
      sourceSize, ?_, ?_⟩
    · rw [support.readEq]
      exact support.readPacket.sourceAt
    · simpa only [sourcesEq, echoSource] using trace
  have sourceEq := sourceTrace.echo_value
  rw [sourceEq] at selected sourceTrace
  have originalSelected : RecursiveNamedPublicNestedOutputSelections.Selected fixture.recipe.compiled.compatible.checked actual.session
      (outputSelection call.firstOutput call.secondOutput call.repeatedOutput)
      (sourceArgument first.source second.source) payload nativeResult runOptions.outputValidationFuel added := by
    exact selected_uncast call.returned.symm selected
  obtain ⟨collected⟩ := selected_entries originalSelected
  let next : RetainedState support call.completion.session (entries ++ added) := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := retained }
  exact ⟨added, collected, next, sourceTrace, state.artifact, actual, payload, nativeResult, actualAt, selected⟩

end Tests.SourceCoreCapturedNested
