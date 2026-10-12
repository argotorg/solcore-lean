import Solcore.Test.SourceCoreCapturedMappingPublicExecution
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputPreservation

/-! The same two observed mapping calls establish independent Source traces.
Those traces imply actual public export on their original starts at every
sufficient execution and output-validation budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedMapping
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def ForwardWordAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle)
    (argument : List (Core.Word × Core.Word)) (word : Core.Word) (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
    publicSession.startHandlePacked handle (publicArgument argument) runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ requiredExecution requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ completion : SourceCoreExecution.Completion publicArtifact,
          outcome = .succeeded completion ∧ completion.value = .word word ∧ completion.session.ExportsReady ∧
          ∃ returned : RetainedState support completion.session entries, returned.heap = after

private theorem forward_word {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    (entryType : entry.sourceType = .function (.mapping .word .word) .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function (.mapping .word .word) .word)
    {argument : List (Core.Word × Core.Word)} {word : Core.Word}
    (call : ObservedInvocation publicSession handle argument)
    (exportsReady : publicSession.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceInvocation support invocation state.heap entry.source argument (.value (.word word)) after) :
    ForwardWordAt support publicSession entries handle argument word after := by
  obtain ⟨publicCheckpoint, accepted, _resumed⟩ := call.executed
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have imported := (state.history.current.2.2.2.2 entry member).1
  rw [entryType, entryHandle] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.current.1 imported original
  have signature := started.selected.signature handleType
  have requested := started.requested_exact handleType
  have projected := started.resultProjection
  rw [signature.2] at projected
  have nativeResultEq : nativeResult = .word := (Except.ok.inj projected).symm
  subst nativeResult
  rw [← entryHandle] at started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨size, trace⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, requiredExecution, requiredOutput,
      payload, finalStore, finalMap, finalWorld, _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryOutputPreservation.public_resume_has_sufficient_fuel
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      support.supports fixture.source_wellFormed state.history entry member entryType
      (mapping_input argument) state.registry (state.atSession.exportsReady_iff.mp exportsReady)
      started (.singleton (sourceArgument argument)) trace atCheckpoint
  have payloadEq : payload = .word word := by
    have represented := fullResult.1
    cases represented with
    | value related =>
      obtain ⟨actual, sourceEq, nativeEq⟩ := CompatibleExpressionPrimitives.word_fields related
      cases Dynamic.Value.word.inj sourceEq
      exact nativeEq
  subst payload
  refine ⟨publicCheckpoint, accepted, requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome enoughExecution enoughOutput resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, atCompletion,
      _related, history, returnedRegistry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome enoughExecution enoughOutput resumed
  have valueEq : completion.value = .word word := atCompletion.1.trans (exported.word_value requested)
  let returned : RetainedState support completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := atCompletion.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := history }
  exact ⟨completion, succeeded, valueEq, atCompletion.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩

/-- Actual bootstrap authority and successful public transitions supply export
readiness. No Source execution or output-success assumption is supplied. -/
theorem closed_sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver),
      let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
      ∃ entry : Entry,
        entry.sourceType = .function (.mapping .word .word) .word ∧ entry.handle = sequence.factory.handle ∧
      ∃ initial : RetainedState support sequence.factory.completion.session [entry],
      ∃ first : RetainedState support sequence.first.completion.session [entry],
      ∃ final : RetainedState support sequence.second.completion.session [entry],
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed] (.value entry.source) initial.heap ∧
        SourceInvocation support scope initial.heap entry.source firstArgument (.value (.word seed)) first.heap ∧
        SourceInvocation support scope first.heap entry.source secondArgument (.value (.word seed)) final.heap ∧
        ForwardWordAt support sequence.factory.completion.session [entry] sequence.factory.handle
          firstArgument seed first.heap ∧
        ForwardWordAt support sequence.first.completion.session [entry] sequence.factory.handle
          secondArgument seed final.heap := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨support⟩ := static_supports fixture observed stages receiver.completion.result.context.registry receiver.issued
  let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
  obtain ⟨entry, entryType, handle, handleType, initial, factoryTrace⟩ := first_meaning support stages sequence.factory
  obtain ⟨first, firstTrace⟩ := invoke initial entry (by simp) entryType handle handleType
    sequence.first sequence.firstValue scope
  obtain ⟨final, finalTrace⟩ := invoke first entry (by simp) entryType handle handleType
    sequence.second sequence.secondValue scope
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.factory.ready).exportsReady sequence.factory.authority
  have factoryReady := sequence.factory.executed.exportsReady ready
  have firstReady := sequence.first.executed.exportsReady factoryReady
  exact ⟨receiver, support, entry, entryType, handle, initial, first, final, factoryTrace, firstTrace, finalTrace,
    forward_word initial entry (by simp) entryType handle handleType sequence.first factoryReady firstTrace,
    forward_word first entry (by simp) entryType handle handleType sequence.second firstReady finalTrace⟩

/-- Run the same three-call scenario once and check both proof directions. -/
def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_forward_meaning fixture observed stages sequence
  IO.println "Actual mapping closure reuse: Source reflection and public export at sufficient fuel, with exact receivers and histories proved"

end Tests.SourceCoreCapturedMapping
