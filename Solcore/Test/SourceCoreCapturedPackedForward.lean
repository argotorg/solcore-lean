import Solcore.Test.SourceCoreCapturedPackedPublicExecution
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectWordPreservation

/-! The actual two packed calls first establish independent Source traces.
Those traces then imply public success at every sufficient execution budget
and every output-validation budget of at least one, on their original starts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedPacked
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

/-- The actual public checkpoint admits all sufficiently large execution
budgets, with one output-validation step already sufficient. Returned states
have the same Source heap as the independently established application. -/
def ForwardWordAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle) (argument word : Core.Word)
    (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
    publicSession.startHandlePacked handle (.word argument) runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ required, ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
      required ≤ executionFuel → 1 ≤ outputFuel →
      checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion publicArtifact,
        outcome = .succeeded completion ∧ completion.value = .word word ∧
        ∃ returned : RetainedState support completion.session entries, returned.heap = after

private theorem forward_word {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = .function .word .word)
    {function : Dynamic.Closure} (entrySource : entry.source = .closure function)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {argument word : Core.Word} (call : ObservedInvocation publicSession handle argument)
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
  have registryEq := started.function_tree_registry (.simple (.word argument)) state.registry
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [registryEq]
    exact receiver.completion.result.extension
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.actual.header.function.context .word (.word argument) (.word argument) :=
    .data ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩
      ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩
  obtain ⟨size, trace⟩ := trace
  rw [entrySource] at trace
  rw [← entryHandle] at started
  obtain ⟨required, finalStore, finalMap, finalWorld, _nativeEnough, _fullResult, publicEnough⟩ :=
    RecursiveNamedPublicDirectWordPreservation.public_resume_has_sufficient_fuel
      (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (stagePrepared := actualStagePrepared fixture) (profile := observed.profile)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (history := state.history)
      (entry := entry) (member := member) (entryType := entryType) (entrySource := entrySource)
      (input := input) started metadata (.singleton (.word argument)) trace atCheckpoint
  refine ⟨publicCheckpoint, accepted, required, ?_⟩
  intro executionFuel outputFuel outcome enough positive resumed
  obtain ⟨publicCompletion, actual, _generation, reached, succeeded, wordValue, _exported,
      indexedAt, _related, history, returnedRegistry⟩ := publicEnough executionFuel outputFuel outcome enough positive resumed
  rw [registryEq] at returnedRegistry
  exact ⟨publicCompletion, succeeded, wordValue,
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      indexedAt.2.2.2, state.atRecipe, returnedRegistry, history⟩, rfl⟩

/-- Both finite observed public calls have an independently justified forward
fuel guarantee on the original checkpoint, with exact captured Word 10 and
Source post-heaps. No Source execution assumption is an input. -/
theorem sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    ∃ support : PublicSupports receiver,
      let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
      ∃ entry : Entry,
        entry.sourceType = .function .word .word ∧ entry.handle = sequence.factory.handle ∧
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
  obtain ⟨support, entry, function, entryType, handle, source, _parameters, _result,
      initial, first, final, factoryTrace, firstTrace, finalTrace⟩ :=
    sequence_meaning fixture observed stages sequence receiver
  exact ⟨support, entry, entryType, handle, initial, first, final, factoryTrace, firstTrace, finalTrace,
    forward_word initial entry (by simp) entryType source handle sequence.first firstTrace,
    forward_word first entry (by simp) entryType source handle sequence.second finalTrace⟩

/-- Use the existing observed sequence once for reflection and preservation. -/
def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_forward_meaning fixture observed stages sequence receiver
  IO.println "Actual packed closure reuse: Source reflection and public Word preservation with output fuel 1 proved"

end Tests.SourceCoreCapturedPacked
