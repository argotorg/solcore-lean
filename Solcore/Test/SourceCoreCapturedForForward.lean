import Solcore.Test.SourceCoreCapturedForPublicExecution
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectWordPreservation

/-! The actual finite-loop calls first establish independent Source traces.
Those traces then imply public success at every sufficient execution budget
and every output-validation budget of at least one, on their original starts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedFor
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

/-- The actual public checkpoint admits all sufficiently large execution
budgets, with one output-validation step already sufficient. Returned states
have the same Source heap as the independently established application. -/
def ForwardWordAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle) (flag : Bool) (argument : Core.Word) (stop : Bool) (word : Core.Word)
    (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
    publicSession.startHandlePacked handle (.product (.bool flag) (.product (.word argument) (.bool stop))) runOptions.inputValidationFuel = .ok checkpoint ∧
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
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = .function (.product .bool (.product .word .bool)) .word)
    {function : Dynamic.Closure} (entrySource : entry.source = .closure function)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {flag : Bool} {argument word : Core.Word} {stop : Bool} (call : ObservedInvocation publicSession handle flag argument stop)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceInvocation support invocation state.heap entry.source flag argument stop (.value (.word word)) after) :
    ForwardWordAt support publicSession entries handle flag argument stop word after := by
  obtain ⟨publicCheckpoint, accepted, _resumed⟩ := call.executed
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have imported := (state.history.current.2.2.2.2 entry member).1
  rw [entryType, entryHandle] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.current.1 imported original
  have registryEq := started.function_tree_registry (.simple (.product (.bool flag) (.product (.word argument) (.bool stop)))) state.registry
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [registryEq]
    exact receiver.completion.result.extension
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.actual.header.function.context (.product .bool (.product .word .bool))
      (.product (.bool flag) (.product (.word argument) (.bool stop))) (.product (.bool flag) (.product (.word argument) (.bool stop))) :=
    .product
      (.data ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
        ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩)
      (.product
        (.data ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩
          ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩)
        (.data ⟨.bool stop, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool stop⟩
          ⟨.bool stop, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool stop⟩))
  obtain ⟨size, trace⟩ := trace
  rw [entrySource] at trace
  rw [← entryHandle] at started
  obtain ⟨required, finalStore, finalMap, finalWorld, _nativeEnough, _fullResult, publicEnough⟩ :=
    RecursiveNamedPublicDirectWordPreservation.public_resume_has_sufficient_fuel
      (completion := receiver.completion)
      (receiver := receiver.issued)
      (stagePrepared := actualStagePrepared fixture) (profile := observed.profile)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (history := state.history)
      (entry := entry) (member := member) (entryType := entryType) (entrySource := entrySource)
      (input := input) started metadata (.cons (.cons (.singleton (.bool stop)))) trace atCheckpoint
  refine ⟨publicCheckpoint, accepted, required, ?_⟩
  intro executionFuel outputFuel outcome enough positive resumed
  obtain ⟨publicCompletion, actual, _generation, reached, succeeded, wordValue, _exported,
      indexedAt, _related, history, returnedRegistry⟩ := publicEnough executionFuel outputFuel outcome enough positive resumed
  rw [registryEq] at returnedRegistry
  exact ⟨publicCompletion, succeeded, wordValue,
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      indexedAt.2.2.2, state.atRecipe, returnedRegistry, history⟩, rfl⟩

def ForwardMeaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
    ∃ (firstEntry secondEntry thirdEntry : Entry) (firstClosure secondClosure : Dynamic.Closure),
      firstEntry.sourceType = .function (.product .bool (.product .word .bool)) .word ∧ firstEntry.handle = sequence.first.handle ∧
      secondEntry.sourceType = .function (.product .bool (.product .word .bool)) .word ∧ secondEntry.handle = sequence.second.handle ∧
      thirdEntry.sourceType = .function (.product .bool (.product .word .bool)) .word ∧ thirdEntry.handle = sequence.third.handle ∧
      firstEntry.handle ≠ secondEntry.handle ∧
      firstEntry.source = .closure firstClosure ∧ secondEntry.source = .closure secondClosure ∧
      firstClosure.parameters = [observed.running, observed.argument, observed.shape.stop] ∧ secondClosure.parameters = [observed.running, observed.argument, observed.shape.stop] ∧
      ∃ first : RetainedState support sequence.first.completion.session [firstEntry],
      ∃ second : RetainedState support sequence.second.completion.session [firstEntry, secondEntry],
      ∃ written : RetainedState support sequence.firstCall.completion.session [firstEntry, secondEntry],
      ∃ third : RetainedState support sequence.third.completion.session [firstEntry, secondEntry, thirdEntry],
      ∃ other : RetainedState support sequence.secondCall.completion.session [firstEntry, secondEntry, thirdEntry],
      ∃ final : RetainedState support sequence.firstAgain.completion.session [firstEntry, secondEntry, thirdEntry],
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed]
          (.value firstEntry.source) first.heap ∧
        SourceCall support support.actual.header scope first.heap [.word (Core.Word.ofNatModulo 20)]
          (.value secondEntry.source) second.heap ∧
        SourceInvocation support scope second.heap firstEntry.source true (Core.Word.ofNatModulo 11) false
          (.value (.word (Core.Word.ofNatModulo 10))) written.heap ∧
        SourceCall support support.actual.header scope written.heap [.word (Core.Word.ofNatModulo 30)]
          (.value thirdEntry.source) third.heap ∧
        SourceInvocation support scope third.heap secondEntry.source false (Core.Word.ofNatModulo 21) false
          (.value (.word (Core.Word.ofNatModulo 20))) other.heap ∧
        SourceInvocation support scope other.heap firstEntry.source true (Core.Word.ofNatModulo 12) false
          (.value (.word (Core.Word.ofNatModulo 11))) final.heap ∧
        ForwardWordAt support sequence.second.completion.session [firstEntry, secondEntry] sequence.first.handle
          true (Core.Word.ofNatModulo 11) false (Core.Word.ofNatModulo 10) written.heap ∧
        ForwardWordAt support sequence.third.completion.session [firstEntry, secondEntry, thirdEntry] sequence.second.handle
          false (Core.Word.ofNatModulo 21) false (Core.Word.ofNatModulo 20) other.heap ∧
        ForwardWordAt support sequence.secondCall.completion.session [firstEntry, secondEntry, thirdEntry] sequence.first.handle
          true (Core.Word.ofNatModulo 12) false (Core.Word.ofNatModulo 11) final.heap

/-- Both nonempty and zero-iteration paths have a forward public
fuel guarantee on their original checkpoints, with exact Source post-heaps. -/
theorem sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedSequence fixture observed)
    (receiver : ObservedReceiver fixture observed) : ForwardMeaning stages sequence receiver := by
  obtain ⟨support, firstEntry, secondEntry, thirdEntry, firstClosure, secondClosure,
      firstType, firstHandle, secondType, secondHandle, thirdType, thirdHandle, distinct,
      firstSource, secondSource, firstParameters, secondParameters,
      first, second, written, third, other, final,
      firstTrace, secondTrace, writtenTrace, thirdTrace, otherTrace, finalTrace⟩ :=
    sequence_meaning fixture observed stages sequence receiver
  exact ⟨support, firstEntry, secondEntry, thirdEntry, firstClosure, secondClosure,
    firstType, firstHandle, secondType, secondHandle, thirdType, thirdHandle, distinct,
    firstSource, secondSource, firstParameters, secondParameters,
    first, second, written, third, other, final,
    firstTrace, secondTrace, writtenTrace, thirdTrace, otherTrace, finalTrace,
    forward_word second firstEntry (by simp) firstType firstSource firstHandle sequence.firstCall writtenTrace,
    forward_word third secondEntry (by simp) secondType secondSource secondHandle sequence.secondCall otherTrace,
    forward_word other firstEntry (by simp) firstType firstSource firstHandle sequence.firstAgain finalTrace⟩

/-- All static and receiving evidence comes from the actual accepted compiler
and authentic registry. No external receiver or body meaning is required. -/
theorem closed_sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedSequence fixture observed) :
    ∃ receiver, ForwardMeaning stages sequence receiver := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_forward_meaning fixture observed stages sequence receiver⟩

/-- The observed scenario is shared by reflection and forward preservation. -/
def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_forward_meaning fixture observed stages sequence
  IO.println "Actual captured for loops: independent Source traces, returned histories and sufficient public Word export fuel proved for all three direct calls"

end Tests.SourceCoreCapturedFor
