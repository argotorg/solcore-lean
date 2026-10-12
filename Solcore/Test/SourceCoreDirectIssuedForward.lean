import Solcore.Test.SourceCoreDirectIssuedPublicExecution
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableWordPreservation

/-! The actual two packed calls first establish independent Source traces.
Those traces then imply public success at every sufficient execution budget
and every output-validation budget of at least one, on their original starts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open RecursiveNamedPublicFunctionHistory (Entry)

/-- The actual public checkpoint admits all sufficiently large execution
budgets, with one output-validation step already sufficient. Returned states
have the same Source heap as the independently established application. -/
def ForwardWordAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle) (argument : SourceCorePublicValues.Value) (word : Core.Word)
    (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
    publicSession.startHandlePacked handle argument runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ required, ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
      required ≤ executionFuel → 1 ≤ outputFuel →
      checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion publicArtifact,
        outcome = .succeeded completion ∧ completion.value = .word word ∧
        ∃ returned : RetainedState support completion.session entries, returned.heap = after

private theorem forward_word {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) {parameter : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {argument : SourceCorePublicValues.Value} {source : Dynamic.Value} {word : Core.Word}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context parameter argument source)
    (simple : SourceCoreIndexedSession.FunctionTreeSimple argument)
    (call : ObservedInvocation publicSession handle argument)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceInvocation support invocation state.heap entry.source source word after) :
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
  have registryEq := started.function_tree_registry simple state.registry
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [registryEq]
    exact receiver.completion.result.extension
  obtain ⟨size, trace⟩ := trace
  rw [← entryHandle] at started
  obtain ⟨required, finalStore, finalMap, finalWorld, _nativeEnough, _fullResult, publicEnough⟩ :=
    RecursiveNamedPublicDirectCallableWordPreservation.public_resume_has_sufficient_fuel
      (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (stagePrepared := actualStagePrepared fixture) (profile := observed.profile)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (history := state.history)
      (entry := entry) (member := member) (entryType := entryType)
      (input := input) started metadata (.singleton source) trace atCheckpoint
  refine ⟨publicCheckpoint, accepted, required, ?_⟩
  intro executionFuel outputFuel outcome enough positive resumed
  obtain ⟨publicCompletion, actual, _generation, reached, succeeded, wordValue, _exported,
      indexedAt, _related, history, returnedRegistry⟩ := publicEnough executionFuel outputFuel outcome enough positive resumed
  rw [registryEq] at returnedRegistry
  exact ⟨publicCompletion, succeeded, wordValue,
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      indexedAt.2.2.2, state.atRecipe, returnedRegistry, history⟩, rfl⟩

def ForwardSequenceMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
    ∃ first named builtin : Entry,
      first.sourceType = .function .unit .word ∧
      named.sourceType = .function (.function .unit .word) .word ∧
      builtin.sourceType = .function .integer .word ∧
      first.handle = sequence.first.handle ∧ named.handle = sequence.named.handle ∧
      builtin.handle = sequence.builtin.handle ∧
      named.source = .global (CallableNamedReversal.global (CallableNamedMetadata.global
        support.readPacket.header.named.specialized support.readInput.prepared.available)) ∧
      builtin.source = .builtin ⟨.wordFromInteger⟩ ∧
      ∃ firstState : RetainedState support sequence.first.completion.session [first],
      ∃ namedState : RetainedState support sequence.named.completion.session [first, named],
      ∃ readState : RetainedState support sequence.read.completion.session [first, named],
      ∃ builtinState : RetainedState support sequence.builtin.completion.session [first, named, builtin],
      ∃ finalState : RetainedState support sequence.converted.completion.session [first, named, builtin],
        namedState.heap = firstState.heap ∧ builtinState.heap = readState.heap ∧
        SourceCall support support.makeHeader.header scope ⟨[]⟩ [.word seed] (.value first.source) firstState.heap ∧
        SourceInvocation support scope namedState.heap named.source first.source seed readState.heap ∧
        SourceInvocation support scope builtinState.heap builtin.source (.integer builtinArgument)
          builtinResult finalState.heap ∧
        ForwardWordAt support sequence.named.completion.session [first, named] sequence.named.handle
          (.function sequence.first.handle) seed readState.heap ∧
        ForwardWordAt support sequence.builtin.completion.session [first, named, builtin] sequence.builtin.handle
          (.integer builtinArgument) builtinResult finalState.heap

/-- The real named and builtin calls establish independent Source traces,
then prove public success for all sufficient fuel on those same checkpoints. -/
theorem sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    ForwardSequenceMeaning makeStages sequence receiver := by
  obtain ⟨support, first, named, builtin, firstType, namedType, builtinType,
    firstHandle, namedHandle, builtinHandle, namedSource, builtinSource,
    firstState, namedState, readState, builtinState, finalState, namedHeap, builtinHeap,
    firstTrace, readTrace, finalTrace⟩ := sequence_meaning fixture observed extra makeStages readStages sequence receiver
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input [first, named]
      support.makeHeader.header.function.context (.function .unit .word)
      (.function sequence.first.handle) first.source := by
    simpa only [firstType, firstHandle] using
      (RecursiveNamedPublicFunctionHistoryInputs.Input.retained
        (context := support.makeHeader.header.function.context) first (by simp : first ∈ [first, named]))
  have integerInput : RecursiveNamedPublicFunctionHistoryInputs.Input [first, named, builtin]
      support.makeHeader.header.function.context .integer (.integer builtinArgument) (.integer builtinArgument) :=
    .data ⟨.integer builtinArgument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer builtinArgument⟩
      ⟨.integer builtinArgument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer builtinArgument⟩
  exact ⟨support, first, named, builtin, firstType, namedType, builtinType,
    firstHandle, namedHandle, builtinHandle, namedSource, builtinSource,
    firstState, namedState, readState, builtinState, finalState, namedHeap, builtinHeap,
    firstTrace, readTrace, finalTrace,
    forward_word namedState named (by simp) namedType namedHandle input (.function sequence.first.handle)
      sequence.read readTrace,
    forward_word builtinState builtin (by simp) builtinType builtinHandle integerInput (.simple (.integer builtinArgument))
      sequence.converted finalTrace⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let readStages ← observeStages fixture observed.readRow
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_forward_meaning fixture observed extra makeStages readStages sequence receiver
  IO.println "Actual direct named and builtin calls: Source reflection and public Word preservation with output fuel 1 proved"

end Tests.SourceCoreDirectIssued
