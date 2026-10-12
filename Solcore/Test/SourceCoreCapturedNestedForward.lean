import Solcore.Test.SourceCoreCapturedNestedPublicExecution
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputPreservation

/-! The three collected-handle calls establish independent Source traces.
Those traces imply actual public export on their original starts at every
sufficient execution and output-validation budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedNested
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def ForwardWordAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle)
    (word : Core.Word) (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
    publicSession.startHandlePacked handle .unit runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ requiredExecution requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ completion : SourceCoreExecution.Completion publicArtifact,
          outcome = .succeeded completion ∧ completion.value = .word word ∧ completion.session.ExportsReady ∧
          ∃ returned : RetainedState support completion.session entries, returned.heap = after

theorem forward_word {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    (entryType : entry.sourceType = .function .unit .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function .unit .word)
    {word : Core.Word}
    (call : ObservedInvocation publicSession handle .unit)
    (exportsReady : publicSession.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceInvocation support invocation state.heap entry.source (.value (.word word)) after) :
    ForwardWordAt support publicSession entries handle word after := by
  have unitInput : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context .unit .unit .unit :=
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
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
      unitInput state.registry (state.atSession.exportsReady_iff.mp exportsReady)
      started .nil trace atCheckpoint
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

/-- Collected-call Source traces imply export at all sufficient budgets
on their original starts, with the same Source heap and reusable history. -/
theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) :
    ForwardWordAt meaning.support sequence.echo.completion.session
        ([meaning.first, meaning.second, meaning.named] ++ meaning.added)
        sequence.echo.firstOutput seed meaning.firstReadState.heap ∧
    ForwardWordAt meaning.support sequence.intervening.completion.session
        (([meaning.first, meaning.second, meaning.named] ++ meaning.added) ++ [meaning.intervening])
        sequence.echo.secondOutput secondSeed meaning.secondReadState.heap ∧
    ForwardWordAt meaning.support sequence.secondRead.completion.session
        (([meaning.first, meaning.second, meaning.named] ++ meaning.added) ++ [meaning.intervening])
        sequence.echo.repeatedOutput seed meaning.finalState.heap := by
  have initialReady := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have issuedReady := sequence.named.issued.exportsReady secondReady
  have echoReady := sequence.echo.executed.exportsReady issuedReady
  have firstReadReady := sequence.firstRead.executed.exportsReady echoReady
  have interveningReady := sequence.intervening.executed.exportsReady firstReadReady
  have secondReadReady := sequence.secondRead.executed.exportsReady interveningReady
  have firstMember : meaning.collected.firstEntry ∈ [meaning.first, meaning.second, meaning.named] ++ meaning.added := by
    simp [meaning.collected.ordered]
  have secondMember : meaning.collected.secondEntry ∈
      ([meaning.first, meaning.second, meaning.named] ++ meaning.added) ++ [meaning.intervening] := by
    simp [meaning.collected.ordered]
  have repeatedMember : meaning.collected.repeatedEntry ∈
      ([meaning.first, meaning.second, meaning.named] ++ meaning.added) ++ [meaning.intervening] := by
    simp [meaning.collected.ordered]
  exact ⟨forward_word meaning.collectedState meaning.collected.firstEntry firstMember
      meaning.collected.firstType meaning.collected.firstHandle
      ((congrArg SourceCorePublicValues.Handle.sourceType sequence.echo.firstSame).trans meaning.firstHandleType) sequence.firstRead echoReady meaning.firstReadTrace,
    forward_word meaning.interveningState meaning.collected.secondEntry secondMember
      meaning.collected.secondType meaning.collected.secondHandle
      ((congrArg SourceCorePublicValues.Handle.sourceType sequence.echo.secondSame).trans meaning.secondHandleType) sequence.secondRead interveningReady meaning.secondReadTrace,
    forward_word meaning.secondReadState meaning.collected.repeatedEntry repeatedMember
      meaning.collected.repeatedType meaning.collected.repeatedHandle
      ((congrArg SourceCorePublicValues.Handle.sourceType sequence.echo.repeatedSame).trans meaning.firstHandleType) sequence.repeatedRead secondReadReady meaning.repeatedReadTrace⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let readStages ← observeStages fixture observed.readRow
  let sequence ← observeSequence fixture observed
  have _meaning : ∃ receiver : ObservedReceiver fixture observed,
      ∃ meaning : SequenceWitness makeStages sequence receiver,
        ForwardWordAt meaning.support sequence.echo.completion.session
          ([meaning.first, meaning.second, meaning.named] ++ meaning.added)
          sequence.echo.firstOutput seed meaning.firstReadState.heap := by
    obtain ⟨receiver, meaning⟩ := closed_sequence_meaning fixture observed extra makeStages readStages sequence
    obtain ⟨meaning⟩ := meaning
    exact ⟨receiver, meaning, meaning.forward.1⟩
  IO.println "Nested output collection: ordered duplicate mapping rows, captures 10/20/10, Source traces, sufficient-fuel export and exact histories proved"

end Tests.SourceCoreCapturedNested
