import Solcore.Test.SourceCoreConstructorCallsPublicExecution
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollectionPreservation

/-! Independent Source success also implies public nominal-constructor export and ordered
nested collection for every sufficient execution and output fuel budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicNestedOutputSelections (Selection Selected)

def SelectedAt {fixture : CompiledFixture} {publicArtifact : SourceCoreExecution.Artifact}
    (completion : SourceCoreExecution.Completion publicArtifact)
    (selection : Selection (containerType fixture.dataType) completion.value) (source : Dynamic.Value)
    (outputFuel : Nat) (added : List Entry) : Prop :=
  ∃ (artifact : SourceCoreIndexedSession.Artifact) (actual : SourceCoreIndexedSession.Completion artifact)
    (native : Core.Value) (type : Core.Ty), completion.IndexedAt actual ∧
    Selected fixture.recipe.compiled.compatible.checked actual.session selection source native type outputFuel added

def ForwardCollectionAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint artifact,
    session.startHandlePacked handle argument runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ requiredExecution requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ completion : SourceCoreExecution.Completion artifact,
          outcome = .succeeded completion ∧ completion.session.ExportsReady ∧
          ∀ selection : Selection (containerType fixture.dataType) completion.value,
            ∃ (added : List Entry) (next : RetainedState support completion.session (entries ++ added)),
              next.heap = after ∧ added.map Entry.handle = selection.handles ∧
              SelectedAt (fixture := fixture) completion selection source outputFuel added

theorem SequenceWitness.forward_collection {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) :
    ForwardCollectionAt meaning.support sequence.named.completion.session
      [meaning.first, meaning.factory, meaning.builtin, meaning.named]
      sequence.named.handle (packedArgument sequence.factory.handle sequence.first.handle sequence.builtin.handle)
      meaning.source meaning.collectedState.heap := by
  let state := meaning.issuedState
  have initialReady := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have factoryReady := sequence.factory.issued.exportsReady firstReady
  have builtinReady := sequence.builtin.issued.exportsReady factoryReady
  have exportsReady := sequence.named.issued.exportsReady builtinReady
  obtain ⟨publicCheckpoint, accepted, _resumed⟩ := sequence.construction.executed
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have member : meaning.named ∈ [meaning.first, meaning.factory, meaning.builtin, meaning.named] := by simp
  have imported := (state.history.current.2.2.2.2 meaning.named member).1
  rw [meaning.namedType, meaning.namedHandle] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.current.1 imported original
  rw [← meaning.namedHandle] at started
  have input := construction_input
    (entries := [meaning.first, meaning.factory, meaning.builtin, meaning.named])
    (context := meaning.support.makeHeader.header.function.context)
    meaning.factory meaning.first meaning.builtin (by simp) (by simp) (by simp)
    meaning.factoryType meaning.firstType meaning.builtinType meaning.factoryHandle meaning.firstHandle meaning.builtinHandle
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨sources, size, packing, trace⟩ := meaning.constructionTrace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, requiredExecution, requiredOutput,
      payload, finalStore, finalMap, finalWorld, _enough, _fullResult, resumes⟩ :=
    RecursiveNamedPublicActualRegistryOutputCollectionPreservation.public_resume_has_sufficient_fuel
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      meaning.support.observations semantic meaning.support.family
      (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (meaning.support.terminals header member))
      meaning.support.supports fixture.source_wellFormed state.history meaning.named member meaning.namedType input
      state.atRecipe state.registry (state.atSession.exportsReady_iff.mp exportsReady)
      started packing trace atCheckpoint
  refine ⟨publicCheckpoint, accepted, requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome enoughExecution enoughOutput resumed
  obtain ⟨completion, actual, _generation, success, _exported, atCompletion, returnedRegistry, returnedReady, selections⟩ :=
    resumes executionFuel outputFuel outcome enoughExecution enoughOutput resumed
  refine ⟨completion, success, atCompletion.2.2.2.exportsReady_iff.mpr returnedReady, ?_⟩
  intro selection
  obtain ⟨reached, added, selected, handles, _related, history⟩ := selections selection
  let next : RetainedState meaning.support completion.session
      ([meaning.first, meaning.factory, meaning.builtin, meaning.named] ++ added) := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := meaning.collectedState.heap
    store := finalStore
    caller := reached
    atSession := atCompletion.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := history }
  exact ⟨added, next, rfl, handles, state.artifact, actual, payload, nativeResult, atCompletion, selected⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let readStages ← observeStages fixture observed.readRow
  let sequence ← observeSequence fixture observed
  have _meaning : ∃ receiver : ObservedReceiver fixture observed,
      ∃ meaning : SequenceWitness makeStages sequence receiver,
        ForwardCollectionAt meaning.support sequence.named.completion.session
          [meaning.first, meaning.factory, meaning.builtin, meaning.named]
          sequence.named.handle (packedArgument sequence.factory.handle sequence.first.handle sequence.builtin.handle)
          meaning.source meaning.collectedState.heap := by
    obtain ⟨receiver, witness⟩ := closed_sequence_meaning fixture observed extra makeStages readStages sequence
    obtain ⟨witness⟩ := witness
    exact ⟨receiver, witness, witness.forward_collection⟩
  IO.println "Constructor recursive child and payload collection: independent Source meaning, sufficient public fuel, retained callable reuse20/30export/10/37 proved"

end Tests.SourceCoreConstructorCalls
