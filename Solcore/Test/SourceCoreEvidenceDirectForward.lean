import Solcore.Test.SourceCoreEvidenceDirectInitialForward
import Solcore.Test.SourceCoreEvidenceDirectPublicExecution
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation

/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreEvidenceDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key arguments scalar.publicValue)
    (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.value = scalar.publicValue ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session entries, returned.heap = after

theorem forward_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments scalar.publicValue)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.rows) fixture.recipePrepared
      call.checkpoint state.session key publicArguments runOptions.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall support request.header invocation state.heap arguments (.value scalar.source) after) :
    ForwardAt (entries := entries) support scalar call after := by
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _capture,
      payload, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryNamedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.wordInput, support.boolInput, support.relayWordInput, support.relayBoolInput, support.chooseWordInput, support.chooseBoolInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family)
      (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (atRegistry := state.registry)
      (exportsReady := state.atSession.exportsReady_iff.mp ready) (sourceAt := sourceAt) applied
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, rawType] at requested
  have nativeScalar : payload = scalar.native := by
    have represented := fullResult.2.1
    rw [nativeType] at represented
    cases represented with
    | value related => exact scalar.native_value related
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
  let returned : RetainedState support completion.session entries := {
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
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  exact ⟨completion, succeeded, actualAt.1.trans (scalar.succeeded_value (nativeScalar ▸ exported) requested),
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩

theorem CallMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {before : RetainedState support session []}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {scalar : ScalarOutput} {call : ObservedCall session key publicArguments scalar.publicValue}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : CallMeaning before header scalar call arguments invocation)
    (ready : session.ExportsReady) : ForwardAt (entries := []) support scalar call meaning.after.heap := by
  apply forward_call before scalar call meaning.request meaning.inputs meaning.rawType meaning.nativeType ready
  rw [meaning.headerEq]
  exact meaning.trace

structure ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages sequence receiver) : Prop where
  first : InitialForwardAt meaning.support sequence.first meaning.initial.heap
  second : ForwardAt (entries := []) meaning.support (.bool false) sequence.second meaning.secondMeaning.after.heap
  third : ForwardAt (entries := []) meaning.support (.word (Core.Word.ofNatModulo 33)) sequence.third meaning.thirdMeaning.after.heap
  fourth : ForwardAt (entries := []) meaning.support (.bool true) sequence.fourth meaning.fourthMeaning.after.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages sequence receiver) : ForwardMeaning meaning := by
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 100000 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have thirdReady := sequence.third.executed.exportsReady secondReady
  exact ⟨forward_initial meaning.support sequence.first meaning.firstTrace,
    meaning.secondMeaning.forward firstReady,
    meaning.thirdMeaning.forward secondReady,
    meaning.fourthMeaning.forward thirdReady⟩

theorem closed_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (relayWordStages : ObservedStages fixture observed.relayWordRow)
    (relayBoolStages : ObservedStages fixture observed.relayBoolRow)
    (chooseWordStages : ObservedStages fixture observed.chooseWordRow)
    (chooseBoolStages : ObservedStages fixture observed.chooseBoolRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed)
      (meaning : SequenceWitness wordStages boolStages sequence receiver), ForwardMeaning meaning := by
  obtain ⟨receiver, ⟨meaning⟩⟩ := closed_sequence_meaning fixture observed wordStages boolStages
    relayWordStages relayBoolStages chooseWordStages chooseBoolStages sequence
  exact ⟨receiver, meaning, meaning.forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let relayWordStages ← observeStages fixture observed.relayWordRow
  let relayBoolStages ← observeStages fixture observed.relayBoolRow
  let chooseWordStages ← observeStages fixture observed.chooseWordRow
  let chooseBoolStages ← observeStages fixture observed.chooseBoolRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_forward_meaning fixture observed wordStages boolStages relayWordStages relayBoolStages chooseWordStages chooseBoolStages sequence
  IO.println "Evidence direct calls: Word11, BoolFalse, Word33, BoolTrue; four Source histories and sufficient public fuel proved"

end Tests.SourceCoreEvidenceDirect
