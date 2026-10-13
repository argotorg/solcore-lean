import Solcore.Test.SourceCoreEvidenceClosureInitialForward
import Solcore.Test.SourceCoreEvidenceClosureInvocationForward
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation

/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry} {key : SourceCoreIndexedSession.Key}
    {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key publicArguments) (resultType : TypeSystem.Ty)
    (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧
        completion.session.ExportsReady ∧ ReturnedHistory support completion entries resultType source after outputFuel

theorem forward_make {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key publicArguments) (ready : session.ExportsReady)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.rows) fixture.recipePrepared
      call.checkpoint state.session key publicArguments runOptions.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value} {resultType : TypeSystem.Ty}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (resultTypeEq : request.header.function.resultType = closureType resultType)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support request.header invocation state.heap
      arguments (.value source) after) :
    ForwardAt (entries := entries) support call resultType source after := by
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
      (inputs := [support.wordInput, support.boolInput, support.factoryWordInput, support.factoryBoolInput, support.chooseWordInput, support.chooseBoolInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family)
      (namedTerminals := support.bodies) (namedSupport := support.supports)
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
  have rootResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [rootResult] at requested
  have requestedRaw := requested
  rw [resultTypeEq] at requested
  have checkpointReady := request.started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp ready)
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, _reached, succeeded, exported, actualAt,
      _related, _history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound (Nat.le_trans (Nat.le_max_left _ _) outputBound) resumed
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded request.atCheckpoint resumed checkpointReady
      (_nativeEnough executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion := SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  let entry : RecursiveNamedPublicFunctionHistory.Entry :=
    ⟨request.header.function.resultType, source, handle, payload, request.header.output, outputFuel⟩
  obtain ⟨returnedCaller, related, post⟩ := fullResult.2.2.2.2.2.2.2
  have prior := RecursiveNamedPublicHistoryRegistryExtension.extend_history state.history extended
  have retained := RecursiveNamedPublicFunctionHistory.History.next prior rfl request.started request.selected
    exported fullResult returnedCaller ⟨related, post⟩
    (.remember requestedRaw rfl rfl (actualAt.1.symm.trans functionValue))
  let returned : RetainedState support completion.session (entries ++ [entry]) := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := returnedCaller
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := retained }
  have represented : CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked receiving.result.context.registry
      support.functions finalMap finalWorld (closureType resultType) source payload request.header.output := by
    have result := fullResult.2.1
    rw [resultTypeEq] at result
    cases result with | value represented => exact represented
  have encoded := (exported.reimports_payload requested rfl).2
  rw [← actualAt.1] at encoded
  exact ⟨completion, succeeded, actualAt.2.2.2.exportsReady_iff.mpr returnedReady,
    entry, resultTypeEq, rfl, functionValue, handleType, returned, rfl, payload, _, encoded, represented⟩


/-- The three factory executions derive bounds from their independent Source traces. -/
def ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages sequence receiver) : Prop :=
  InitialForwardAt meaning.support sequence.first meaning.first.source meaning.initial.heap ∧
  ForwardAt (entries := [meaning.first]) meaning.support sequence.second .bool meaning.second.source meaning.secondState.heap ∧
  ForwardAt (entries := [meaning.first, meaning.second]) meaning.support sequence.third .word
    meaning.third.source meaning.thirdState.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages sequence receiver) : ForwardMeaning meaning := by
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady ready
  have secondReady := sequence.second.executed.exportsReady firstReady
  have readReady := sequence.firstRead.executed.exportsReady secondReady
  let support := meaning.support
  obtain ⟨secondRequest⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.wordInput, support.boolInput, support.factoryWordInput,
      support.factoryBoolInput, support.chooseWordInput, support.chooseBoolInput] support.rows support.complete
    meaning.initial.atRecipe meaning.initial.history.current.1 meaning.initial.atSession sequence.second.started
  have secondHeader := selected_bool_at support.wordHeader support.boolHeader support.factoryWordHeader
    support.factoryBoolHeader support.chooseWordHeader support.chooseBoolHeader support.header_list secondRequest
  have secondInputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [meaning.first] secondRequest.header.function.context
      (secondRequest.header.bindings.map (fun binding => binding.1.scheme.body))
      [.bool false, .word (Core.Word.ofNatModulo 22)] [.bool false, .word (Core.Word.ofNatModulo 22)] := by
    rw [secondHeader, support.boolHeader.bool_input_types]
    exact bool_word_inputs false _
  have secondResult : secondRequest.header.function.resultType = closureType .bool := by
    rw [secondHeader]; exact support.boolHeader.bool_result_type
  have secondTrace : SourceCall support secondRequest.header
      (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
      meaning.initial.heap [.bool false, .word (Core.Word.ofNatModulo 22)] (.value meaning.second.source) meaning.secondState.heap := by
    rw [secondHeader]; exact meaning.secondTrace
  obtain ⟨thirdRequest⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.wordInput, support.boolInput, support.factoryWordInput,
      support.factoryBoolInput, support.chooseWordInput, support.chooseBoolInput] support.rows support.complete
    meaning.firstReadState.atRecipe meaning.firstReadState.history.current.1 meaning.firstReadState.atSession sequence.third.started
  have thirdHeader := selected_word_at support.wordHeader support.boolHeader support.factoryWordHeader
    support.factoryBoolHeader support.chooseWordHeader support.chooseBoolHeader support.header_list thirdRequest
  have thirdInputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [meaning.first, meaning.second] thirdRequest.header.function.context
      (thirdRequest.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word (Core.Word.ofNatModulo 33), .bool false] [.word (Core.Word.ofNatModulo 33), .bool false] := by
    rw [thirdHeader, support.wordHeader.word_input_types]
    exact word_bool_inputs _ false
  have thirdResult : thirdRequest.header.function.resultType = closureType .word := by
    rw [thirdHeader]; exact support.wordHeader.word_result_type
  have thirdTrace : SourceCall support thirdRequest.header
      (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
      meaning.firstReadState.heap [.word (Core.Word.ofNatModulo 33), .bool false] (.value meaning.third.source) meaning.thirdState.heap := by
    rw [thirdHeader]; exact meaning.thirdTrace
  exact ⟨forward_initial support sequence.first meaning.firstTrace,
    forward_make meaning.initial sequence.second firstReady secondRequest secondInputs secondResult secondTrace,
    forward_make meaning.firstReadState sequence.third readReady thirdRequest thirdInputs thirdResult thirdTrace⟩

theorem closed_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedFactories fixture observed)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (factoryWordStages : ObservedStages fixture observed.factoryWordRow)
    (factoryBoolStages : ObservedStages fixture observed.factoryBoolRow)
    (chooseWordStages : ObservedStages fixture observed.chooseWordRow)
    (chooseBoolStages : ObservedStages fixture observed.chooseBoolRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      ∃ meaning : SequenceWitness wordStages boolStages sequence receiver,
        ForwardMeaning meaning ∧ InvocationForwardMeaning meaning := by
  obtain ⟨receiver, meaning⟩ := closed_sequence_meaning fixture observed extra wordStages boolStages factoryWordStages
    factoryBoolStages chooseWordStages chooseBoolStages sequence
  obtain ⟨meaning⟩ := meaning
  exact ⟨receiver, meaning, meaning.forward, meaning.invocations_forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeFactories fixture observed
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let factoryWordStages ← observeStages fixture observed.factoryWordRow
  let factoryBoolStages ← observeStages fixture observed.factoryBoolRow
  let chooseWordStages ← observeStages fixture observed.chooseWordRow
  let chooseBoolStages ← observeStages fixture observed.chooseBoolRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_forward_meaning fixture observed extra wordStages boolStages factoryWordStages
    factoryBoolStages chooseWordStages chooseBoolStages sequence
  IO.println "Evidence closure PASS: Aword11/Bboolfalse/A11/Cword33/Bfalse/A11/C33, three distinct handles, exact Source heaps/history, all seven public fuel bounds proved"
end Tests.SourceCoreEvidenceClosure
