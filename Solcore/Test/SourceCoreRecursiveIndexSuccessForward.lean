import Solcore.Test.SourceCoreRecursiveIndexInitialForward
import Solcore.Test.SourceCoreRecursiveIndexInputs
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation

/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry} {key : SourceCoreIndexedSession.Key}
    {arguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key arguments)
    (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧
        ∃ handle, completion.value = .function handle ∧ handle.sourceType = closureType ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session entries, returned.heap = after ∧
          ReturnedValue completion returned source outputFuel

theorem forward_make {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support session entries) {value : Core.Word}
    (call : ObservedFunctionCall session observed.makeRow.row.key [.word value]) (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support support.makeHeader.header invocation state.heap
      [.word value] (.value source) after) :
    ForwardAt (entries := entries) support call source after := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.makeInput, support.echoInput, support.chooseInput, support.selectInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader := selected_make_at support.makeHeader support.echoHeader support.chooseHeader support.selectHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word value] [.word value] := by
    rw [selectedHeader, support.makeHeader.make_input_types_source]
    exact .cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
      ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  have sourceAt' : CallableIndexedOwnedFunctionValues.NamedSourceAt request.header rawD function := by
    rw [selectedHeader]; exact sourceAt
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _capture,
      payload, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryNamedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.makeInput, support.echoInput, support.chooseInput, support.selectInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family)
      (namedTerminals := fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (atRegistry := state.registry)
      (exportsReady := state.atSession.exportsReady_iff.mp ready) (sourceAt := sourceAt') applied
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.makeHeader.make_result_type] at requested
  have checkpointReady := request.started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp ready)
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound (Nat.le_trans (Nat.le_max_left _ _) outputBound) resumed
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
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded request.atCheckpoint resumed checkpointReady
      (_nativeEnough executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion := SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  have represented : CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked receiving.result.context.registry
      support.functions finalMap finalWorld closureType source payload request.header.output := by
    have result := fullResult.2.1
    have rawType : request.header.function.resultType = closureType := by rw [selectedHeader]; exact support.makeHeader.make_result_type
    rw [rawType] at result
    cases result with | value represented => exact represented
  have encoded := (exported.reimports_payload requested rfl).2
  rw [← actualAt.1] at encoded
  exact ⟨completion, succeeded, handle, functionValue, handleType,
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl, payload, _, encoded, represented⟩


theorem forward_select {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support session entries)
    (first second : RecursiveNamedPublicFunctionHistory.Entry)
    (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle)
    {key : Core.Word}
    (call : ObservedFunctionCall session observed.selectRow.row.key [table firstHandle secondHandle, .word key])
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support support.selectHeader.header invocation state.heap
      [sourceTable first second, .word key] (.value source) after) :
    ForwardAt (entries := entries) support call source after := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.makeInput, support.echoInput, support.chooseInput, support.selectInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader := selected_select_at support.makeHeader support.echoHeader support.chooseHeader support.selectHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [table firstHandle secondHandle, .word key] [sourceTable first second, .word key] := by
    rw [selectedHeader, support.selectHeader.select_input_types_source]
    exact select_inputs first second firstMember secondMember firstType secondType firstHandleEq secondHandleEq key
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  have sourceAt' : CallableIndexedOwnedFunctionValues.NamedSourceAt request.header rawD function := by
    rw [selectedHeader]; exact sourceAt
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _capture,
      payload, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryNamedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.makeInput, support.echoInput, support.chooseInput, support.selectInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family)
      (namedTerminals := fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (atRegistry := state.registry)
      (exportsReady := state.atSession.exportsReady_iff.mp ready) (sourceAt := sourceAt') applied
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.selectHeader.select_result_type] at requested
  have checkpointReady := request.started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp ready)
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound (Nat.le_trans (Nat.le_max_left _ _) outputBound) resumed
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
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded request.atCheckpoint resumed checkpointReady
      (_nativeEnough executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion := SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  have represented : CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked receiving.result.context.registry
      support.functions finalMap finalWorld closureType source payload request.header.output := by
    have result := fullResult.2.1
    have rawType : request.header.function.resultType = closureType := by rw [selectedHeader]; exact support.selectHeader.select_result_type
    rw [rawType] at result
    cases result with | value represented => exact represented
  have encoded := (exported.reimports_payload requested rfl).2
  rw [← actualAt.1] at encoded
  exact ⟨completion, succeeded, handle, functionValue, handleType,
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl, payload, _, encoded, represented⟩


end Tests.SourceCoreRecursiveIndex
