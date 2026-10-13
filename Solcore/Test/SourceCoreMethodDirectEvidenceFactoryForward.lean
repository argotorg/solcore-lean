import Solcore.Test.SourceCoreMethodDirectEvidenceStep
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation

/-! Independent Source success supplies sufficient native and output fuel at
the original public checkpoint. Every sufficient resume retains the full
physical cache and the same Source heap and prior history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodDirectEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def FactoryForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key arguments)
    (resultType : TypeSystem.Ty) (source : Dynamic.Value)
    (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.session.ExportsReady ∧
        ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
          entry.sourceType = closureType resultType ∧ entry.source = source ∧
          completion.value = .function entry.handle ∧ entry.handle.sourceType = closureType resultType ∧
          ∃ returned : RetainedState inventory receiver completion.session (entries ++ [entry]),
            returned.heap = after

theorem forward_factory {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {inventory : OrdinaryInventory fixture observed} {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState inventory receiver session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key publicArguments)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers inventory.rows) fixture.recipePrepared
      call.checkpoint state.session key publicArguments runOptions.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    {resultType : TypeSystem.Ty}
    (rawType : request.header.function.resultType = closureType resultType)
    (ready : session.ExportsReady)
    (packet : CallableIndexedOwnedPreparedStagedNamedBodies.Body request.header)
    (preservesBodies : ∀ budget {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).Closure request.header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
        (headers := headers inventory.rows) (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        request.header (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked
          state.receiving.result.context.registry (inventory.functions receiver))
        (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) child
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics) budget)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall inventory request.header invocation state.heap arguments (.value source) after) :
    FactoryForwardAt (entries := entries) inventory receiver call resultType source after := by
  have registry := request.started.simple_registry state.registry simple
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    RecursiveNamedPublicPhysicalClosureHistory.History.current_arguments
      (profile := observed.profile)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (history := state.history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    inventory.rows request.header request.selected.member
  have supports := (RecursiveNamedPublicReturnedValues.header_context_supports
    request.header inventory.wordHeader.header fixture.source_wellFormed).2
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    CallableIndexedOwnedPreparedStagedPhysicalBodyPublicInvocationBounds.preserves_root
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (functions := inventory.functions receiver)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled)
      (packet := packet) (preservesBodies := preservesBodies)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := state.history.physical)
      (wellFormed := fixture.source_wellFormed)
      (selected := request.selected) (caller := state.caller)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := supports) applied
  obtain ⟨payload, rfl⟩ : ∃ payload, value = .inRight .word payload := by
    have representedResult := result.2.1
    cases representedResult with
    | value represented => exact ⟨_, rfl⟩
  have completes : ∀ executionFuel, requiredExecution ≤ executionFuel →
      request.checkpoint.NativeDone executionFuel (.inRight .word payload) finalStore :=
    fun fuel bound => request.started.initial.native_done_iff.mpr (enough fuel bound)
  have representedResult : CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked
      state.receiving.result.context.registry (inventory.functions receiver)
      finalMap finalWorld request.header.function.resultType source payload request.header.output := by
    have representedResult := result.2.1
    cases representedResult with
    | value related => exact related
  have shape : SourceCorePublicOutputShapes.Output fixture.recipe.compiled.compatible.checked request.encodedValues.registry
      (finalStore.map Core.Value.type) fixture.recipe.program.layouts.definitions request.header.function.resultType payload := by
    have shaped := CompatiblePublicOutputShapes.ValueRep.output representedResult
    rw [← registry] at shaped
    rw [result.2.2.1.runtime_hasTypes.world_eq] at shaped
    exact shaped
  have checkpointRegistry : request.checkpoint.RegistryAt request.encodedValues.registry := by
    have atValues := request.started.values
    generalize checkpointEq : request.checkpoint = checkpoint at atValues ⊢
    cases checkpoint
    change _ = request.encodedValues at atValues
    exact congrArg SourceCoreCompatibleValues.Context.registry atValues
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have selectedResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [selectedResult] at requested
  have checkpointReady := request.started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp ready)
  obtain ⟨requiredOutput, exports⟩ := call.checkpoint.output_succeeded_uniform
    request.atCheckpoint atRecipe checkpointRegistry checkpointReady requested shape
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, generation, succeeded, exported, actualAt, returnedReady⟩ :=
    exports executionFuel (completes executionFuel executionBound) outputFuel (Nat.le_trans (Nat.le_max_left _ _) outputBound) outcome resumed
  have requestedRaw := requested
  rw [rawType] at requested
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded request.atCheckpoint resumed checkpointReady
      (completes executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion :=
    SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  let entry : RecursiveNamedPublicFunctionHistory.Entry :=
    ⟨request.header.function.resultType, source, handle, payload, request.header.output, outputFuel⟩
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.next state.history.semantic
    rfl request.started request.selected exported result reached ⟨related, post⟩
    (.remember requestedRaw rfl rfl (actualAt.1.symm.trans functionValue))
  have physicalRetained := state.history.after_result result retained
  have returnedRegistry := request.started.returned_registry exported
  rw [registry] at returnedRegistry
  let returned : RetainedState inventory receiver completion.session (entries ++ [entry]) := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := returnedRegistry
    history := physicalRetained }
  exact ⟨completion, succeeded, actualAt.2.2.2.exportsReady_iff.mpr returnedReady,
    entry, rawType, rfl, functionValue, handleType, returned, rfl⟩

end Tests.SourceCoreMethodDirectEvidence
