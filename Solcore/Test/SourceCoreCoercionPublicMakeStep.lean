import Solcore.Test.SourceCoreCoercionPublicCommon
import Solcore.Test.SourceCoreCoercionPublicResults
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalBodyPublicInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedHistoryPublicBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticExtension
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryRegistryExtension

/-! Actual factory calls append their freshly exported closures to the same physical history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem RetainedState.make_typed_handle {fixture : CompiledFixture} {observed : ObservedProgram fixture}
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
    (descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key))
    (packet : CallableIndexedOwnedPreparedStagedNamedBodies.Body request.header)
    (reflectsBodies : ∀ budget {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).Closure request.header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
        (headers := headers inventory.rows) (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        request.header (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked
          state.receiving.result.context.registry (inventory.functions receiver))
        (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) child
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics) budget)
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
      entry.sourceType = request.header.function.resultType ∧ entry.handle = call.handle ∧
      call.handle.sourceType = request.header.function.resultType ∧
      ∃ after : RetainedState inventory receiver call.completion.session (entries ++ [entry]),
        SourceCall inventory request.header invocation state.heap arguments
          (.value entry.source) after.heap := by
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
    request.header inventory.makeHeader.header fixture.source_wellFormed).2
  obtain ⟨actual, generation, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result⟩ :=
    CallableIndexedOwnedPreparedStagedPhysicalBodyPublicInvocationBounds.public_run_succeeded_reflects
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (functions := inventory.functions receiver)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled)
      (packet := packet) (reflectsBodies := reflectsBodies)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := state.history.physical)
      (wellFormed := fixture.source_wellFormed)
      (selected := request.selected) (caller := state.caller)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := request.sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled fixture.recipePrepared)
      (started := request.started) (invocation := invocation)
      call.started request.atCheckpoint call.executed descriptor
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType] at requested
  obtain ⟨reached, source, payload, sourceValue, _nativeValue, _related, retained⟩ :=
    state.history.semantic.remember_success rfl request.started request.selected requested succeeded result
      (valueEq.symm.trans call.returned)
  have physicalRetained := state.history.after_result result retained
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans call.returned)
  let entry : RecursiveNamedPublicFunctionHistory.Entry :=
    ⟨request.header.function.resultType, source, call.handle, payload, request.header.output,
      runOptions.outputValidationFuel⟩
  have returnedRegistry := request.started.returned_registry succeeded
  rw [registry] at returnedRegistry
  let next : RetainedState inventory receiver call.completion.session (entries ++ [entry]) := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := returnedRegistry
    history := physicalRetained }
  exact ⟨entry, rfl, rfl, handleType, next, request.rawD, request.function, sourceSize, request.sourceAt, sourceValue ▸ trace⟩

end Tests.SourceCoreCoercionPublic
