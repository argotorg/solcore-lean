import Solcore.Test.SourceCoreCoercionPublicCommon
import Solcore.Test.SourceCoreCoercionPublicResults
import Solcore.Test.SourceCoreCoercionPublicSelection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalBodyPublicInvocationBounds

/-! The initial method-bearing public call connects its actual bootstrap and input
encoding to the Source result and the full returned physical cache. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem first_meaning_typed_handle {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (inventory : OrdinaryInventory fixture observed)
    (distinct : ([inventory.makeInput, inventory.useInput, inventory.keepInput].map (fun input => input.prepared.index)).Nodup)
    (packet : CallableIndexedOwnedPreparedStagedNamedBodies.Body inventory.makeHeader.header)
    (reflectsBodies : ∀ budget {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).Closure inventory.makeHeader.header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
        (headers := headers inventory.rows) (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        inventory.makeHeader.header (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked
          receiver.completion.result.context.registry (inventory.functions receiver))
        (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) child
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiver.completion.result.diagnostics) budget) (stages : ObservedStages fixture observed.makeRow.toObservedRow)
    (first : ObservedPublicRun fixture observed.makeRow.toObservedRow) :
    ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
      entry.sourceType = closureType .word ∧ entry.handle = first.handle ∧
      ∃ state : RetainedState inventory receiver first.completion.session [entry],
        SourceCall inventory inventory.makeHeader.header
          (RecursiveStageRegistry.scope stages.sidecar [] inventory.makeHeader.header.function)
          ⟨[]⟩ [.bool true] (.value entry.source) state.heap := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := fixture.actual_start first.opened first.started
  have ready : first.bootstrap.ReadyAt 102400 first.session := .single first.ready
  obtain ⟨_bootstrap, initialized, _value, _initialStore, _atBootstrap, initial,
      initializedAt, _done, booted⟩ := ready.indexed opened first.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  have startupRegistry : encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
    apply started.simple_registry (booted.registry_at initial)
    exact bool_simple true
  have selected := inventory.selected_row_issued observed.makeRow.toObservedRow
    inventory.makeHeader inventory.make_member inventory.makeSlot
    (SourceCoreIndexedSession.Recipe.prepare_roots prepared (List.mem_of_find?_eq_some started.selected))
    (of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
      decide (candidate.key = observed.makeRow.row.key)) started.selected))
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      inventory.makeHeader.header.function.context [.bool true] inventory.makeHeader.header.types := by
    rw [inventory.makeHeader.make_types]
    exact .cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool true] [.bool true] :=
    .cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt inventory.makeHeader.header inventory.makeInput.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global inventory.makePacket.header.named.specialized inventory.makeInput.prepared.available)) := by
    rw [inventory.makeAligned]
    exact inventory.makePacket.sourceAt
  obtain ⟨physicalCaller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedPhysicalClosureArguments.initial_data_arguments
      (inputs := [inventory.makeInput, inventory.useInput, inventory.keepInput])
      (rows := inventory.rows) (distinct := distinct)
      (profile := observed.profile) (completion := receiver.completion)
      (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (started := started) (inputTypes := inputTypes) (inputMeanings := inputMeanings) (metadata := metadata)
  have supports := (RecursiveNamedPublicReturnedValues.header_context_supports
    inventory.makeHeader.header inventory.makeHeader.header fixture.source_wellFormed).2
  obtain ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result⟩ :=
    CallableIndexedOwnedPreparedStagedPhysicalBodyPublicInvocationBounds.public_run_succeeded_reflects
      (stagePrepared := actualStagePrepared fixture) (completion := receiver.completion)
      (functions := inventory.functions receiver) (packet := packet) (reflectsBodies := reflectsBodies)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := physicalCaller.physical) (wellFormed := fixture.source_wellFormed)
      (selected := selected) (caller := physicalCaller.base.val)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared)
      (started := started)
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] inventory.makeHeader.header.function)
      first.started checkpointAt first.executed (stages.descriptor_at inventory.makeHeader)
  have physicalRetained := RecursiveNamedPublicPhysicalHistory.physical_of_result physicalCaller.physical result
  have returnedRegistry := started.returned_registry succeeded
  rw [startupRegistry] at returnedRegistry
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType] at requested
  obtain ⟨returnedCaller, source, payload, sourceValue, _nativeValue, _related, retained⟩ :=
    RecursiveNamedPublicFunctionHistory.first_remembered rfl started selected requested succeeded result
      (valueEq.symm.trans first.returned)
  let entry : RecursiveNamedPublicFunctionHistory.Entry :=
    ⟨inventory.makeHeader.header.function.resultType, source, first.handle, payload,
      inventory.makeHeader.header.output, runOptions.outputValidationFuel⟩
  let state : RetainedState inventory receiver first.completion.session [entry] := {
    artifact := artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := returnedCaller
    atSession := returnedAt
    atRecipe := started.recipe_eq
    receiving := receiver.completion
    issued := receiver.issued
    extension := .refl _
    registry := receiver.registry.symm ▸ returnedRegistry
    history := ⟨retained, physicalRetained⟩ }
  exact ⟨entry, inventory.makeHeader.make_result_type, rfl, state, inventory.makeInput.prepared.available, _, sourceSize, sourceAt, sourceValue ▸ trace⟩

end Tests.SourceCoreCoercionPublic
