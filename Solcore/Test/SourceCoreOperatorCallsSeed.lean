import Solcore.Test.SourceCoreOperatorCallsCommon
import Solcore.Test.SourceCoreOperatorCallsSelection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning

/-! The initial nonempty-loop call derives its Source trace, Word result and reusable
empty history from actual bootstrap, input encoding and public completion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem first_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver) (stages : ObservedStages fixture observed.identityRow)
    (first : ObservedInitial fixture observed) :
    ∃ state : RetainedState support first.call.completion.session [],
      SourceCall support support.identityHeader.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.identityHeader.header.function)
        ⟨[]⟩ [.word seed] (.value (.word seed)) state.heap := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := first.start_receipt
  have startupRegistry := first.metadata_at_start opened sessionAt started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.identityHeader.header := by
    apply selected_identity_root (fixture := fixture) (observed := observed)
      support.identityHeader support.selectHeader (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.identityRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.identityHeader.header.function.context
      (support.identityHeader.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word seed] [.word seed] := by
    rw [support.identityHeader.identity_input_types]
    exact .cons (.leaf (.data
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.identityHeader.header support.identityInput.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.identityPacket.header.named.specialized support.identityInput.prepared.available)) := by
    rw [support.identityEq]
    exact support.identityPacket.sourceAt
  obtain ⟨caller, actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      returnedCaller, added, handles, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_collects
      (inputs := [support.identityInput, support.selectInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] support.identityHeader.header.function)
      first.call.started first.call.executed .skip support.identityDescriptor
  have empty : added = [] := List.map_eq_nil_iff.mp handles
  subst added
  have returnedRegistry := started.returned_registry succeeded
  rw [startupRegistry] at returnedRegistry
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType, support.identityHeader.result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans first.call.returned) support.identityHeader.output result
  let state : RetainedState support first.call.completion.session [] := {
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
    history := retained }
  exact ⟨state, support.identityInput.prepared.available, _, sourceSize, sourceAt, outcomeValue ▸ trace⟩

end Tests.SourceCoreOperatorCalls
