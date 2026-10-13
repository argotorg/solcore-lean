import Solcore.Test.SourceCoreGenericDirectCommon
import Solcore.Test.SourceCoreGenericDirectResults
import Solcore.Test.SourceCoreGenericDirectSelection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning

/-! The initial generic direct call derives its Source trace, Word result and reusable
empty history from actual bootstrap, input encoding and public completion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem first_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver) (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) :
    ∃ state : RetainedState support first.completion.session [],
      SourceCall support support.wordHeader.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.wordHeader.header.function)
        ⟨[]⟩ [.word seed, .bool true] (.value (.word seed)) state.heap := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := fixture.actual_start first.opened first.started
  have ready : first.bootstrap.ReadyAt 100000 first.session := .single first.ready
  obtain ⟨_bootstrap, initialized, _value, _initialStore, _atBootstrap, initial,
      initializedAt, _done, booted⟩ := ready.indexed opened first.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  have startupRegistry : encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
    apply started.simple_registry (booted.registry_at initial)
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word seed
    · exact .bool true
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.wordHeader.header := by
    apply selected_word_root support.wordHeader support.boolHeader support.chooseWordHeader support.chooseBoolHeader
      (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.wordRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.wordHeader.header.function.context
      (support.wordHeader.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word seed, .bool true] [.word seed, .bool true] := by
    rw [support.wordHeader.word_input_types]
    exact .cons (.leaf (.data
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩))
      (.cons (.leaf (.data
        ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩
        ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩)) .nil)
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.wordHeader.header support.wordInput.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.wordPacket.header.named.specialized support.wordInput.prepared.available)) := by
    rw [support.wordEq]
    exact support.wordPacket.sourceAt
  obtain ⟨caller, actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      returnedCaller, added, handles, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_collects
      (inputs := [support.wordInput, support.boolInput, support.chooseWordInput, support.chooseBoolInput]) (rows := support.rows) (distinct := support.distinct)
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
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] support.wordHeader.header.function)
      first.started first.executed .skip support.wordDescriptor
  have empty : added = [] := List.map_eq_nil_iff.mp handles
  subst added
  have returnedRegistry := started.returned_registry succeeded
  rw [startupRegistry] at returnedRegistry
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType, support.wordHeader.word_result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans first.returned) support.wordHeader.word_output result
  let state : RetainedState support first.completion.session [] := {
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
  exact ⟨state, support.wordInput.prepared.available, _, sourceSize, sourceAt, outcomeValue ▸ trace⟩

end Tests.SourceCoreGenericDirect
