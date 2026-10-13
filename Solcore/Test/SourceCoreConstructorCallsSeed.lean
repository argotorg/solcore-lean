import Solcore.Test.SourceCoreConstructorCallsCommon
import Solcore.Test.SourceCoreConstructorCallsSelection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionInitial

/-! Actual initialization and the first public make(10) execution establish
the first Source closure and history entry, including its captured parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

def ObservedPublicRun.as_function_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (first : ObservedPublicRun fixture observed.makeRow) :
    RecursiveNamedPublicPhysicalSessionState.FunctionCall first.session observed.makeRow.row.key [.word seed] runOptions :=
  ⟨⟨⟨first.checkpoint, first.started⟩, first.completion, first.executed⟩, first.handle, first.returned⟩

theorem ObservedPublicRun.initial_start {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.makeRow) :
    Nonempty (RecursiveNamedPublicPhysicalSessionInitial.Started support.rows fixture.recipePrepared
      support.makeHeader.header first.as_function_call.toCall.toStartedCall) := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ :=
    fixture.actual_start first.opened first.started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.makeHeader.header := by
    apply selected_make_root (fixture := fixture) (observed := observed)
      support.makeHeader support.readHeader (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.makeRow.row.key)) started.selected)
  subst selectedHeader
  exact ⟨{
    publicCompiled := fixture.facadeCompiled
    artifact := artifact, nativeSession := session, checkpoint := checkpoint, root := root
    world := world, store := store, native := native, encodedValues := encodedValues
    opened := opened, atSession := sessionAt, atCheckpoint := checkpointAt
    started := started, selected := selected, bootstrap := first.bootstrap
    bootstrapFuel := 100000, fresh := first.fresh, authority := first.authority
    ready := .single first.ready }⟩

theorem first_meaning_typed_handle {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (extra : ObservedMake fixture observed)
    (support : PublicSupports receiver)
    (makeStages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) :
    ∃ entry : Entry,
      entry.sourceType = .function .unit .word ∧ entry.handle = first.handle ∧
      first.handle.sourceType = .function .unit .word ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.makeHeader.header
          (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
          ⟨[]⟩ [.word seed] (.value entry.source) state.heap := by
  obtain ⟨start⟩ := first.initial_start support
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      support.makeHeader.header.function.context [.word seed] support.makeHeader.header.types := by
    have bindingTypes : support.makeHeader.header.types =
        support.makeHeader.header.bindings.map (fun binding => binding.1.scheme.body) := by
      have bodyTypes := Dynamic.MonoBindersExtend.bodyTypes_eq support.makeHeader.header.extended
      rw [support.makeHeader.header.parameters] at bodyTypes
      simpa only [List.map_map, Function.comp_def] using bodyTypes.symm
    rw [bindingTypes, support.makeHeader.make_input_types extra]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  obtain ⟨entry, type, handle, state, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionInitial.first_function support.rows fixture.recipePrepared
      support.makeHeader.header support.makeHeader.header support.program support.distinct first.as_function_call start
      (by intro value member; cases List.mem_singleton.mp member; exact .word seed)
      inputTypes inputMeanings support.makeDescriptor
      (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
  obtain ⟨checkpoint, started, resumed⟩ := first.executed
  have same : checkpoint = first.checkpoint := Except.ok.inj (started.symm.trans first.started)
  subst checkpoint
  obtain ⟨actual, _generation, _value, _store, _done, exported, valueEq, _typeEq, _budgetEq, _atSession⟩ :=
    resumed.indexed_succeeded start.atCheckpoint
  have atRecipe : start.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe → artifact.RecipeAt fixture.recipe :=
      fun artifact atRecipe => by cases artifact; exact atRecipe
    exact convert _ start.started.recipe_eq
  have requested := start.started.original.result_type_at atRecipe start.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result start.selected).2
  rw [resultType, support.makeHeader.make_result_type] at requested
  have handleType := exported.function_source_type requested (valueEq.symm.trans first.returned)
  exact ⟨entry, type.trans support.makeHeader.make_result_type, handle, handleType, state, trace⟩

/-- The original factory theorem remains available when the public handle's
raw type is not needed by the caller. -/
theorem first_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (extra : ObservedMake fixture observed)
    (support : PublicSupports receiver)
    (makeStages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) :
    ∃ entry : Entry,
      entry.sourceType = .function .unit .word ∧ entry.handle = first.handle ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.makeHeader.header
          (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
          ⟨[]⟩ [.word seed] (.value entry.source) state.heap := by
  obtain ⟨entry, sourceType, handle, _handleType, state, trace⟩ :=
    first_meaning_typed_handle extra support makeStages first
  exact ⟨entry, sourceType, handle, state, trace⟩

end Tests.SourceCoreConstructorCalls
