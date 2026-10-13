import Solcore.Test.SourceCoreCoercionPublicSeed
import Solcore.Test.SourceCoreCoercionPublicStep
import Solcore.Test.SourceCoreCoercionPublicMakeStep
import Solcore.Test.SourceCoreCoercionPublicFamily
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionInputRegistry
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

structure CallMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments)
    (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  registry : request.encodedValues.registry = before.receiving.result.context.registry
  rawType : request.header.function.resultType = scalar.sourceType
  nativeType : request.header.output = scalar.nativeType
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session entries
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value scalar.source) after.heap

structure FactoryMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key publicArguments)
    (resultType : TypeSystem.Ty) (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  rawType : request.header.function.resultType = closureType resultType
  entry : Entry
  entryType : entry.sourceType = closureType resultType
  handleEq : entry.handle = call.handle
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session (entries ++ [entry])
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value entry.source) after.heap

theorem RetainedState.factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog fixture.recipe.compiled)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value : Bool)
    (call : ObservedFunctionCall session observed.makeRow.row.key [.bool value])
    (stages : ObservedStages fixture observed.makeRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.makeHeader.header call .word [.bool value] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_at
    fixture.recipePrepared [support.makeInput, support.useInput, support.keepInput]
    support.toOrdinaryInventory.rows state.atRecipe
    state.history.semantic.current.1 state.atSession (fun root found =>
      ⟨support.makeHeader.header, support.toOrdinaryInventory.selected_row observed.makeRow.toObservedRow
        support.makeHeader support.toOrdinaryInventory.make_member support.makeSlot root found⟩) call.started
  have selected : request.header = support.makeHeader.header :=
    selected_make_at support.makeHeader support.useHeader support.keepHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool value] [.bool value] := by
    rw [selected, support.makeHeader.make_input_types]
    exact bool_inputs value
  have raw : request.header.function.resultType = closureType .word := by
    rw [selected, support.makeHeader.make_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.makeHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (bool_simple value) descriptor (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by rw [← selected]; exact trace⟩⟩

theorem RetainedState.use_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog fixture.recipe.compiled)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .word)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Core.Word) (call : ObservedCall session observed.useRow.row.key [.function handle])
    (returned : call.completion.value = .word value)
    (stages : ObservedStages fixture observed.useRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useHeader.header (.word value) call [entry.source] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_at
    fixture.recipePrepared [support.makeInput, support.useInput, support.keepInput]
    support.toOrdinaryInventory.rows state.atRecipe
    state.history.semantic.current.1 state.atSession (fun root found =>
      ⟨support.useHeader.header, support.toOrdinaryInventory.selected_row observed.useRow.toObservedRow
        support.useHeader support.toOrdinaryInventory.use_member support.useSlot root found⟩) call.started
  have selected : request.header = support.useHeader.header :=
    selected_use_at support.makeHeader support.useHeader support.keepHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useHeader.use_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.word value : ScalarOutput).sourceType := by
    rw [selected, support.useHeader.use_result_type]; rfl
  have native : request.header.output = (.word value : ScalarOutput).nativeType := by
    rw [selected, support.useHeader.use_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.word value) call returned request inputs registry raw native descriptor
    (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by rw [← selected]; exact trace⟩⟩

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow.toObservedRow)
    (useStages : ObservedStages fixture observed.useRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : StaticSupportPackage fixture observed receiver.completion
  firstEntry : Entry
  firstType : firstEntry.sourceType = closureType .word
  firstHandle : firstEntry.handle = sequence.first.handle
  initial : RetainedState support.toOrdinaryInventory receiver sequence.first.completion.session [firstEntry]
  firstTrace : SourceCall support.toOrdinaryInventory support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    ⟨[]⟩ [.bool true] (.value firstEntry.source) initial.heap
  secondMeaning : FactoryMeaning initial support.makeHeader.header sequence.second .word [.bool false]
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
  firstReadMeaning : CallMeaning secondMeaning.after support.useHeader.header (.word (Core.Word.ofNatModulo 41)) sequence.firstRead [firstEntry.source]
    (RecursiveStageRegistry.scope useStages.sidecar [] support.useHeader.header.function)
  thirdMeaning : FactoryMeaning firstReadMeaning.after support.makeHeader.header sequence.third .word [.bool false]
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
  secondReadMeaning : CallMeaning thirdMeaning.after support.useHeader.header (.word (Core.Word.ofNatModulo 7)) sequence.secondRead [secondMeaning.entry.source]
    (RecursiveStageRegistry.scope useStages.sidecar [] support.useHeader.header.function)
  repeatedReadMeaning : CallMeaning secondReadMeaning.after support.useHeader.header (.word (Core.Word.ofNatModulo 41)) sequence.repeatedRead [firstEntry.source]
    (RecursiveStageRegistry.scope useStages.sidecar [] support.useHeader.header.function)
  thirdReadMeaning : CallMeaning repeatedReadMeaning.after support.useHeader.header (.word (Core.Word.ofNatModulo 7)) sequence.thirdRead [thirdMeaning.entry.source]
    (RecursiveStageRegistry.scope useStages.sidecar [] support.useHeader.header.function)

theorem SequenceWitness.handles_distinct {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow.toObservedRow}
    {useStages : ObservedStages fixture observed.useRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages useStages sequence receiver) :
    meaning.firstEntry.handle ≠ meaning.secondMeaning.entry.handle ∧
      meaning.firstEntry.handle ≠ meaning.thirdMeaning.entry.handle ∧
      meaning.secondMeaning.entry.handle ≠ meaning.thirdMeaning.entry.handle := by
  rw [meaning.firstHandle, meaning.secondMeaning.handleEq, meaning.thirdMeaning.handleEq]
  exact ⟨sequence.firstSecond, sequence.firstThird, sequence.secondThird⟩

theorem sequence_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow.toObservedRow)
    (useStages : ObservedStages fixture observed.useRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog fixture.recipe.compiled)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness makeStages useStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports fixture observed factories methods receiver.issued
  obtain ⟨firstEntry, firstType, firstHandle, initial, firstTrace⟩ := first_meaning_typed_handle
    support.toOrdinaryInventory support.distinct
    (support.bodies support.makeHeader.header support.toOrdinaryInventory.make_member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods receiver.issued (.refl _)
      support.makeHeader.header support.toOrdinaryInventory.make_member selected budget) makeStages sequence.first
  obtain ⟨second⟩ := RetainedState.factory_meaning support sources bodies methods initial false sequence.second makeStages
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
  obtain ⟨firstRead⟩ := RetainedState.use_meaning support sources bodies methods second.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 41) sequence.firstRead sequence.firstValue useStages
    (RecursiveStageRegistry.scope useStages.sidecar [] support.useHeader.header.function)
  obtain ⟨third⟩ := RetainedState.factory_meaning support sources bodies methods firstRead.after
    false sequence.third makeStages
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
  obtain ⟨secondRead⟩ := RetainedState.use_meaning support sources bodies methods third.after second.entry
    (by simp) second.entryType second.handleEq (Core.Word.ofNatModulo 7) sequence.secondRead sequence.secondValue useStages
    (RecursiveStageRegistry.scope useStages.sidecar [] support.useHeader.header.function)
  obtain ⟨repeatedRead⟩ := RetainedState.use_meaning support sources bodies methods secondRead.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 41) sequence.repeatedRead sequence.repeatedValue useStages
    (RecursiveStageRegistry.scope useStages.sidecar [] support.useHeader.header.function)
  obtain ⟨thirdRead⟩ := RetainedState.use_meaning support sources bodies methods repeatedRead.after third.entry
    (by simp) third.entryType third.handleEq (Core.Word.ofNatModulo 7) sequence.thirdRead sequence.thirdValue useStages
    (RecursiveStageRegistry.scope useStages.sidecar [] support.useHeader.header.function)
  exact ⟨⟨support, firstEntry, firstType, firstHandle, initial, firstTrace,
    second, firstRead, third, secondRead, repeatedRead, thirdRead⟩⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (makeStages : ObservedStages fixture observed.makeRow.toObservedRow)
    (useStages : ObservedStages fixture observed.useRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog fixture.recipe.compiled)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      Nonempty (SequenceWitness makeStages useStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning makeStages useStages factories sources bodies methods sequence receiver⟩

end Tests.SourceCoreCoercionPublic
