import Solcore.Test.SourceCoreMethodOriginEvidenceSeed
import Solcore.Test.SourceCoreMethodOriginEvidenceStep
import Solcore.Test.SourceCoreMethodOriginEvidenceMakeStep
import Solcore.Test.SourceCoreMethodOriginEvidenceFamily
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionInputRegistry
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOriginEvidence
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

theorem RetainedState.word_factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value next : Core.Word) (flag : Bool)
    (call : ObservedFunctionCall session observed.wordRow.row.key [.word value, .word next, .bool flag])
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.wordHeader.header call .word [.word value, .word next, .bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.wordHeader.header :=
    selected_word_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word value, .word next, .bool flag] [.word value, .word next, .bool flag] := by
    rw [selected, support.wordHeader.word_input_types]
    exact word_inputs value next flag
  have raw : request.header.function.resultType = closureType .word := by
    rw [selected, support.wordHeader.word_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.wordHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (word_simple value next flag) descriptor (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by rw [← selected]; exact trace⟩⟩

theorem RetainedState.bool_factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value next : Bool) (flag : Bool)
    (call : ObservedFunctionCall session observed.boolRow.row.key [.bool value, .bool next, .bool flag])
    (stages : ObservedStages fixture observed.boolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.boolHeader.header call .bool [.bool value, .bool next, .bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.boolHeader.header :=
    selected_bool_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool value, .bool next, .bool flag] [.bool value, .bool next, .bool flag] := by
    rw [selected, support.boolHeader.bool_input_types]
    exact bool_inputs value next flag
  have raw : request.header.function.resultType = closureType .bool := by
    rw [selected, support.boolHeader.bool_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.boolHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (bool_simple value next flag) descriptor (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by rw [← selected]; exact trace⟩⟩

theorem RetainedState.useWord_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .word)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Core.Word) (call : ObservedCall session observed.useWordRow.row.key [.function handle])
    (returned : call.completion.value = .word value)
    (stages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useWordHeader.header (.word value) call [entry.source] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.useWordHeader.header :=
    selected_useWord_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useWordHeader.useWord_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.word value : ScalarOutput).sourceType := by
    rw [selected, support.useWordHeader.useWord_result_type]; rfl
  have native : request.header.output = (.word value : ScalarOutput).nativeType := by
    rw [selected, support.useWordHeader.useWord_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useWordHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.word value) call returned request inputs registry raw native descriptor
    (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by rw [← selected]; exact trace⟩⟩

theorem RetainedState.useBool_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .bool)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Bool) (call : ObservedCall session observed.useBoolRow.row.key [.function handle])
    (returned : call.completion.value = .bool value)
    (stages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useBoolHeader.header (.bool value) call [entry.source] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.useBoolHeader.header :=
    selected_useBool_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useBoolHeader.useBool_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.bool value : ScalarOutput).sourceType := by
    rw [selected, support.useBoolHeader.useBool_result_type]; rfl
  have native : request.header.output = (.bool value : ScalarOutput).nativeType := by
    rw [selected, support.useBoolHeader.useBool_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useBoolHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.bool value) call returned request inputs registry raw native descriptor
    (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by rw [← selected]; exact trace⟩⟩

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : StaticSupportPackage fixture observed receiver.completion
  firstEntry : Entry
  firstType : firstEntry.sourceType = closureType .word
  firstHandle : firstEntry.handle = sequence.first.handle
  initial : RetainedState support.toOrdinaryInventory receiver sequence.first.completion.session [firstEntry]
  firstTrace : SourceCall support.toOrdinaryInventory support.wordHeader.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] (.value firstEntry.source) initial.heap
  secondMeaning : FactoryMeaning initial support.boolHeader.header sequence.second .bool [.bool false, .bool true, .bool true]
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  firstReadMeaning : CallMeaning secondMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 33)) sequence.firstRead [firstEntry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  thirdMeaning : FactoryMeaning firstReadMeaning.after support.wordHeader.header sequence.third .word [.word (Core.Word.ofNatModulo 55), .word (Core.Word.ofNatModulo 66), .bool false]
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  secondReadMeaning : CallMeaning thirdMeaning.after support.useBoolHeader.header (.bool true) sequence.secondRead [secondMeaning.entry.source]
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  repeatedReadMeaning : CallMeaning secondReadMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 33)) sequence.repeatedRead [firstEntry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  thirdReadMeaning : CallMeaning repeatedReadMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 55)) sequence.thirdRead [thirdMeaning.entry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)

theorem SequenceWitness.handles_distinct {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) :
    meaning.firstEntry.handle ≠ meaning.secondMeaning.entry.handle ∧
      meaning.firstEntry.handle ≠ meaning.thirdMeaning.entry.handle ∧
      meaning.secondMeaning.entry.handle ≠ meaning.thirdMeaning.entry.handle := by
  rw [meaning.firstHandle, meaning.secondMeaning.handleEq, meaning.thirdMeaning.handleEq]
  exact ⟨sequence.firstSecond, sequence.firstThird, sequence.secondThird⟩

theorem sequence_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports fixture observed factories methods receiver.issued
  obtain ⟨firstEntry, firstType, firstHandle, initial, firstTrace⟩ := first_meaning_typed_handle
    support.toOrdinaryInventory support.distinct
    (support.bodies support.wordHeader.header support.toOrdinaryInventory.word_member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods receiver.issued (.refl _)
      support.wordHeader.header support.toOrdinaryInventory.word_member selected budget) wordStages sequence.first
  obtain ⟨second⟩ := RetainedState.bool_factory_meaning support sources bodies methods initial false true true sequence.second boolStages
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  obtain ⟨firstRead⟩ := RetainedState.useWord_meaning support sources bodies methods second.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 33) sequence.firstRead sequence.firstValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨third⟩ := RetainedState.word_factory_meaning support sources bodies methods firstRead.after
    (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false sequence.third wordStages
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  obtain ⟨secondRead⟩ := RetainedState.useBool_meaning support sources bodies methods third.after second.entry
    (by simp) second.entryType second.handleEq true sequence.secondRead sequence.secondValue useBoolStages
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  obtain ⟨repeatedRead⟩ := RetainedState.useWord_meaning support sources bodies methods secondRead.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 33) sequence.repeatedRead sequence.repeatedValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨thirdRead⟩ := RetainedState.useWord_meaning support sources bodies methods repeatedRead.after third.entry
    (by simp) third.entryType third.handleEq (Core.Word.ofNatModulo 55) sequence.thirdRead sequence.thirdValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  exact ⟨⟨support, firstEntry, firstType, firstHandle, initial, firstTrace,
    second, firstRead, third, secondRead, repeatedRead, thirdRead⟩⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning wordStages boolStages useWordStages useBoolStages factories sources bodies methods sequence receiver⟩

end Tests.SourceCoreMethodOriginEvidence
