import Solcore.Test.SourceCoreEvidenceMethodSeed
import Solcore.Test.SourceCoreEvidenceMethodStep
import Solcore.Test.SourceCoreEvidenceMethodFamily

/-! Four original public calls share their exact successive sessions, complete
Source heaps and physical method captures. Every body law is derived from the
actual compiler packets by the common numeric induction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure CallMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (before : RetainedState support.toOrdinaryInventory receiver session [])
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments scalar.publicValue)
    (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  rawType : request.header.function.resultType = scalar.sourceType
  nativeType : request.header.output = scalar.nativeType
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session []
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value scalar.source) after.heap

theorem RetainedState.word_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (bodies : MethodBodies fixture)
    (state : RetainedState support.toOrdinaryInventory receiver session [])
    (word : Core.Word)
    (call : ObservedCall session observed.wordRow.row.key [.word word] (.word word))
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.wordHeader.header (.word word) call [.word word] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.viaWordInput, support.viaBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.wordHeader.header :=
    selected_word_at support.wordHeader support.boolHeader support.viaWordHeader support.viaBoolHeader
      support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word word] [.word word] := by
    rw [selected, support.wordHeader.word_input_types]
    exact word_inputs word
  have raw : request.header.function.resultType = (.word word : ScalarOutput).sourceType := by
    rw [selected, support.wordHeader.word_result_type]; rfl
  have native : request.header.output = (.word word : ScalarOutput).nativeType := by
    rw [selected, support.wordHeader.word_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact stages.descriptor_at support.wordHeader
  obtain ⟨after, trace⟩ := state.finished_call (.word word) call request inputs
    (word_simple word) raw native descriptor (support.terminals request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support bodies state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, native, after, by rw [← selected]; exact trace⟩⟩

theorem RetainedState.bool_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (bodies : MethodBodies fixture)
    (state : RetainedState support.toOrdinaryInventory receiver session [])
    (flag : Bool)
    (call : ObservedCall session observed.boolRow.row.key [.bool flag] (.bool flag))
    (stages : ObservedStages fixture observed.boolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.boolHeader.header (.bool flag) call [.bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.viaWordInput, support.viaBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.boolHeader.header :=
    selected_bool_at support.wordHeader support.boolHeader support.viaWordHeader support.viaBoolHeader
      support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool flag] [.bool flag] := by
    rw [selected, support.boolHeader.bool_input_types]
    exact bool_inputs flag
  have raw : request.header.function.resultType = (.bool flag : ScalarOutput).sourceType := by
    rw [selected, support.boolHeader.bool_result_type]; rfl
  have native : request.header.output = (.bool flag : ScalarOutput).nativeType := by
    rw [selected, support.boolHeader.bool_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact stages.descriptor_at support.boolHeader
  obtain ⟨after, trace⟩ := state.finished_call (.bool flag) call request inputs
    (bool_simple flag) raw native descriptor (support.terminals request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support bodies state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, native, after, by rw [← selected]; exact trace⟩⟩

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : StaticSupportPackage fixture observed receiver.completion
  initial : RetainedState support.toOrdinaryInventory receiver sequence.first.completion.session []
  firstTrace : SourceCall support.toOrdinaryInventory support.wordHeader.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    ⟨[]⟩ [.word seed] (.value (.word seed)) initial.heap
  secondMeaning : CallMeaning initial support.boolHeader.header (.bool false) sequence.second
    [.bool false]
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  thirdMeaning : CallMeaning secondMeaning.after support.wordHeader.header (.word (Core.Word.ofNatModulo 33)) sequence.third
    [.word (Core.Word.ofNatModulo 33)]
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  fourthMeaning : CallMeaning thirdMeaning.after support.boolHeader.header (.bool true) sequence.fourth
    [.bool true]
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)

theorem sequence_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (bodies : MethodBodies fixture)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness wordStages boolStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports fixture observed wordStages boolStages methods receiver.issued
  obtain ⟨initial, firstTrace⟩ := first_meaning support.toOrdinaryInventory support.distinct
    (support.terminals support.wordHeader.header support.toOrdinaryInventory.word_member)
    (fun budget {child} selected => reflects_bodies receiver support bodies receiver.issued (.refl _)
      support.wordHeader.header support.toOrdinaryInventory.word_member selected budget) wordStages sequence.first
  obtain ⟨second⟩ := RetainedState.bool_meaning support bodies initial false sequence.second boolStages
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  obtain ⟨third⟩ := RetainedState.word_meaning support bodies second.after (Core.Word.ofNatModulo 33) sequence.third wordStages
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  obtain ⟨fourth⟩ := RetainedState.bool_meaning support bodies third.after true sequence.fourth boolStages
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  exact ⟨⟨support, initial, firstTrace, second, third, fourth⟩⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (bodies : MethodBodies fixture)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      Nonempty (SequenceWitness wordStages boolStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning wordStages boolStages methods bodies sequence receiver⟩

end Tests.SourceCoreEvidenceMethod
