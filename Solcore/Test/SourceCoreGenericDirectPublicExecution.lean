import Solcore.Test.SourceCoreGenericDirectSeed
import Solcore.Test.SourceCoreGenericDirectStep

/-! Both actual instantiations of choose remain distinct in the compiler
inventory. Four public calls use their exact successive sessions and Source heaps. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure CallMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (before : RetainedState support session [])
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments scalar.publicValue)
    (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  rawType : request.header.function.resultType = scalar.sourceType
  nativeType : request.header.output = scalar.nativeType
  after : RetainedState support call.completion.session []
  trace : SourceCall support header invocation before.heap arguments (.value scalar.source) after.heap

theorem RetainedState.word_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (state : RetainedState support session [])
    (word : Core.Word) (flag : Bool)
    (call : ObservedCall session observed.wordRow.row.key [.word word, .bool flag] (.word word))
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.wordHeader.header (.word word) call [.word word, .bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.wordInput, support.boolInput, support.chooseWordInput, support.chooseBoolInput]
    support.rows support.complete state.atRecipe state.history.current.1 state.atSession call.started
  have selected : request.header = support.wordHeader.header :=
    selected_word_at support.wordHeader support.boolHeader support.chooseWordHeader support.chooseBoolHeader
      support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word word, .bool flag] [.word word, .bool flag] := by
    rw [selected, support.wordHeader.word_input_types]
    exact word_bool_inputs word flag
  have raw : request.header.function.resultType = (ScalarOutput.word word).sourceType := by
    rw [selected, support.wordHeader.word_result_type]; rfl
  have native : request.header.output = (ScalarOutput.word word).nativeType := by
    rw [selected, support.wordHeader.word_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact stages.descriptor_at support.wordHeader
  obtain ⟨after, trace⟩ := state.finished_call (.word word) call request inputs
    (word_bool_simple word flag) raw native descriptor invocation
  exact ⟨⟨request, selected, inputs, raw, native, after, by rw [← selected]; exact trace⟩⟩

theorem RetainedState.bool_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (state : RetainedState support session [])
    (flag : Bool) (word : Core.Word)
    (call : ObservedCall session observed.boolRow.row.key [.bool flag, .word word] (.bool flag))
    (stages : ObservedStages fixture observed.boolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.boolHeader.header (.bool flag) call [.bool flag, .word word] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.wordInput, support.boolInput, support.chooseWordInput, support.chooseBoolInput]
    support.rows support.complete state.atRecipe state.history.current.1 state.atSession call.started
  have selected : request.header = support.boolHeader.header :=
    selected_bool_at support.wordHeader support.boolHeader support.chooseWordHeader support.chooseBoolHeader
      support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool flag, .word word] [.bool flag, .word word] := by
    rw [selected, support.boolHeader.bool_input_types]
    exact bool_word_inputs flag word
  have raw : request.header.function.resultType = (ScalarOutput.bool flag).sourceType := by
    rw [selected, support.boolHeader.bool_result_type]; rfl
  have native : request.header.output = (ScalarOutput.bool flag).nativeType := by
    rw [selected, support.boolHeader.bool_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact stages.descriptor_at support.boolHeader
  obtain ⟨after, trace⟩ := state.finished_call (.bool flag) call request inputs
    (bool_word_simple flag word) raw native descriptor invocation
  exact ⟨⟨request, selected, inputs, raw, native, after, by rw [← selected]; exact trace⟩⟩

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : PublicSupports receiver
  initial : RetainedState support sequence.first.completion.session []
  firstTrace : SourceCall support support.wordHeader.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    ⟨[]⟩ [.word seed, .bool true] (.value (.word seed)) initial.heap
  secondMeaning : CallMeaning initial support.boolHeader.header (.bool false) sequence.second
    [.bool false, .word (Core.Word.ofNatModulo 22)]
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  thirdMeaning : CallMeaning secondMeaning.after support.wordHeader.header (.word (Core.Word.ofNatModulo 33)) sequence.third
    [.word (Core.Word.ofNatModulo 33), .bool false]
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  fourthMeaning : CallMeaning thirdMeaning.after support.boolHeader.header (.bool true) sequence.fourth
    [.bool true, .word (Core.Word.ofNatModulo 44)]
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)

theorem sequence_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (chooseWordStages : ObservedStages fixture observed.chooseWordRow)
    (chooseBoolStages : ObservedStages fixture observed.chooseBoolRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness wordStages boolStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports fixture observed wordStages boolStages chooseWordStages chooseBoolStages
    receiver.completion.result.context.registry receiver.issued
  obtain ⟨initial, firstTrace⟩ := first_meaning support wordStages sequence.first
  obtain ⟨second⟩ := initial.bool_meaning false (Core.Word.ofNatModulo 22) sequence.second boolStages
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  obtain ⟨third⟩ := second.after.word_meaning (Core.Word.ofNatModulo 33) false sequence.third wordStages
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  obtain ⟨fourth⟩ := third.after.bool_meaning true (Core.Word.ofNatModulo 44) sequence.fourth boolStages
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  exact ⟨⟨support, initial, firstTrace, second, third, fourth⟩⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (chooseWordStages : ObservedStages fixture observed.chooseWordRow)
    (chooseBoolStages : ObservedStages fixture observed.chooseBoolRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      Nonempty (SequenceWitness wordStages boolStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning wordStages boolStages chooseWordStages chooseBoolStages sequence receiver⟩

end Tests.SourceCoreGenericDirect
