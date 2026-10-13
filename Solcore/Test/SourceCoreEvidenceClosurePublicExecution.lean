import Solcore.Test.SourceCoreEvidenceClosureSeed
import Solcore.Test.SourceCoreEvidenceClosureMakeStep
import Solcore.Test.SourceCoreEvidenceClosureInvocation

/-! Seven actual public calls retain three distinct closures, both scalar result
profiles, and every intermediate Source heap in the returned session history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : PublicSupports receiver
  first : Entry
  second : Entry
  third : Entry
  firstType : first.sourceType = closureType .word
  secondType : second.sourceType = closureType .bool
  thirdType : third.sourceType = closureType .word
  firstHandle : first.handle = sequence.first.handle
  secondHandle : second.handle = sequence.second.handle
  thirdHandle : third.handle = sequence.third.handle
  firstHandleType : sequence.first.handle.sourceType = closureType .word
  secondHandleType : sequence.second.handle.sourceType = closureType .bool
  thirdHandleType : sequence.third.handle.sourceType = closureType .word
  firstSecond : first.handle ≠ second.handle
  firstThird : first.handle ≠ third.handle
  secondThird : second.handle ≠ third.handle
  initial : RetainedState support sequence.first.completion.session [first]
  secondState : RetainedState support sequence.second.completion.session [first, second]
  firstReadState : RetainedState support sequence.firstRead.completion.session [first, second]
  thirdState : RetainedState support sequence.third.completion.session [first, second, third]
  secondReadState : RetainedState support sequence.secondRead.completion.session [first, second, third]
  repeatedReadState : RetainedState support sequence.repeatedRead.completion.session [first, second, third]
  finalState : RetainedState support sequence.thirdRead.completion.session [first, second, third]
  firstTrace : SourceCall support support.wordHeader.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    ⟨[]⟩ [.word seed, .bool true] (.value first.source) initial.heap
  secondTrace : SourceCall support support.boolHeader.header
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
    initial.heap [.bool false, .word (Core.Word.ofNatModulo 22)] (.value second.source) secondState.heap
  firstArguments : List Dynamic.Value
  firstPacking : Dynamic.ValuesPack firstArguments .unit
  firstReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    secondState.heap first.source firstArguments (.value (.word seed)) firstReadState.heap
  thirdTrace : SourceCall support support.wordHeader.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    firstReadState.heap [.word (Core.Word.ofNatModulo 33), .bool false] (.value third.source) thirdState.heap
  secondArguments : List Dynamic.Value
  secondPacking : Dynamic.ValuesPack secondArguments .unit
  secondReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    thirdState.heap second.source secondArguments (.value (.bool false)) secondReadState.heap
  repeatedArguments : List Dynamic.Value
  repeatedPacking : Dynamic.ValuesPack repeatedArguments .unit
  repeatedReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    secondReadState.heap first.source repeatedArguments (.value (.word seed)) repeatedReadState.heap
  thirdArguments : List Dynamic.Value
  thirdPacking : Dynamic.ValuesPack thirdArguments .unit
  thirdReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    repeatedReadState.heap third.source thirdArguments (.value (.word (Core.Word.ofNatModulo 33))) finalState.heap

theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedFactories fixture observed)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (factoryWordStages : ObservedStages fixture observed.factoryWordRow)
    (factoryBoolStages : ObservedStages fixture observed.factoryBoolRow)
    (chooseWordStages : ObservedStages fixture observed.chooseWordRow)
    (chooseBoolStages : ObservedStages fixture observed.chooseBoolRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness wordStages boolStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports fixture observed extra wordStages boolStages factoryWordStages factoryBoolStages
    chooseWordStages chooseBoolStages receiver.completion.result.context.registry receiver.issued
  let scope := RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function
  let boolScope := RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function
  obtain ⟨first, firstType, firstHandle, firstHandleType, initial, firstTrace⟩ :=
    first_meaning_typed_handle support wordStages sequence.first
  obtain ⟨secondRequest⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.wordInput, support.boolInput, support.factoryWordInput,
      support.factoryBoolInput, support.chooseWordInput, support.chooseBoolInput] support.rows support.complete
    initial.atRecipe initial.history.current.1 initial.atSession sequence.second.started
  have secondHeader := selected_bool_at support.wordHeader support.boolHeader support.factoryWordHeader
    support.factoryBoolHeader support.chooseWordHeader support.chooseBoolHeader support.header_list secondRequest
  have secondInputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [first] secondRequest.header.function.context
      (secondRequest.header.bindings.map (fun binding => binding.1.scheme.body))
      [.bool false, .word (Core.Word.ofNatModulo 22)] [.bool false, .word (Core.Word.ofNatModulo 22)] := by
    rw [secondHeader, support.boolHeader.bool_input_types]
    exact bool_word_inputs false _
  obtain ⟨second, secondType, secondHandle, secondHandleType, secondState, secondTrace⟩ :=
    initial.make_typed_handle sequence.second secondRequest secondInputs (bool_word_simple false _)
      (secondHeader.symm ▸ support.boolDescriptor) boolScope
  rw [secondHeader] at secondType secondHandleType secondTrace
  rw [support.boolHeader.bool_result_type] at secondType secondHandleType
  have unitInput : ∀ entries, RecursiveNamedPublicFunctionHistoryInputs.Input
      entries support.wordHeader.header.function.context .unit .unit .unit := fun _ =>
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  obtain ⟨firstArguments, firstReadState, firstPacking, firstReadTrace⟩ := invoke_word secondState first
    (by simp) firstType firstHandle firstHandleType (unitInput _) sequence.firstRead sequence.firstValue scope
  obtain ⟨thirdRequest⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.wordInput, support.boolInput, support.factoryWordInput,
      support.factoryBoolInput, support.chooseWordInput, support.chooseBoolInput] support.rows support.complete
    firstReadState.atRecipe firstReadState.history.current.1 firstReadState.atSession sequence.third.started
  have thirdHeader := selected_word_at support.wordHeader support.boolHeader support.factoryWordHeader
    support.factoryBoolHeader support.chooseWordHeader support.chooseBoolHeader support.header_list thirdRequest
  have thirdInputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [first, second] thirdRequest.header.function.context
      (thirdRequest.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word (Core.Word.ofNatModulo 33), .bool false] [.word (Core.Word.ofNatModulo 33), .bool false] := by
    rw [thirdHeader, support.wordHeader.word_input_types]
    exact word_bool_inputs _ false
  obtain ⟨third, thirdType, thirdHandle, thirdHandleType, thirdState, thirdTrace⟩ :=
    firstReadState.make_typed_handle sequence.third thirdRequest thirdInputs (word_bool_simple _ false)
      (thirdHeader.symm ▸ support.wordDescriptor) scope
  rw [thirdHeader] at thirdType thirdHandleType thirdTrace
  rw [support.wordHeader.word_result_type] at thirdType thirdHandleType
  obtain ⟨secondArguments, secondReadState, secondPacking, secondReadTrace⟩ := invoke_bool thirdState second
    (by simp) secondType secondHandle secondHandleType (unitInput _) sequence.secondRead sequence.secondValue scope
  obtain ⟨repeatedArguments, repeatedReadState, repeatedPacking, repeatedReadTrace⟩ := invoke_word secondReadState first
    (by simp) firstType firstHandle firstHandleType (unitInput _) sequence.repeatedRead sequence.repeatedValue scope
  obtain ⟨thirdArguments, finalState, thirdPacking, thirdReadTrace⟩ := invoke_word repeatedReadState third
    (by simp) thirdType thirdHandle thirdHandleType (unitInput _) sequence.thirdRead sequence.thirdValue scope
  exact ⟨{
    support, first, second, third, firstType, secondType, thirdType,
    firstHandle, secondHandle, thirdHandle, firstHandleType, secondHandleType, thirdHandleType,
    firstSecond := by rw [firstHandle, secondHandle]; exact sequence.firstSecond
    firstThird := by rw [firstHandle, thirdHandle]; exact sequence.firstThird
    secondThird := by rw [secondHandle, thirdHandle]; exact sequence.secondThird
    initial, secondState, firstReadState, thirdState, secondReadState, repeatedReadState, finalState,
    firstTrace, secondTrace, firstArguments, firstPacking, firstReadTrace,
    thirdTrace, secondArguments, secondPacking, secondReadTrace,
    repeatedArguments, repeatedPacking, repeatedReadTrace, thirdArguments, thirdPacking, thirdReadTrace }⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedFactories fixture observed)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (factoryWordStages : ObservedStages fixture observed.factoryWordRow)
    (factoryBoolStages : ObservedStages fixture observed.factoryBoolRow)
    (chooseWordStages : ObservedStages fixture observed.chooseWordRow)
    (chooseBoolStages : ObservedStages fixture observed.chooseBoolRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed, Nonempty (SequenceWitness wordStages boolStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning fixture observed extra wordStages boolStages factoryWordStages factoryBoolStages
    chooseWordStages chooseBoolStages sequence receiver⟩
end Tests.SourceCoreEvidenceClosure
