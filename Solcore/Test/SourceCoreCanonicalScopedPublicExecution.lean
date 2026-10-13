import Solcore.Test.SourceCoreCanonicalScopedSeed
import Solcore.Test.SourceCoreCanonicalScopedMakeStep
import Solcore.Test.SourceCoreCanonicalScopedInvocation

/-! Three actual factory calls and three later handle calls with direct bodies keep
all returned sessions and captured Source heaps in one ordered history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : PublicSupports receiver
  first : Entry
  second : Entry
  intervening : Entry
  firstType : first.sourceType = closureType
  secondType : second.sourceType = closureType
  interveningType : intervening.sourceType = closureType
  firstHandle : first.handle = sequence.first.handle
  secondHandle : second.handle = sequence.second.handle
  interveningHandle : intervening.handle = sequence.intervening.handle
  firstHandleType : sequence.first.handle.sourceType = closureType
  secondHandleType : sequence.second.handle.sourceType = closureType
  distinct : first.handle ≠ second.handle
  initial : RetainedState support sequence.first.completion.session [first]
  secondState : RetainedState support sequence.second.completion.session [first, second]
  firstReadState : RetainedState support sequence.firstRead.completion.session [first, second]
  interveningState : RetainedState support sequence.intervening.completion.session [first, second, intervening]
  secondReadState : RetainedState support sequence.secondRead.completion.session [first, second, intervening]
  finalState : RetainedState support sequence.repeatedRead.completion.session [first, second, intervening]
  firstTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    ⟨[]⟩ [.word seed] (.value first.source) initial.heap
  secondTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    initial.heap [.word secondSeed] (.value second.source) secondState.heap
  firstArguments : List Dynamic.Value
  firstPacking : Dynamic.ValuesPack firstArguments (.product (.word firstNext) (.product (.bool true) (.bool false)))
  firstReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondState.heap first.source firstArguments (.value (.word seed)) firstReadState.heap
  interveningTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    firstReadState.heap [.word interveningSeed] (.value intervening.source) interveningState.heap
  secondArguments : List Dynamic.Value
  secondPacking : Dynamic.ValuesPack secondArguments (.product (.word secondNext) (.product (.bool true) (.bool false)))
  secondReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    interveningState.heap second.source secondArguments (.value (.word secondSeed)) secondReadState.heap
  repeatedArguments : List Dynamic.Value
  repeatedPacking : Dynamic.ValuesPack repeatedArguments (.product (.word repeatedNext) (.product (.bool false) (.bool false)))
  repeatedReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondReadState.heap first.source repeatedArguments (.value (.word firstNext)) finalState.heap

theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (relayStages : ObservedStages fixture observed.relayRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness makeStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports (completion := receiver.completion)
    fixture observed extra identityStages makeStages relayStages receiver.completion.result.context.registry receiver.issued
  let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
  obtain ⟨first, firstType, firstHandle, firstHandleType, initial, firstTrace⟩ :=
    first_meaning_typed_handle support makeStages sequence.first
  obtain ⟨second, secondType, secondHandle, secondHandleType, secondState, secondTrace⟩ :=
    initial.make_typed_handle sequence.second scope
  have packedInput : ∀ entries next flag stop, RecursiveNamedPublicFunctionHistoryInputs.Input
      entries support.makeHeader.header.function.context parameterType (packed next flag stop)
        (.product (.word next) (.product (.bool flag) (.bool stop))) := by
    intro entries next flag stop
    exact .product
      (.data ⟨.word next, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word next⟩
        ⟨.word next, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word next⟩)
      (.product
        (.data ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
          ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩)
        (.data ⟨.bool stop, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool stop⟩
          ⟨.bool stop, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool stop⟩))
  obtain ⟨firstArguments, firstReadState, firstPacking, firstReadTrace⟩ := invoke_word secondState first
    (by simp) firstType firstHandle firstHandleType (packedInput _ firstNext true false) sequence.firstRead sequence.firstValue scope
  obtain ⟨intervening, interveningType, interveningHandle, _interveningHandleType, interveningState, interveningTrace⟩ :=
    firstReadState.make_typed_handle sequence.intervening scope
  obtain ⟨secondArguments, secondReadState, secondPacking, secondReadTrace⟩ := invoke_word interveningState second
    (by simp) secondType secondHandle secondHandleType (packedInput _ secondNext true false) sequence.secondRead sequence.secondValue scope
  obtain ⟨repeatedArguments, finalState, repeatedPacking, repeatedReadTrace⟩ := invoke_word secondReadState first
    (by simp) firstType firstHandle firstHandleType (packedInput _ repeatedNext false false) sequence.repeatedRead sequence.repeatedValue scope
  exact ⟨{
    support, first, second, intervening, firstType, secondType, interveningType,
    firstHandle, secondHandle, interveningHandle, firstHandleType, secondHandleType,
    distinct := by rw [firstHandle, secondHandle]; exact sequence.distinct
    initial, secondState, firstReadState, interveningState, secondReadState, finalState,
    firstTrace, secondTrace, firstArguments, firstPacking, firstReadTrace,
    interveningTrace, secondArguments, secondPacking, secondReadTrace,
    repeatedArguments, repeatedPacking, repeatedReadTrace }⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (relayStages : ObservedStages fixture observed.relayRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed, Nonempty (SequenceWitness makeStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning fixture observed extra identityStages makeStages relayStages sequence receiver⟩

end Tests.SourceCoreCanonicalScoped
