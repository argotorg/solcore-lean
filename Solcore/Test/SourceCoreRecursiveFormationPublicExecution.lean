import Solcore.Test.SourceCoreRecursiveFormationSeed
import Solcore.Test.SourceCoreRecursiveFormationMakeStep
import Solcore.Test.SourceCoreRecursiveFormationInvocation

/-! Two real tuple exports and four direct calls retain both output pairs in
order across the exact returned sessions and Source heaps. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : PublicSupports receiver
  first : Entry
  second : Entry
  third : Entry
  fourth : Entry
  firstType : first.sourceType = closureType
  secondType : second.sourceType = closureType
  thirdType : third.sourceType = closureType
  fourthType : fourth.sourceType = closureType
  firstHandle : first.handle = sequence.first.left
  secondHandle : second.handle = sequence.first.right
  thirdHandle : third.handle = sequence.second.left
  fourthHandle : fourth.handle = sequence.second.right
  firstHandleType : sequence.first.left.sourceType = closureType
  secondHandleType : sequence.first.right.sourceType = closureType
  thirdHandleType : sequence.second.left.sourceType = closureType
  fourthHandleType : sequence.second.right.sourceType = closureType
  firstDistinct : first.handle ≠ second.handle
  secondDistinct : third.handle ≠ fourth.handle
  distinct : first.handle ≠ third.handle
  initial : RetainedState support sequence.first.completion.session [first, second]
  firstReadState : RetainedState support sequence.firstRead.completion.session [first, second]
  secondState : RetainedState support sequence.second.completion.session [first, second, third, fourth]
  secondReadState : RetainedState support sequence.secondRead.completion.session [first, second, third, fourth]
  thirdReadState : RetainedState support sequence.thirdRead.completion.session [first, second, third, fourth]
  finalState : RetainedState support sequence.repeatedRead.completion.session [first, second, third, fourth]
  firstTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    ⟨[]⟩ [.word seed] (.value (.product first.source second.source)) initial.heap
  firstArguments : List Dynamic.Value
  firstPacking : Dynamic.ValuesPack firstArguments .unit
  firstReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    initial.heap first.source firstArguments (.value (.word seed)) firstReadState.heap
  secondTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    firstReadState.heap [.word secondSeed] (.value (.product third.source fourth.source)) secondState.heap
  secondArguments : List Dynamic.Value
  secondPacking : Dynamic.ValuesPack secondArguments .unit
  secondReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondState.heap second.source secondArguments (.value (.word seed)) secondReadState.heap
  thirdArguments : List Dynamic.Value
  thirdPacking : Dynamic.ValuesPack thirdArguments .unit
  thirdReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondReadState.heap third.source thirdArguments (.value (.word secondSeed)) thirdReadState.heap
  repeatedArguments : List Dynamic.Value
  repeatedPacking : Dynamic.ValuesPack repeatedArguments .unit
  repeatedReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    thirdReadState.heap first.source repeatedArguments (.value (.word seed)) finalState.heap

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
  obtain ⟨first, second, firstType, secondType, firstHandle, secondHandle, initial, firstTrace⟩ :=
    first_meaning support makeStages sequence.first
  have unitInput : ∀ entries, RecursiveNamedPublicFunctionHistoryInputs.Input
      entries support.makeHeader.header.function.context .unit .unit .unit := fun _ =>
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  obtain ⟨firstArguments, firstReadState, firstPacking, firstReadTrace⟩ := invoke_word initial first
    (by simp) firstType firstHandle sequence.firstLeftType (unitInput _) sequence.firstRead sequence.firstValue scope
  obtain ⟨third, fourth, thirdType, fourthType, thirdHandle, fourthHandle, secondState, secondTrace⟩ :=
    firstReadState.make_pair sequence.second scope
  obtain ⟨secondArguments, secondReadState, secondPacking, secondReadTrace⟩ := invoke_word secondState second
    (by simp) secondType secondHandle sequence.firstRightType (unitInput _) sequence.secondRead sequence.secondValue scope
  obtain ⟨thirdArguments, thirdReadState, thirdPacking, thirdReadTrace⟩ := invoke_word secondReadState third
    (by simp) thirdType thirdHandle sequence.second.leftType (unitInput _) sequence.thirdRead sequence.thirdValue scope
  obtain ⟨repeatedArguments, finalState, repeatedPacking, repeatedReadTrace⟩ := invoke_word thirdReadState first
    (by simp) firstType firstHandle sequence.firstLeftType (unitInput _) sequence.repeatedRead sequence.repeatedValue scope
  exact ⟨{
    support, first, second, third, fourth, firstType, secondType, thirdType, fourthType,
    firstHandle, secondHandle, thirdHandle, fourthHandle,
    firstHandleType := sequence.firstLeftType
    secondHandleType := sequence.firstRightType
    thirdHandleType := sequence.second.leftType
    fourthHandleType := sequence.second.rightType
    firstDistinct := by rw [firstHandle, secondHandle]; exact sequence.firstDistinct
    secondDistinct := by rw [thirdHandle, fourthHandle]; exact sequence.secondDistinct
    distinct := by rw [firstHandle, thirdHandle]; exact sequence.distinct
    initial, firstReadState, secondState, secondReadState, thirdReadState, finalState,
    firstTrace, firstArguments, firstPacking, firstReadTrace, secondTrace,
    secondArguments, secondPacking, secondReadTrace, thirdArguments, thirdPacking, thirdReadTrace,
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

end Tests.SourceCoreRecursiveFormation
