import Solcore.Test.SourceCoreNestedFormationSeed
import Solcore.Test.SourceCoreNestedFormationMakeStep
import Solcore.Test.SourceCoreNestedFormationInvocation

/-! Seven actual public calls retain both generations of captured closures. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : PublicSupports receiver
  first : Entry
  firstInner : Entry
  second : Entry
  secondInner : Entry
  firstType : first.sourceType = outerType
  firstHandle : first.handle = sequence.first.handle
  firstHandleType : sequence.first.handle.sourceType = outerType
  firstInnerType : firstInner.sourceType = closureType
  firstInnerHandle : firstInner.handle = sequence.firstFormation.handle
  firstInnerHandleType : sequence.firstFormation.handle.sourceType = closureType
  secondType : second.sourceType = outerType
  secondHandle : second.handle = sequence.second.handle
  secondHandleType : sequence.second.handle.sourceType = outerType
  secondInnerType : secondInner.sourceType = closureType
  secondInnerHandle : secondInner.handle = sequence.secondFormation.handle
  secondInnerHandleType : sequence.secondFormation.handle.sourceType = closureType
  distinctOuter : first.handle ≠ second.handle
  distinctInner : firstInner.handle ≠ secondInner.handle
  initial : RetainedState support sequence.first.completion.session [first]
  firstFormationState : RetainedState support sequence.firstFormation.completion.session [first, firstInner]
  secondState : RetainedState support sequence.second.completion.session [first, firstInner, second]
  secondFormationState : RetainedState support sequence.secondFormation.completion.session [first, firstInner, second, secondInner]
  firstReadState : RetainedState support sequence.firstRead.completion.session [first, firstInner, second, secondInner]
  secondReadState : RetainedState support sequence.secondRead.completion.session [first, firstInner, second, secondInner]
  finalState : RetainedState support sequence.repeatedRead.completion.session [first, firstInner, second, secondInner]
  firstTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    ⟨[]⟩ [.word seed] (.value first.source) initial.heap
  secondTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    firstFormationState.heap [.word secondSeed] (.value second.source) secondState.heap
  firstFormationArguments : List Dynamic.Value
  firstFormationPacking : Dynamic.ValuesPack firstFormationArguments .unit
  firstFormationTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    initial.heap first.source firstFormationArguments (.value firstInner.source) firstFormationState.heap
  secondFormationArguments : List Dynamic.Value
  secondFormationPacking : Dynamic.ValuesPack secondFormationArguments .unit
  secondFormationTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondState.heap second.source secondFormationArguments (.value secondInner.source) secondFormationState.heap
  firstReadArguments : List Dynamic.Value
  firstReadPacking : Dynamic.ValuesPack firstReadArguments .unit
  firstReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondFormationState.heap firstInner.source firstReadArguments (.value (.word seed)) firstReadState.heap
  secondReadArguments : List Dynamic.Value
  secondReadPacking : Dynamic.ValuesPack secondReadArguments .unit
  secondReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    firstReadState.heap secondInner.source secondReadArguments (.value (.word secondSeed)) secondReadState.heap
  repeatedReadArguments : List Dynamic.Value
  repeatedReadPacking : Dynamic.ValuesPack repeatedReadArguments .unit
  repeatedReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondReadState.heap firstInner.source repeatedReadArguments (.value (.word seed)) finalState.heap

/-- Exact exported raw types separate outer from inner handles; genuine
issuance observations distinguish the two captures within each generation. -/
theorem SequenceWitness.handles_distinct {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) :
    [meaning.first.handle, meaning.firstInner.handle, meaning.second.handle, meaning.secondInner.handle].Nodup := by
  have different : ∀ (outer inner : SourceCorePublicValues.Handle),
      outer.sourceType = outerType → inner.sourceType = closureType → outer ≠ inner := by
    intro outer inner outerRaw innerRaw same
    have types := congrArg SourceCorePublicValues.Handle.sourceType same
    rw [outerRaw, innerRaw] at types
    cases types
  have firstRaw : meaning.first.handle.sourceType = outerType := by
    rw [meaning.firstHandle]; exact meaning.firstHandleType
  have secondRaw : meaning.second.handle.sourceType = outerType := by
    rw [meaning.secondHandle]; exact meaning.secondHandleType
  have firstInnerRaw : meaning.firstInner.handle.sourceType = closureType := by
    rw [meaning.firstInnerHandle]; exact meaning.firstInnerHandleType
  have secondInnerRaw : meaning.secondInner.handle.sourceType = closureType := by
    rw [meaning.secondInnerHandle]; exact meaning.secondInnerHandleType
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true]
  exact ⟨⟨different _ _ firstRaw firstInnerRaw, meaning.distinctOuter,
      different _ _ firstRaw secondInnerRaw⟩,
    ⟨Ne.symm (different _ _ secondRaw firstInnerRaw), meaning.distinctInner⟩,
    different _ _ secondRaw secondInnerRaw⟩

theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness makeStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports (completion := receiver.completion)
    fixture observed extra identityStages makeStages receiver.completion.result.context.registry receiver.issued
  let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
  obtain ⟨first, firstType, firstHandle, firstHandleType, initial, firstTrace⟩ :=
    first_meaning_typed_handle support makeStages sequence.first
  obtain ⟨firstInner, firstInnerType, firstInnerHandle, firstInnerHandleType,
      firstFormationArguments, firstFormationState, firstFormationPacking, firstFormationTrace⟩ :=
    invoke_formation initial first (by simp) firstType firstHandle firstHandleType sequence.firstFormation scope
  obtain ⟨second, secondType, secondHandle, secondHandleType, secondState, secondTrace⟩ :=
    firstFormationState.make_typed_handle sequence.second scope
  obtain ⟨secondInner, secondInnerType, secondInnerHandle, secondInnerHandleType,
      secondFormationArguments, secondFormationState, secondFormationPacking, secondFormationTrace⟩ :=
    invoke_formation secondState second (by simp) secondType secondHandle secondHandleType sequence.secondFormation scope
  have unitInput : ∀ entries, RecursiveNamedPublicFunctionHistoryInputs.Input
      entries support.makeHeader.header.function.context .unit .unit .unit := fun _ =>
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  obtain ⟨firstReadArguments, firstReadState, firstReadPacking, firstReadTrace⟩ :=
    invoke_word secondFormationState firstInner (by simp) firstInnerType firstInnerHandle firstInnerHandleType
      (unitInput _) sequence.firstRead sequence.firstValue scope
  obtain ⟨secondReadArguments, secondReadState, secondReadPacking, secondReadTrace⟩ :=
    invoke_word firstReadState secondInner (by simp) secondInnerType secondInnerHandle secondInnerHandleType
      (unitInput _) sequence.secondRead sequence.secondValue scope
  obtain ⟨repeatedReadArguments, finalState, repeatedReadPacking, repeatedReadTrace⟩ :=
    invoke_word secondReadState firstInner (by simp) firstInnerType firstInnerHandle firstInnerHandleType
      (unitInput _) sequence.repeatedRead sequence.repeatedValue scope
  exact ⟨{
    support, first, firstInner, second, secondInner,
    firstType, firstHandle, firstHandleType, firstInnerType, firstInnerHandle, firstInnerHandleType,
    secondType, secondHandle, secondHandleType, secondInnerType, secondInnerHandle, secondInnerHandleType,
    distinctOuter := by rw [firstHandle, secondHandle]; exact sequence.distinctOuter
    distinctInner := by rw [firstInnerHandle, secondInnerHandle]; exact sequence.distinctInner
    initial, firstFormationState, secondState, secondFormationState, firstReadState, secondReadState, finalState,
    firstTrace, secondTrace, firstFormationArguments, firstFormationPacking, firstFormationTrace,
    secondFormationArguments, secondFormationPacking, secondFormationTrace,
    firstReadArguments, firstReadPacking, firstReadTrace, secondReadArguments, secondReadPacking, secondReadTrace,
    repeatedReadArguments, repeatedReadPacking, repeatedReadTrace }⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed, Nonempty (SequenceWitness makeStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning fixture observed extra identityStages makeStages sequence receiver⟩

end Tests.SourceCoreNestedFormation
