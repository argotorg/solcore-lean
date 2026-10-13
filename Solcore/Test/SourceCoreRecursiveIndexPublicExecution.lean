import Solcore.Test.SourceCoreRecursiveIndexSeed
import Solcore.Test.SourceCoreRecursiveIndexMakeStep
import Solcore.Test.SourceCoreRecursiveIndexSelectStep
import Solcore.Test.SourceCoreRecursiveIndexInvocation
import Solcore.Test.SourceCoreRecursiveIndexFailureStep

/-! The same checked index expression selects two distinct retained closures,
fails for a third key, and leaves a session in which the first closure still runs. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : PublicSupports receiver
  first : Entry
  second : Entry
  firstSelected : Entry
  intervening : Entry
  secondSelected : Entry
  firstType : first.sourceType = closureType
  secondType : second.sourceType = closureType
  firstSelectedType : firstSelected.sourceType = closureType
  interveningType : intervening.sourceType = closureType
  secondSelectedType : secondSelected.sourceType = closureType
  firstHandle : first.handle = sequence.first.handle
  secondHandle : second.handle = sequence.second.handle
  firstSelectedHandle : firstSelected.handle = sequence.firstSelect.handle
  interveningHandle : intervening.handle = sequence.intervening.handle
  secondSelectedHandle : secondSelected.handle = sequence.secondSelect.handle
  firstHandleType : sequence.first.handle.sourceType = closureType
  firstSelectedHandleType : sequence.firstSelect.handle.sourceType = closureType
  secondSelectedHandleType : sequence.secondSelect.handle.sourceType = closureType
  distinct : first.handle ≠ second.handle
  initial : RetainedState support sequence.first.completion.session [first]
  secondState : RetainedState support sequence.second.completion.session [first, second]
  firstSelectState : RetainedState support sequence.firstSelect.completion.session [first, second, firstSelected]
  firstReadState : RetainedState support sequence.firstRead.completion.session [first, second, firstSelected]
  interveningState : RetainedState support sequence.intervening.completion.session [first, second, firstSelected, intervening]
  secondSelectState : RetainedState support sequence.secondSelect.completion.session [first, second, firstSelected, intervening, secondSelected]
  secondReadState : RetainedState support sequence.secondRead.completion.session [first, second, firstSelected, intervening, secondSelected]
  failedState : RetainedState support sequence.failed.returned [first, second, firstSelected, intervening, secondSelected]
  finalState : RetainedState support sequence.repeatedRead.completion.session [first, second, firstSelected, intervening, secondSelected]
  firstTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    ⟨[]⟩ [.word seed] (.value first.source) initial.heap
  secondTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    initial.heap [.word secondSeed] (.value second.source) secondState.heap
  firstSelectTrace : SourceCall support support.selectHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondState.heap [sourceTable first second, .word firstKey] (.value firstSelected.source) firstSelectState.heap
  firstArguments : List Dynamic.Value
  firstPacking : Dynamic.ValuesPack firstArguments .unit
  firstReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    firstSelectState.heap firstSelected.source firstArguments (.value (.word seed)) firstReadState.heap
  interveningTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    firstReadState.heap [.word interveningSeed] (.value intervening.source) interveningState.heap
  secondSelectTrace : SourceCall support support.selectHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    interveningState.heap [sourceTable first second, .word secondKey] (.value secondSelected.source) secondSelectState.heap
  secondArguments : List Dynamic.Value
  secondPacking : Dynamic.ValuesPack secondArguments .unit
  secondReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondSelectState.heap secondSelected.source secondArguments (.value (.word secondSeed)) secondReadState.heap
  failure : Staging.Recursive.Failure
  failedTrace : SourceCall support support.selectHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondReadState.heap [sourceTable first second, .word missingKey] (.fault failure) failedState.heap
  failedMeaning : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
    failedState.receiving.result.diagnostics failure sequence.failed.reason
  repeatedArguments : List Dynamic.Value
  repeatedPacking : Dynamic.ValuesPack repeatedArguments .unit
  repeatedReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    failedState.heap first.source repeatedArguments (.value (.word seed)) finalState.heap

theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (admission : ObservedProgramCertificate fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (echoStages : ObservedStages fixture observed.echoRow)
    (chooseStages : ObservedStages fixture observed.chooseRow)
    (selectStages : ObservedStages fixture observed.selectRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness makeStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports
    fixture observed admission makeStages echoStages chooseStages selectStages receiver
  let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
  obtain ⟨first, firstType, firstHandle, firstHandleType, initial, firstTrace⟩ :=
    first_meaning_typed_handle support makeStages sequence.first
  obtain ⟨second, secondType, secondHandle, _secondHandleType, secondState, secondTrace⟩ :=
    initial.make_typed_handle sequence.second scope
  obtain ⟨firstSelected, firstSelectedType, firstSelectedHandle, firstSelectedHandleType, firstSelectState, firstSelectTrace⟩ :=
    secondState.select_typed_handle first second (by simp) (by simp) firstType secondType
      firstHandle secondHandle sequence.firstSelect scope
  have unitInput : ∀ entries, RecursiveNamedPublicFunctionHistoryInputs.Input
      entries support.makeHeader.header.function.context .unit .unit .unit := fun _ =>
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  obtain ⟨firstArguments, firstReadState, firstPacking, firstReadTrace⟩ := invoke_word firstSelectState firstSelected
    (by simp) firstSelectedType firstSelectedHandle firstSelectedHandleType (unitInput _) sequence.firstRead sequence.firstValue scope
  obtain ⟨intervening, interveningType, interveningHandle, _interveningHandleType, interveningState, interveningTrace⟩ :=
    firstReadState.make_typed_handle sequence.intervening scope
  obtain ⟨secondSelected, secondSelectedType, secondSelectedHandle, secondSelectedHandleType, secondSelectState, secondSelectTrace⟩ :=
    interveningState.select_typed_handle first second (by simp) (by simp) firstType secondType
      firstHandle secondHandle sequence.secondSelect scope
  obtain ⟨secondArguments, secondReadState, secondPacking, secondReadTrace⟩ := invoke_word secondSelectState secondSelected
    (by simp) secondSelectedType secondSelectedHandle secondSelectedHandleType (unitInput _) sequence.secondRead sequence.secondValue scope
  obtain ⟨failedState, failure, failedTrace, failedMeaning⟩ :=
    secondReadState.select_failure first second (by simp) (by simp) firstType secondType
      firstHandle secondHandle sequence.failed scope
  obtain ⟨repeatedArguments, finalState, repeatedPacking, repeatedReadTrace⟩ := invoke_word failedState first
    (by simp) firstType firstHandle firstHandleType (unitInput _) sequence.repeatedRead sequence.repeatedValue scope
  exact ⟨{
    support, first, second, firstSelected, intervening, secondSelected,
    firstType, secondType, firstSelectedType, interveningType, secondSelectedType,
    firstHandle, secondHandle, firstSelectedHandle, interveningHandle, secondSelectedHandle,
    firstHandleType, firstSelectedHandleType, secondSelectedHandleType,
    distinct := by rw [firstHandle, secondHandle]; exact sequence.distinct
    initial, secondState, firstSelectState, firstReadState, interveningState, secondSelectState,
    secondReadState, failedState, finalState,
    firstTrace, secondTrace, firstSelectTrace, firstArguments, firstPacking, firstReadTrace,
    interveningTrace, secondSelectTrace, secondArguments, secondPacking, secondReadTrace,
    failure, failedTrace, failedMeaning, repeatedArguments, repeatedPacking, repeatedReadTrace }⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (admission : ObservedProgramCertificate fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (echoStages : ObservedStages fixture observed.echoRow)
    (chooseStages : ObservedStages fixture observed.chooseRow)
    (selectStages : ObservedStages fixture observed.selectRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed, Nonempty (SequenceWitness makeStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning fixture observed admission makeStages echoStages chooseStages selectStages sequence receiver⟩

end Tests.SourceCoreRecursiveIndex
